/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineModuleComplexRepresentative
import WeilConjectures.AlgebraicGeometry.AffineDerivedTensorChartComparison
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.Algebra.Homology.TorAmplitudeFlatModel
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import all WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison

/-! # Quasi-coherent tests on an affine scheme

Source: Stacks Project, Tag 08EA, affine paragraph, using Tags 06Z0 and 08E9.
(blueprint: lem-pc-affine-qcoh-tor-amplitude-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- On an affine scheme, quasi-coherent test sheaves detect Tor amplitude.
Source: Stacks Project, Tag 08EA, affine paragraph, and Tags 06Z0, 08E9.
(blueprint: lem-pc-affine-qcoh-tor-amplitude-detection).

Proof: Write X as Spec A using its canonical affine spectrum chart. The affine
quasi-coherent derived equivalence represents E by termwise tilde of a module complex M.
Test against tilde N, for every A-module N. The affine tensor comparison and exactness
of tilde identify the tested cohomology with tilde of H^i(M tensor-derived N).
Faithfulness of tilde detects its vanishing, hence M has Tor amplitude [a,b].
The module flat-model criterion gives a flat complex P supported in [a,b] representing M.
Its tilde complex, transported along the canonical chart, is K-flat and represents E.
Tensoring it with any sheaf G in degree zero has zero terms outside [a,b], hence zero
cohomology there. This is a K-flat witness for the conclusion. The argument includes
zero rings, empty affine schemes, unbounded E, and a=b; no arbitrary model is selected
from an unproved mere existence theorem, as only the resulting vanishing is asserted. -/
theorem affineQCoh_torAmplitude_detection (X : Scheme.{u}) [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a b : ℤ) (hab : a ≤ b)
    (h : ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      F.IsQuasicoherent → ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes X E F i) :
    ∀ G : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X E G i := by
  classical
  let A := Γ(X, ⊤)
  let : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
  let L : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) := tilde.functor Γ(X, ⊤)
  let : L.IsLeftAdjoint := (tilde.adjunction (R := Γ(X, ⊤))).isLeftAdjoint
  let : L.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let : L.Faithful := (tilde.fullyFaithfulFunctor (R := Γ(X, ⊤))).faithful
  let : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N), PreservesLimit (parallelPair f 0) L :=
    fun {_ _} f ↦ tilde_preservesKernel A f
  let : PreservesFiniteLimits L := Functor.preservesFiniteLimits_of_preservesKernels L
  let R : SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
    Scheme.Modules.restrictFunctor X.toSpecΓ
  let S := Scheme.Modules.restrictFunctor X.isoSpec.inv
  have eRS : R ⋙ S ≅ 𝟭 _ :=
    (Scheme.Modules.restrictFunctorComp X.isoSpec.inv X.toSpecΓ).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by
        rw [← Scheme.isoSpec_hom]
        exact X.isoSpec.inv_hom_id) ≪≫ Scheme.Modules.restrictFunctorId
  let : R.Faithful := eRS.faithful_of_comp
  let : R.Additive := by
    change (Scheme.Modules.restrictFunctor X.toSpecΓ).Additive
    infer_instance
  let : PreservesFiniteLimits R := by
    change PreservesFiniteLimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
    infer_instance
  let : PreservesFiniteColimits R := by
    change PreservesFiniteColimits (Scheme.Modules.restrictFunctor X.toSpecΓ)
    infer_instance
  let C : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := L ⋙ R
  let T := L.mapHomologicalComplex (.up ℤ)
  let CT := C.mapHomologicalComplex (.up ℤ)
  obtain ⟨M, ⟨eM⟩⟩ := exists_affine_module_complex_representative X E hE
  change E ≅ DerivedCategory.Q.obj (CT.obj M) at eM
  obtain ⟨P, s, hs, _, hk⟩ := CochainComplex.exists_quasiIso_flat_kFlat M
  have : QuasiIso s := hs
  have hAmp : DerivedCategory.torAmplitudeIn (ModuleCat.{u} A) a b
      (DerivedCategory.Q.obj M) := by
    intro N
    have hN (i : ℤ) (hi : i < a ∨ b < i) :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (DerivedCategory.Q.obj M ⊗ (DerivedCategory.singleFunctor _ 0).obj N)) := by
      let N₀ := (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj N
      let K := CochainComplex.mapBifunctor P N₀ (curriedTensor (ModuleCat.{u} A))
      have hF : (C.obj N).IsQuasicoherent := by
        change ((Scheme.Modules.restrictFunctor X.toSpecΓ).obj (tilde N)).IsQuasicoherent
        infer_instance
      have hzSingle := (tensor_vanishes_iff X E (C.obj N) i).1 (h _ hF i hi)
      have hz := hzSingle.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
        (whiskerLeftIso E ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (C.obj N)))).symm
      let eN : (DerivedCategory.singleFunctor _ 0).obj (C.obj N) ≅
          DerivedCategory.Q.obj (CT.obj N₀) :=
        (DerivedCategory.singleFunctorIsoCompQ _ 0).app (C.obj N) ≪≫
        DerivedCategory.Q.mapIso
          ((HomologicalComplex.singleMapHomologicalComplex C (.up ℤ) 0).app N).symm
      obtain ⟨β⟩ := affine_derivedTensor_chart_comparison X M N₀ P s hs hk
      let cmp := tensorIso eM eN ≪≫ β
      have hzK := hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso cmp).symm
      let eH : (DerivedCategory.homologyFunctor _ i).obj
          (DerivedCategory.Q.obj (CT.obj K)) ≅ C.obj (K.homology i) :=
        (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
          (C.mapHomologicalComplexHomologyIso (.up ℤ) i).app K
      have hzC := hzK.of_iso eH.symm
      have hK : IsZero (K.homology i) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply C.map_injective
        rw [C.map_id, C.map_zero]
        exact hzC.eq_of_src _ _
      let eTensor : DerivedCategory.Q.obj M ⊗ (DerivedCategory.singleFunctor _ 0).obj N ≅
          DerivedCategory.Q.obj K :=
        whiskerRightIso (asIso (DerivedCategory.Q.map s)).symm _ ≪≫
          whiskerLeftIso (DerivedCategory.Q.obj P)
            ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N) ≪≫
          DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P N₀ hk
      exact hK.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eTensor ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app K)
    exact ⟨(DerivedCategory.isGE_iff _ a).2 (fun i hi ↦ hN i (Or.inl hi)),
      (DerivedCategory.isLE_iff _ b).2 (fun i hi ↦ hN i (Or.inr hi))⟩
  obtain ⟨B, hflat, hzero, ⟨eB⟩⟩ :=
    (DerivedCategory.module_torAmplitudeIn_iff_exists_flat_model M a b hab).mp hAmp
  let e : DerivedCategory.Q.obj (CT.obj B) ≅ E :=
    (C.mapDerivedCategoryFactors.app B).symm ≪≫
      C.mapDerivedCategory.mapIso eB.symm ≪≫ C.mapDerivedCategoryFactors.app M ≪≫ eM.symm
  have hB := isKFlat_restrict X.toSpecΓ (T.obj B)
    (isKFlat_tilde A B (CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat B
      ⟨b, fun i hi ↦ hzero i (Or.inr hi)⟩ hflat))
  intro G i hi
  let := SheafOfModules.monoidalCategory X.sheaf
  refine ⟨CT.obj B, hB, ⟨e⟩, ?_⟩
  let β := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) G (CT.obj B)
  apply IsZero.of_iso _ ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso β)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  change IsZero ((tensorRight G).obj (C.obj (B.X i)))
  exact (tensorRight G).map_isZero (C.map_isZero (hzero i hi))

end AlgebraicGeometry
