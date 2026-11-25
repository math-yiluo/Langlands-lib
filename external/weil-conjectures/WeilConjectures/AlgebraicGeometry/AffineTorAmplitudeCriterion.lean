/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TorAmplitudeFlatModel
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison

/-! # Tor amplitude under the affine associated-sheaf correspondence

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.10.4, Tag 08E9,
part (1) (blueprint: lem-pc-affine-tor-amplitude-criterion).
-/

@[expose] public section

universe u wA wX

open CategoryTheory

namespace AlgebraicGeometry


open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 256 in
private theorem isZero_derivedTensor_homology_of_vanish (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ)
    (h : schemeDerivedTensorCohomologyVanishes X E F i) :
    CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (E ⊗ DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨P, hP, ⟨e⟩, hz⟩ := h
  let N := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F
  let cP := (Functor.const (Discrete PUnit.{1})).obj P
  let cN := (Functor.const (Discrete PUnit.{1})).obj N
  obtain ⟨β⟩ := kFlat_derivedTensor_comparison_natIso X cP cN (fun _ ↦ hP)
  let β' : DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N (MonoidalCategory.curriedTensor _)) :=
    (β.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  exact hz.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      (MonoidalCategory.whiskerRightIso e.symm (DerivedCategory.Q.obj N) ≪≫ β') ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 256 in
/-- A module complex and its corresponding quasi-coherent derived object on `Spec A`
have the same Tor amplitude in `[a,b]`. The corresponding object is the image under `Q` of
the termwise tilde complex of `M`, as in `exists_affineQCohDerivedEquivalence`.
Source: Stacks Project, Tag 08E9, part (1)
(blueprint: lem-pc-affine-tor-amplitude-criterion).

Proof:
1. Choose a flat module model P in [a,b] using
   lem-pc-module-tor-amplitude-flat-model. Bounded flat complexes are K-flat
   (lem-pc-module-bounded-flat-kflat), and tilde preserves K-flatness
   (lem-pc-affine-tilde-kflat). The affine equivalence transports its representing
   isomorphism to sheaves. Tensor with a sheaf in degree zero is termwise tensor,
   so zero terms outside [a,b] give zero homology and the required K-flat witness.
2. Conversely, test against tilde N for every module N. Unpack the K-flat witness
   of vanishing and apply lem-pc-kflat-derived-tensor-comparison. Choose a module
   K-flat resolution P to M using the proved source resolution theorem
   (lem-pc-source-module-kflat-resolution). The module K-flat tensor computation
   (lem-pc-source-kflat-module-tensor-model) and the affine derived tensor comparison
   identify the sheaf tensor with tilde of the module total tensor.
3. The existing affine derived cohomology comparison
   (new-affine-derived-tilde-homology-comparison) identifies its cohomology with tilde
   of the module cohomology. Full faithfulness of tilde, from
   lem-weil-pbc-affine-tilde-gamma-adjunction, detects zero identity morphisms and hence
   zero modules. The canonical t-structure characterizations of IsGE and IsLE convert
   this vanishing to the asserted module Tor amplitude. -/
theorem affine_torAmplitude_iff (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) (hab : a ≤ b) :
    (∀ G : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes (Spec (.of A))
          (DerivedCategory.Q.obj
            ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
              (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _ _
              (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M))
          G i) ↔
      DerivedCategory.torAmplitudeIn (ModuleCat.{u} A) a b (DerivedCategory.Q.obj M) := by
  let T := @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _ _
    (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)
  constructor
  · intro h
    let := schemeDerivedTensorMonoidal (Spec (.of A))
    let L : ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) :=
      tilde.functor (.of A)
    let : L.Faithful := (tilde.fullyFaithfulFunctor (R := .of A)).faithful
    let : L.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    obtain ⟨eqv, ⟨α⟩, _⟩ := exists_affineQCohDerivedEquivalence.{u, wA, wX} A
    obtain ⟨P, s, hs, _, hk⟩ := CochainComplex.exists_quasiIso_flat_kFlat M
    have : QuasiIso s := hs
    have : IsIso (DerivedCategory.Q.map s) := inferInstance
    intro N
    have hN (i : ℤ) (hi : i < a ∨ b < i) :
        CategoryTheory.Limits.IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (MonoidalCategory.tensorObj (DerivedCategory.Q.obj M)
            ((DerivedCategory.singleFunctor _ 0).obj N))) := by
      let N₀ := (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj N
      let K := CochainComplex.mapBifunctor P N₀ (MonoidalCategory.curriedTensor (ModuleCat.{u} A))
      let eM : MonoidalCategory.tensorObj (DerivedCategory.Q.obj M)
          ((DerivedCategory.singleFunctor _ 0).obj N) ≅
          DerivedCategory.Q.obj K :=
        MonoidalCategory.whiskerRightIso (asIso (DerivedCategory.Q.map s)).symm _ ≪≫
          MonoidalCategory.whiskerLeftIso (DerivedCategory.Q.obj P)
            ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N) ≪≫
          DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P N₀ hk
      have hz := isZero_derivedTensor_homology_of_vanish.{u, wX} (Spec (.of A)) _ (L.obj N) i
        (h (L.obj N) i hi)
      let eN := DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app N)
      obtain ⟨β⟩ := derivedTensor_tilde_iso.{u, wX} A M N₀ P s hs hk
      have hz' := hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
        (MonoidalCategory.whiskerLeftIso (DerivedCategory.Q.obj (T.obj M)) eN))
      have hβ := hz'.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso β.symm)
      obtain ⟨γ⟩ := affineDerivedTilde_homology_comparison.{u, wA, wX} A eqv.functor ⟨α⟩ i
      let eH : (DerivedCategory.homologyFunctor _ i).obj
          (DerivedCategory.Q.obj (T.obj K)) ≅
          L.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            (DerivedCategory.Q.obj K)) :=
        (DerivedCategory.homologyFunctor _ i).mapIso (α.app K).symm ≪≫
          γ.app (DerivedCategory.Q.obj K)
      have htilde := hβ.of_iso eH.symm
      have hK : CategoryTheory.Limits.IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            (DerivedCategory.Q.obj K)) := by
        apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2
        apply L.map_injective
        rw [L.map_id, L.map_zero]
        exact htilde.eq_of_src _ _
      exact hK.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eM)
    exact ⟨(DerivedCategory.isGE_iff _ a).2 (fun i hi ↦ hN i (Or.inl hi)),
      (DerivedCategory.isLE_iff _ b).2 (fun i hi ↦ hN i (Or.inr hi))⟩
  · intro h
    obtain ⟨P, hflat, hzero, ⟨e⟩⟩ :=
      (DerivedCategory.module_torAmplitudeIn_iff_exists_flat_model M a b hab).mp h
    obtain ⟨eqv, ⟨α⟩, _⟩ := exists_affineQCohDerivedEquivalence.{u, wA, wX} A
    let e' : DerivedCategory.Q.obj (T.obj P) ≅ DerivedCategory.Q.obj (T.obj M) :=
      (α.app P).symm ≪≫
        (eqv.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).mapIso e.symm ≪≫
        α.app M
    have hk := isKFlat_tilde A P
      (CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat P
        ⟨b, fun i hi ↦ hzero i (Or.inr hi)⟩ hflat)
    intro G i hi
    change schemeDerivedTensorCohomologyVanishes (Spec (.of A))
      (DerivedCategory.Q.obj (T.obj M)) G i
    let := SheafOfModules.monoidalCategory (Spec (.of A)).sheaf
    change ∃ R : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := (Spec (.of A)).sheaf) R ∧
        Nonempty (DerivedCategory.Q.obj R ≅ DerivedCategory.Q.obj (T.obj M)) ∧ _
    refine ⟨T.obj P, hk, ⟨e'⟩, ?_⟩
    let β := CochainComplex.mapBifunctorSingle₂Iso
      (MonoidalCategory.curriedTensor _) G (T.obj P)
    apply CategoryTheory.Limits.IsZero.of_iso _
      ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso β)
    apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    change CategoryTheory.Limits.IsZero
      ((MonoidalCategory.tensorRight G).obj ((tilde.functor (.of A)).obj (P.X i)))
    let : (tilde.functor (.of A)).PreservesZeroMorphisms :=
      ⟨fun _ _ ↦ tilde.map_zero⟩
    let : (MonoidalCategory.tensorRight G).PreservesZeroMorphisms := ⟨fun X Y ↦
      congrArg (fun t ↦ t.app G) ((MonoidalCategory.curriedTensor _).map_zero X Y)⟩
    exact (MonoidalCategory.tensorRight G).map_isZero
      ((tilde.functor (.of A)).map_isZero (hzero i hi))

end AlgebraicGeometry
