/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import WeilConjectures.AlgebraicGeometry.AffineModuleComplexRepresentative
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.AffineDerivedTensorChartComparison
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Affine-local cohomology of derived tensor

Source: Stacks Project, Tag 08DX, part (1), with its affine calculation in part (2).
(blueprint: lem-pc-derived-tensor-qcoh-component).
-/

@[expose] public section

universe uX wD

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

noncomputable local instance DerivedTensorPreservesQCoh_monoidalCategory (X : Scheme.{uX}) :
    MonoidalCategory (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The independent localizations and their tensor instances require extra elaboration steps.
set_option synthInstance.maxSize 2048 in
/-- Affine-local cohomology calculation for a K-flat tensor representative.
Source: Stacks Project, Tag 08DX(1), proof using Tag 08DX(2) and Tag 06Z0.
Proof: exact restriction commutes with cohomology and with the total tensor of complexes,
and preserves K-flatness. On the affine U, represent the restrictions of Q(P) and Q(N)
by tilde of module complexes using 06Z0. Resolve the first module complex by a K-flat
complex. The affine tensor comparison identifies the restricted tensor representative
with tilde of the total tensor of this resolution and the second module complex.
Tilde is exact, so every cohomology sheaf is tilde of a module and is quasi-coherent.
Transfer through the derived comparison and the equivalence with the over category.
This works in all degrees, including unbounded complexes and the empty open.
(blueprint: lem-pc-derived-tensor-qcoh-component). -/
theorem derivedTensor_cohomology_over_affine {X : Scheme.{uX}}
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (hPQ : schemeDerivedQCohProperty X (DerivedCategory.Q.obj P))
    (hNQ : schemeDerivedQCohProperty X (DerivedCategory.Q.obj N))
    (n : ℤ) (U : X.Opens) (hU : IsAffineOpen U) :
    (((DerivedCategory.homologyFunctor
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj
        (DerivedCategory.Q.obj
          (CochainComplex.mapBifunctor P N (curriedTensor _)))).over U).IsQuasicoherent := by
  classical
  let : HasDerivedCategory (SheafOfModules.{uX}
      (moduleRings U.toScheme.toRingedSpace)) := HasDerivedCategory.standard _
  let S := U.toScheme
  have : IsAffine S := hU
  let : HasDerivedCategory (SheafOfModules.{uX}
      (moduleRings (Spec Γ(S, ⊤)).toRingedSpace)) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{uX} Γ(S, ⊤)) := HasDerivedCategory.standard _
  -- Cache the site instances before repeatedly forming quasi-coherence predicates.
  let : Abelian (SheafOfModules.{uX} (moduleRings S.toRingedSpace)) := inferInstance
  let : Abelian (SheafOfModules.{uX}
      (moduleRings (Spec Γ(S, ⊤)).toRingedSpace)) := inferInstance
  have : ∀ W : S.Opens,
      HasWeakSheafify ((Opens.grothendieckTopology S).over W)
        AddCommGrpCat.{uX} := inferInstance
  have : ∀ W : S.Opens,
      ((Opens.grothendieckTopology S).over W).WEqualsLocallyBijective
        AddCommGrpCat.{uX} := inferInstance
  have : ∀ W : (Spec Γ(S, ⊤)).Opens,
      HasWeakSheafify
        ((Opens.grothendieckTopology (Spec Γ(S, ⊤))).over W)
        AddCommGrpCat.{uX} := inferInstance
  have : ∀ W : (Spec Γ(S, ⊤)).Opens,
      ((Opens.grothendieckTopology (Spec Γ(S, ⊤))).over W).WEqualsLocallyBijective
        AddCommGrpCat.{uX} := inferInstance
  let O := SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{uX} (moduleRings S.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  let : Limits.PreservesFiniteLimits O := Limits.comp_preservesFiniteLimits _ _
  let : Limits.PreservesFiniteColimits O := Limits.comp_preservesFiniteColimits _ _
  let : O.Additive := Functor.additive_of_preserves_binary_products O
  let E := O.mapDerivedCategory.obj (DerivedCategory.Q.obj P)
  let F := O.mapDerivedCategory.obj (DerivedCategory.Q.obj N)
  have hE : schemeDerivedQCohProperty S E :=
    (schemeDerivedQCoh_openRestriction_iff X U (DerivedCategory.Q.obj P)).2 (fun i ↦ by
      have := hPQ i
      exact SheafOfModules.isQuasicoherent_over
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) i).obj
            (DerivedCategory.Q.obj P)) U)
  have hF : schemeDerivedQCohProperty S F :=
    (schemeDerivedQCoh_openRestriction_iff X U (DerivedCategory.Q.obj N)).2 (fun i ↦ by
      have := hNQ i
      exact SheafOfModules.isQuasicoherent_over
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) i).obj
            (DerivedCategory.Q.obj N)) U)
  obtain ⟨M, ⟨eM⟩⟩ := exists_affine_module_complex_representative S E hE
  obtain ⟨L, ⟨eL⟩⟩ := exists_affine_module_complex_representative S F hF
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{uX} Γ(S, ⊤) ⥤
      SheafOfModules.{uX} (moduleRings (Spec Γ(S, ⊤)).toRingedSpace))
      (tilde.functor Γ(S, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let R : SheafOfModules.{uX} (moduleRings (Spec Γ(S, ⊤)).toRingedSpace) ⥤
      SheafOfModules.{uX} (moduleRings S.toRingedSpace) :=
    Scheme.Modules.restrictFunctor S.toSpecΓ
  let : R.Additive := by
    exact Functor.additive_of_preserves_binary_products
      (Scheme.Modules.restrictFunctor S.toSpecΓ)
  let : Limits.PreservesFiniteLimits R := by
    change Limits.PreservesFiniteLimits (Scheme.Modules.restrictFunctor S.toSpecΓ)
    infer_instance
  let : Limits.PreservesFiniteColimits R := by
    change Limits.PreservesFiniteColimits (Scheme.Modules.restrictFunctor S.toSpecΓ)
    infer_instance
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{uX} Γ(S, ⊤)))).reduced
  let K := Λ.resolutionFunctor.obj M
  let s : K ⟶ M := (Λ.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le).app M
  have hs : QuasiIso s := by dsimp [s, K]; infer_instance
  have hK : (HomologicalComplex.quasiIso (ModuleCat.{uX} Γ(S, ⊤)) (.up ℤ)).kFlat K :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le M
  obtain ⟨chartIso⟩ := affine_derivedTensor_chart_comparison S M L K s hs hK
  let B := CochainComplex.mapBifunctor K L (curriedTensor (ModuleCat.{uX} Γ(S, ⊤)))
  let model : E ⊗ F ≅ DerivedCategory.Q.obj
      ((R.mapHomologicalComplex (.up ℤ)).obj (T.obj B)) :=
    MonoidalCategory.tensorIso (C := schemeDerivedCategory S) eM eL ≪≫ chartIso
  obtain ⟨a, ⟨tildeIso⟩, _⟩ := exists_affineQCohDerivedEquivalence_core Γ(S, ⊤)
  have hT (i : ℤ) :=
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec Γ(S, ⊤)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (tildeIso.app B))
      ((a.functor.obj (DerivedCategory.Q.obj B)).property i)
  have hAffine (i : ℤ) :
      ((DerivedCategory.homologyFunctor _ i).obj (E ⊗ F)).IsQuasicoherent := by
    have : ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uX} (moduleRings (Spec Γ(S, ⊤)).toRingedSpace)) i).obj
          (DerivedCategory.Q.obj (T.obj B))).IsQuasicoherent := hT i
    let c := (DerivedCategory.homologyFunctor _ i).mapIso model ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
      (R.mapHomologicalComplexHomologyIso (.up ℤ) i).app (T.obj B) ≪≫
      R.mapIso ((DerivedCategory.homologyFunctorFactors _ i).symm.app (T.obj B))
    exact (SheafOfModules.isQuasicoherent (moduleRings S.toRingedSpace)).prop_of_iso c.symm
      (@Scheme.Modules.isQuasicoherent_restrictFunctor _ _ S.toSpecΓ inferInstance _ this)
  obtain ⟨restrictionIso⟩ := derivedTensor_openRestriction_iso_universes X U
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
  let CP := (Functor.const PUnit.{1}).obj P
  let CN := (Functor.const PUnit.{1}).obj N
  obtain ⟨comparison⟩ := kFlat_derivedTensor_comparison_natIso X CP CN (fun _ ↦ hP)
  let tensorComparison := (comparison.app PUnit.unit.{1}).app PUnit.unit.{1}
  let c := O.mapDerivedCategory.mapIso tensorComparison.symm ≪≫ restrictionIso
  have hRestricted : schemeDerivedQCohProperty S
      (O.mapDerivedCategory.obj
        (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N (curriedTensor _)))) := by
    intro i
    exact (SheafOfModules.isQuasicoherent (moduleRings S.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso c).symm (hAffine i)
  exact (schemeDerivedQCoh_openRestriction_iff X U _).1 hRestricted n

end AlgebraicGeometry
