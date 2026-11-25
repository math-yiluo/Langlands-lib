/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicSliceScalarComparisonData

/-! # Scalar extension on a pro-etale slice

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Exact slice restriction commutes with unbounded derived scalar extension.
This is a comparison of the two functors, for an arbitrary coefficient map; it
contains no adic quotient, constant model, or local-isomorphism hypothesis.

Source: Stacks Project, sites-cohomology.tex, lemma-derived-base-change (06YY),
lemma-pullback-K-flat (0G7E), and lemma-derived-pullback-composition (0D6D).
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).

Proof: choose a flat-term K-flat resolution of the input. Restriction to the slice
is the inverse image of the localization morphism of topoi and is exact. It carries
this resolution to a flat-term K-flat resolution, by pullback-K-flat. Ordinary scalar
extension commutes with slice restriction: on an object V -> U the two presheaf
tensors are the same tensor over R(V), and module sheafification commutes with
localization of the site. Consequently these identifications commute with all
restriction maps and differentials. The universal derived counits identify the two
localized complexes with the displayed composite functors. The representative
comparison is natural on K-flat complexes; localization of their homotopy category
extends it uniquely to a natural isomorphism on the entire derived category.
This also applies when U is empty or one of the coefficient rings is zero. -/
theorem completedAdic_slice_scalarComparison (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    Nonempty
      (ringedDerivedRestrictionGeneral
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U ⋙
          completedAdicSliceDerivedChange X U f ≅
        completedAdicDerivedChange X f ⋙
          ringedDerivedRestrictionGeneral
            ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) U) := by
  let O_R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let O_S := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
  let A := SheafOfModules O_R
  letI : (SheafOfModules.overFunctor O_R U).Additive := by
    exact (ringedOverFunctor_exactGeneral O_R U).1
  letI : (SheafOfModules.overFunctor O_S U).Additive := by
    exact (ringedOverFunctor_exactGeneral O_S U).1
  letI : (completedAdicChange X f).Additive := completedAdicChange_additive X f
  letI : (completedAdicSliceChange X U f).Additive :=
    completedAdicSliceChange_additive X U f
  letI : HasDerivedCategory A := HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules O_S) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules (O_R.over U)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules (O_S.over U)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory
      (SheafOfModules.{t + 1}
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
          ((ProEt.topology X).over U)
          (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).obj S))) :=
    HasDerivedCategory.standard _
  let Q_A := DerivedCategory.Qh (C := A)
  let F := completedAdicDerivedChange X f
  let F_U := completedAdicSliceDerivedChange X U f
  let L_U := ringedDerivedRestrictionGeneral O_R U ⋙ F_U
  let L := F ⋙ ringedDerivedRestrictionGeneral O_S U
  let G_U :=
    ((SheafOfModules.overFunctor O_R U ⋙ completedAdicSliceChange X U f).mapHomotopyCategory
      (.up ℤ)) ⋙ DerivedCategory.Qh
  let G :=
    ((completedAdicChange X f ⋙ SheafOfModules.overFunctor O_S U).mapHomotopyCategory
      (.up ℤ)) ⋙ DerivedCategory.Qh
  obtain ⟨e₀⟩ := completedAdic_slice_scalarComparison_underived X U f
  let e : G_U ≅ G := Functor.isoWhiskerRight
    { hom := NatTrans.mapHomotopyCategory e₀.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory e₀.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] } DerivedCategory.Qh
  obtain ⟨α, α', hα, hα'⟩ := completedAdic_slice_scalarComparison_derived_data X U f
  letI := hα
  letI := hα'
  exact ⟨Functor.leftDerivedNatIso L_U L α α'
    (HomotopyCategory.quasiIso A (.up ℤ)) e⟩

end AlgebraicGeometry.Scheme
