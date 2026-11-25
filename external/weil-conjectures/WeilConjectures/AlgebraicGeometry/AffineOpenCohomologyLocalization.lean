/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineOpenCohomologyLocalizationZero
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Localization of cohomology on an ambient affine open

Source: Stacks Project, Tags 09MR (affine-open paragraph) and 01E1 (locality).
(blueprint: lem-sc-invert-s-cohomology-affine-open).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The affine localization comparison, expressed on an open of the ambient scheme.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, affine-open paragraph;
Cohomology of Sheaves, Lemma 01E1 (2).
(blueprint: lem-sc-invert-s-cohomology-affine-open).

Proof: In degree zero use affineOpen_cohomology_localization_zero. In positive
degrees all twisted numerator groups vanish by affine cohomology vanishing, since
tensor products of quasi-coherent modules are quasi-coherent. Their direct sum and
fraction quotient are therefore subsingletons. The open U ⊓ S is affine by
lem-sc-affine-cap-section-open, so its cohomology also vanishes. The unique additive
equivalence between these zero groups satisfies the fraction formula. For empty U
or zero s the same argument applies. -/
theorem affineOpen_cohomology_localization
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p U ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p U n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ S ≤ U))).app (F ⊗ L.tensorPow n : X.Modules) ξ := by
  intro p
  by_cases hp : p = 0
  · subst p
    exact affineOpen_cohomology_localization_zero X L s F S hS U hU
  · have hpos : 0 < p := Nat.pos_of_ne_zero hp
    obtain ⟨V, hV, hVS⟩ := (affine_cap_section_open X L s U hU).1
    have hVeq : V = U ⊓ S := by
      ext x
      change (x ∈ V) ↔ (x ∈ U ⊓ S)
      rw [hVS x]
      change (x ∈ U ∧ x ∈ nonvanishingLocus L s) ↔ (x ∈ U ∧ x ∈ S)
      rw [← hS]
      rfl
    have hUS : IsAffineOpen (U ⊓ S) := hVeq ▸ hV
    let : ∀ n : ℕ, Subsingleton
        ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          (F ⊗ L.tensorPow n : X.Modules)) := fun n ↦ by
      have : (F ⊗ L.tensorPow n : X.Modules).IsQuasicoherent :=
        isQuasicoherent_tensorObj F (L.tensorPow n)
      exact subsingleton_openModuleCohomology_of_isAffineOpen X _ U hU p hpos
    let : Subsingleton (CohomologyFractionPresentation L F s p U) := by
      constructor
      intro a b
      induction a using QuotientAddGroup.induction_on with
      | H a =>
        induction b using QuotientAddGroup.induction_on with
        | H b =>
          exact congrArg QuotientAddGroup.mk (Subsingleton.elim a b)
    let : Subsingleton
        ((RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj F) :=
      subsingleton_openModuleCohomology_of_isAffineOpen X F (U ⊓ S) hUS p hpos
    let : ∀ n : ℕ, Subsingleton
        ((RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj
          (F ⊗ L.tensorPow n : X.Modules)) := fun n ↦ by
      have : (F ⊗ L.tensorPow n : X.Modules).IsQuasicoherent :=
        isQuasicoherent_tensorObj F (L.tensorPow n)
      exact subsingleton_openModuleCohomology_of_isAffineOpen X _ (U ⊓ S) hUS p hpos
    let e : CohomologyFractionPresentation L F s p U ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj F :=
      { toFun := fun _ ↦ 0
        invFun := fun _ ↦ 0
        left_inv := fun _ ↦ Subsingleton.elim _ _
        right_inv := fun _ ↦ Subsingleton.elim _ _
        map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
    exact ⟨e, fun _ _ ↦ Subsingleton.elim _ _⟩

end AlgebraicGeometry.Scheme.Modules
