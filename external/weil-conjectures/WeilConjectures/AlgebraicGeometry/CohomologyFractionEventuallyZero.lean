/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
import Mathlib.Algebra.Colimit.Module
import all WeilConjectures.AlgebraicGeometry.FractionZeroTensorPower

/-! # Vanishing of a cohomology fraction

Source: Stacks Project, Tag 09MR, degree-zero localization preceding the lemma.
(blueprint: lem-sc-cohomology-fraction-eventually-zero)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A zero fraction has a numerator killed by a further power of the section.

Source: Stacks Project, Tag 09MR, degree-zero localization preceding the lemma;
this is the zero criterion for that localization.
Proof: Tensor multiplication by powers of s has identity transition at exponent zero
and associative transitions, after the canonical tensor-power identifications.
Applying the cohomology functor therefore gives a directed system of additive groups.
Map the direct sum of numerator groups to Mathlib's additive direct limit by its
canonical component maps. Each generating fraction relation maps to zero by the
transition identity, so this map descends to the fraction quotient. Apply it to
the assumed zero fraction. Mathlib's AddCommGroup.DirectLimit.of.zero_exact gives
a later index k where the numerator vanishes. Write k=n+b and identify that
transition with multiplication by s^b. This also handles s=0, n=0, empty opens,
and zero cohomology groups uniformly.
No injectivity of transition maps, quasi-coherence, or compactness is used.
(blueprint: lem-sc-cohomology-fraction-eventually-zero). -/
theorem cohomologyFraction_eventually_zero {X : Scheme.{u}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (W : X.Opens) (n : ℕ)
    (ξ : (openModuleCohomology X.toRingedSpace p W).obj
      (F ⊗ L.tensorPow n : X.Modules))
    (h : cohomologyFraction L F s p W n ξ = 0) :
    ∃ b : ℕ, (openModuleCohomology X.toRingedSpace p W).map
      (mulTensorPowSection (homOfGlobalSection L s) F n b) ξ = 0 := by
  classical
  let H := openModuleCohomology X.toRingedSpace p W
  let G (i : ℕ) : Type u := H.obj (F ⊗ L.tensorPow i : X.Modules)
  let f (i j : ℕ) (hij : i ≤ j) : G i →+ G j :=
    (H.map (tensorSectionTransition (homOfGlobalSection L s) F i j hij)).hom
  have : DirectedSystem G (fun i j hij ↦ f i j hij) := {
    map_self := fun {i} x ↦ by
      dsimp only [f]
      rw [tensorSectionTransition_self, H.map_id]
      rfl
    map_map := fun {k j i} hij hjk x ↦ by
      change (H.map (tensorSectionTransition (homOfGlobalSection L s) F j k hjk))
        ((H.map (tensorSectionTransition (homOfGlobalSection L s) F i j hij)) x) = _
      rw [← ConcreteCategory.comp_apply, ← H.map_comp, tensorSectionTransition_comp]
  }
  let v : (DirectSum ℕ G) →+ AddCommGroup.DirectLimit G f :=
    DirectSum.toAddMonoid (fun i ↦ AddCommGroup.DirectLimit.of G f i)
  have hv : cohomologyFractionRelations L F s p W ≤ v.ker := by
    apply (AddSubgroup.closure_le v.ker).2
    rintro z ⟨i, b, η, rfl⟩
    change v (DirectSum.of G i η - DirectSum.of G (i + b)
      (H.map (mulTensorPowSection (homOfGlobalSection L s) F i b) η)) = 0
    dsimp only [v]
    rw [map_sub, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    have he := AddCommGroup.DirectLimit.of_f (f := f) (Nat.le_add_right i b) η
    dsimp only [f] at he
    rw [tensorSectionTransition_add] at he
    exact sub_eq_zero.mpr he.symm
  let vbar := QuotientAddGroup.lift (cohomologyFractionRelations L F s p W) v hv
  have hlim : AddCommGroup.DirectLimit.of G f n ξ = 0 := by
    have hz := congrArg vbar h
    rw [map_zero] at hz
    change v (DirectSum.of G n ξ) = 0 at hz
    exact (DirectSum.toAddMonoid_of
      (fun i ↦ AddCommGroup.DirectLimit.of G f i) n ξ).symm.trans hz
  obtain ⟨k, hnk, hk⟩ := AddCommGroup.DirectLimit.of.zero_exact (G := G) (f := f) n ξ hlim
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hnk
  refine ⟨b, ?_⟩
  dsimp only [f] at hk
  rw [tensorSectionTransition_add] at hk
  exact hk

end AlgebraicGeometry.Scheme.Modules
