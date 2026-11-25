/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedPrincipalEventualScalarImage

/-! # Finite-level scalar lifts of compatible punctured principal sections

## References

* Stacks Project, Tags 0H3E (the pro-isomorphism of cones with ordinary quotients), 0BLD (degree
  zero), 0BK0 and 0AVY
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Each member of a compatible formal section family has an ambient scalar lift. -/
theorem punctured_principal_finite_level_lift
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f W n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f W n).appTop
        (s (n + 1)) = s n) →
      ∀ n, ∃ a : R,
        ((ΓSpecIso (.of R)).inv ≫
          (FiniteEtale.Adic.openThickeningMap f W n ≫ W.ι).appTop) a = s n := by
  dsimp only
  intro s hs n
  obtain ⟨k, hk⟩ := punctured_principal_eventual_scalar_image R g hg hdepth W hW n
  have hcompat (k : ℕ) :
      puncturedPrincipalSectionRestriction (Ideal.Quotient.mk (Ideal.span {g}))
        W n k (s (n + k)) = s n := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change puncturedPrincipalSectionRestriction (Ideal.Quotient.mk (Ideal.span {g}))
        W n k ((FiniteEtale.Adic.openThickeningTransition
          (Ideal.Quotient.mk (Ideal.span {g})) W (n + k)).appTop
            (s (n + k + 1))) = s n
      rw [hs (n + k)]
      exact ih
  obtain ⟨a, ha⟩ := hk (s (n + k))
  exact ⟨a, ha.trans (hcompat k)⟩

end AlgebraicGeometry.Scheme
