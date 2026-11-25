/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.PrincipalThickeningSingleLift

/-! # Lifting sections across a bounded gap of principal thickenings

## References

* Stacks Project, Tags 0H3D and 0H3E (Lemma 20.39.2 and Example 20.39.3)
* Stacks Project, Tags 0H3D and 0H3E (Lemma 20.39.2 and Example 20.39.3, the pro-isomorphism of
  multiplication complexes with quotients)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Vanishing of H^1 and a uniform power-torsion bound give eventual lifting
from principal thickenings to the ambient open. -/
theorem principal_thickening_sections_lift
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (hH : Subsingleton (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) 1))
    (c : ℕ)
    (hkill : ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    ∀ (res : ∀ n k : ℕ, Γ(FiniteEtale.Adic.openThickening f W (n + k), ⊤) →
        Γ(FiniteEtale.Adic.openThickening f W n, ⊤)),
      (∀ n t, res n 0 t = t) →
      (∀ n k t, res n (k + 1) t = res n k
        ((FiniteEtale.Adic.openThickeningTransition f W (n + k)).appTop t)) →
      ∀ n (t : Γ(FiniteEtale.Adic.openThickening f W (n + c), ⊤)),
        ∃ a : Γ(W.toScheme, ⊤),
          (FiniteEtale.Adic.openThickeningMap f W n).appTop a = res n c t := by
  dsimp
  intro res hzero hsucc n t
  have hcanon : ∀ (k : ℕ) (t : Γ(FiniteEtale.Adic.openThickening
      (Ideal.Quotient.mk (Ideal.span {g})) W (n + k), ⊤)),
      res n k t = principalThickeningCanonical R g W n k t := by
    intro k
    induction k with
    | zero =>
        intro t
        simpa [principalThickeningCanonical] using (hzero n t)
    | succ k ih =>
        intro t
        rw [hsucc n k t, ih]
        rfl
  obtain ⟨a, ha⟩ := principal_thickening_single_lift R g W hH c hkill n t
  refine ⟨a, ?_⟩
  exact ha.trans (hcanon c t).symm

end AlgebraicGeometry.Scheme
