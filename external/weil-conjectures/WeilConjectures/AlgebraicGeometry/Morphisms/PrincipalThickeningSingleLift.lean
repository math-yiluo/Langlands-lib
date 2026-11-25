/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Morphisms.PrincipalThickeningIdealFactor

/-! # Lifting sections across a bounded principal thickening gap

## References

* Stacks Project, Tags 0H3D and 0H3E
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

noncomputable def principalThickeningCanonical
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (n k : ℕ) : Γ(FiniteEtale.Adic.openThickening
      (Ideal.Quotient.mk (Ideal.span {g})) W (n + k), ⊤) →
      Γ(FiniteEtale.Adic.openThickening
        (Ideal.Quotient.mk (Ideal.span {g})) W n, ⊤) :=
  match k with
  | 0 => id
  | k + 1 => principalThickeningCanonical R g W n k ∘
      (FiniteEtale.Adic.openThickeningTransition
        (Ideal.Quotient.mk (Ideal.span {g})) W (n + k)).appTop

private noncomputable def thickeningGap
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (n k : ℕ) : FiniteEtale.Adic.openThickening
        (Ideal.Quotient.mk (Ideal.span {g})) W n ⟶
      FiniteEtale.Adic.openThickening (Ideal.Quotient.mk (Ideal.span {g})) W (n + k) :=
  match k with
  | 0 => 𝟙 _
  | k + 1 => thickeningGap R g W n k ≫ FiniteEtale.Adic.openThickeningTransition
      (Ideal.Quotient.mk (Ideal.span {g})) W (n + k)

private theorem thickeningGap_comp_map
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) (n k : ℕ) :
    thickeningGap R g W n k ≫ FiniteEtale.Adic.openThickeningMap
        (Ideal.Quotient.mk (Ideal.span {g})) W (n + k) =
      FiniteEtale.Adic.openThickeningMap (Ideal.Quotient.mk (Ideal.span {g})) W n := by
  induction k with
  | zero => simp [thickeningGap]
  | succ k ih =>
      change (thickeningGap R g W n k ≫ _) ≫ _ = _
      rw [Category.assoc]
      have hc : FiniteEtale.Adic.openThickeningTransition
          (Ideal.Quotient.mk (Ideal.span {g})) W (n + k) ≫
          FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W (n + (k + 1)) =
          FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W (n + k) := by
        change FiniteEtale.Adic.openThickeningTransition
          (Ideal.Quotient.mk (Ideal.span {g})) W (n + k) ≫
          FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W ((n + k) + 1) = _
        simp [FiniteEtale.Adic.openThickeningTransition, FiniteEtale.Adic.openThickeningMap]
      rw [hc]
      exact ih

private theorem thickeningGap_appTop
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) (n k : ℕ)
    (t : Γ(FiniteEtale.Adic.openThickening
      (Ideal.Quotient.mk (Ideal.span {g})) W (n + k), ⊤)) :
    (thickeningGap R g W n k).appTop t = principalThickeningCanonical R g W n k t := by
  induction k with
  | zero => simp [thickeningGap, principalThickeningCanonical]
  | succ k ih =>
      change (thickeningGap R g W n k ≫ _).appTop t =
        principalThickeningCanonical R g W n k
          ((FiniteEtale.Adic.openThickeningTransition
            (Ideal.Quotient.mk (Ideal.span {g})) W (n + k)).appTop t)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      exact ih _

/-- If `H^1(W, O_W)` vanishes and `g`-power torsion of `R` is killed by `g ^ c`, then the
canonical image at level `n` of every section on the `(n + c)`-th principal thickening of `W`
is the restriction of a section of `W`. -/
theorem principal_thickening_single_lift
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens)
    (hH : Subsingleton (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) 1))
    (c : ℕ)
    (hkill : ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0) :
    ∀ n (t : Γ(FiniteEtale.Adic.openThickening
      (Ideal.Quotient.mk (Ideal.span {g})) W (n + c), ⊤)),
      ∃ a : Γ(W.toScheme, ⊤),
        (FiniteEtale.Adic.openThickeningMap
          (Ideal.Quotient.mk (Ideal.span {g})) W n).appTop a =
          principalThickeningCanonical R g W n c t := by
  intro n t
  obtain ⟨δ, hex, hnat⟩ := principal_thickening_obstruction R g W
  obtain ⟨d, hd⟩ := principal_thickening_ideal_factor R g W c n hkill
  let κ := d ≫ CategoryTheory.Limits.factorThruImage
    (principalThickeningMultiplication R g W n)
  have hκ : κ ≫ CategoryTheory.Limits.image.ι
      (principalThickeningMultiplication R g W n) =
      CategoryTheory.Limits.image.ι (principalThickeningMultiplication R g W (n + c)) := by
    dsimp only [κ]
    rw [Category.assoc, CategoryTheory.Limits.image.fac]
    exact hd
  have hδ : δ n ((thickeningGap R g W n c).appTop t) = 0 := by
    rw [hnat n (n + c) κ (thickeningGap R g W n c) hκ
      (thickeningGap_comp_map R g W n c) t]
    change Modules.H.map (d ≫ CategoryTheory.Limits.factorThruImage
      (principalThickeningMultiplication R g W n)) 1 (δ (n + c) t) = 0
    rw [Modules.H.map_comp_apply]
    have hz : Modules.H.map d 1 (δ (n + c) t) = 0 := hH.elim _ _
    rw [hz, map_zero]
  obtain ⟨a, ha⟩ := hex n ((thickeningGap R g W n c).appTop t) hδ
  exact ⟨a, ha.trans (thickeningGap_appTop R g W n c t)⟩

end AlgebraicGeometry.Scheme
