/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoPunctureGlobalSections
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthThreePunctureHOne
import WeilConjectures.AlgebraicGeometry.Morphisms.PrincipalThickeningSectionsLift

/-! # Eventual scalar image on punctured principal thickenings

## References

* Stacks Project, Tags 0H3E (Example 20.39.3), 0BK0 (Lemma 51.8.2) and 0AVY (Lemma 47.11.1)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Restriction across `k` consecutive thickenings, constructed by composition. -/
noncomputable def puncturedPrincipalSectionRestriction
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (W : (Spec (.of R)).Opens) (n : ℕ) :
    (k : ℕ) → Γ(FiniteEtale.Adic.openThickening f W (n + k), ⊤) →
      Γ(FiniteEtale.Adic.openThickening f W n, ⊤)
  | 0 => fun t ↦ t
  | k + 1 => fun t ↦ puncturedPrincipalSectionRestriction f W n k
      ((FiniteEtale.Adic.openThickeningTransition f W (n + k)).appTop t)

private theorem scalar_power_torsion_bound
    (R : Type u) [CommRing R] [IsNoetherianRing R] (g : R) :
    ∃ c : ℕ, ∀ (j : ℕ) (s : R), g ^ j * s = 0 → g ^ c * s = 0 := by
  let K : ℕ →o Submodule R R :=
    { toFun := fun j ↦ (LinearMap.mulLeft R (g ^ j)).ker
      monotone' := by
        intro j l h s hs
        change g ^ j * s = 0 at hs
        change g ^ l * s = 0
        rw [← Nat.sub_add_cancel h, pow_add, mul_assoc, hs, mul_zero] }
  obtain ⟨c, hc⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  refine ⟨c, ?_⟩
  intro j s hs
  by_cases h : c ≤ j
  · have hj : s ∈ K j := hs
    rw [← hc j h] at hj
    exact hj
  · have h : j ≤ c := by omega
    exact K.monotone h hs

/-- At any fixed level, sufficiently late sections restrict into the scalar image. -/
theorem punctured_principal_eventual_scalar_image
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    ∀ n, ∃ k : ℕ,
      ∀ t : Γ(FiniteEtale.Adic.openThickening f W (n + k), ⊤), ∃ a : R,
        ((ΓSpecIso (.of R)).inv ≫
          (FiniteEtale.Adic.openThickeningMap f W n ≫ W.ι).appTop) a =
            puncturedPrincipalSectionRestriction f W n k t := by
  classical
  have _ := hg
  dsimp only
  let f := Ideal.Quotient.mk (Ideal.span {g})
  let ρ : CommRingCat.of R ⟶ Γ(W.toScheme, ⊤) :=
    (ΓSpecIso (.of R)).inv ≫ W.ι.appTop
  have hρ : Function.Surjective ρ :=
    ((depth_two_puncture_globalSections_bijective R
      (le_trans (by decide) hdepth) W hW).comp
        (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).inv)).surjective
  obtain ⟨c, hc⟩ := scalar_power_torsion_bound R g
  have hH := depth_three_puncture_h_one R hdepth W hW
  have hlift := principal_thickening_sections_lift R g W hH c hc
    (puncturedPrincipalSectionRestriction f W) (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
  intro n
  refine ⟨c, ?_⟩
  intro t
  obtain ⟨s, hs⟩ := hlift n t
  obtain ⟨a, ha⟩ := hρ s
  refine ⟨a, ?_⟩
  rw [← ha] at hs
  simpa only [ρ, Scheme.Hom.comp_appTop, ← Category.assoc,
    ConcreteCategory.comp_apply] using hs

end AlgebraicGeometry.Scheme
