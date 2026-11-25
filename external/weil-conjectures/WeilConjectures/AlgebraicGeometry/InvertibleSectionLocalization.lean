/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.SectionFractionRestrictionMap
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.SectionClearingDenominatorsQCQS
import WeilConjectures.AlgebraicGeometry.SectionRestrictionSTorsion

/-! # Localization of sections at a section of an invertible module

Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), part (2),
equation module-invert-s (blueprint: lem-sc-p1-invertible-section-localization).
-/

@[expose] public section

universe uL

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem fraction_transition {X : Scheme.{uL}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (n b : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)) :
    sectionFraction L F s n t = sectionFraction L F s (n + b)
      ((mulTensorPowSection (homOfGlobalSection L s) F n b).app ⊤ t) := by
  apply sub_eq_zero.mp
  change (sectionFractionRelations L F s).mkQ _ -
    (sectionFractionRelations L F s).mkQ _ = 0
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply Submodule.subset_span
  exact ⟨n, b, t, rfl⟩

private theorem fraction_add {X : Scheme.{uL}} (L F : X.Modules) (s : Γ(L, ⊤))
    (n : ℕ) (t t' : Γ(F ⊗ L.tensorPow n, ⊤)) :
    sectionFraction L F s n (t + t') =
      sectionFraction L F s n t + sectionFraction L F s n t' := by
  exact map_add ((sectionFractionRelations L F s).mkQ.toAddMonoidHom.comp
    (DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, ⊤)) n)) t t'

private theorem fraction_zero {X : Scheme.{uL}} (L F : X.Modules) (s : Γ(L, ⊤))
    (n : ℕ) : sectionFraction L F s n 0 = 0 := by
  exact map_zero ((sectionFractionRelations L F s).mkQ.toAddMonoidHom.comp
    (DirectSum.of (fun i : ℕ ↦ Γ(F ⊗ L.tensorPow i, ⊤)) n))

private theorem fraction_normal_form {X : Scheme.{uL}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (z : SectionFractionPresentation L F s) :
    ∃ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)), sectionFraction L F s n t = z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    induction z using DirectSum.induction_on with
    | zero => exact ⟨0, 0, fraction_zero L F s 0⟩
    | of n t => exact ⟨n, t, rfl⟩
    | add x y hx hy =>
      obtain ⟨n, t, ht⟩ := hx
      obtain ⟨m, u, hu⟩ := hy
      let t' := (mulTensorPowSection (homOfGlobalSection L s) F n m).app ⊤ t
      let u' := (mulTensorPowSection (homOfGlobalSection L s) F m n).app ⊤ u
      have ht' : sectionFraction L F s (n + m) t' =
          (sectionFractionRelations L F s).mkQ x :=
        (fraction_transition L F s n m t).symm.trans ht
      have hu' : sectionFraction L F s (m + n) u' =
          (sectionFractionRelations L F s).mkQ y :=
        (fraction_transition L F s m n u).symm.trans hu
      have hyrepr : ∃ u'' : Γ(F ⊗ L.tensorPow (m + n), ⊤),
          sectionFraction L F s (m + n) u'' =
            (sectionFractionRelations L F s).mkQ y := ⟨u', hu'⟩
      rw [Nat.add_comm m n] at hyrepr
      obtain ⟨u'', hu''⟩ := hyrepr
      refine ⟨n + m, t' + u'', ?_⟩
      rw [fraction_add, ht', hu'']
      exact rfl

/-- Degree-zero section fractions identify canonically with sections on the nonvanishing
open. The fraction formula is written without choosing an inverse tensor power:
`e(t/s^n) ⊗ s^n = t|_U`. Scalar compatibility specifies an isomorphism of modules,
with scalars restricted along `Γ(X, O_X) → Γ(U, O_X)`.
Source: Stacks Project, Properties, Lemma 01PW (lemma-invert-s-sections), part (2).
(blueprint: lem-sc-p1-invertible-section-localization).

Step 1: if a fraction restricts to zero, its numerator restricts to zero because `s`
trivializes `L` on this open. Apply lem-sc-p1-section-restriction-s-torsion to obtain a
power of `s` killing the numerator; the fraction relations then kill the fraction.
Step 2: for a section on this open, lem-sc-p1-section-clearing-denominators-qcqs gives a
nonnegative exponent and a global twisted numerator whose restriction is the section
multiplied by that power of `s`. This fraction maps to the original section.
The tensor construction is additive and commutes with scalar restriction. -/
theorem exists_sectionFraction_nonvanishing_equiv
    (X : Scheme.{uL}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ U : X.Opens, (U : Set X) = nonvanishingLocus L s ∧
      ∃ e : SectionFractionPresentation L F s ≃+ Γ(F, U),
        (∀ (r : Γ(X, ⊤)) (z : SectionFractionPresentation L F s),
          e (r • z) = (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • e z) ∧
        (∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)),
          tmulSection (e (sectionFraction L F s n t))
              (tensorPowSectionOne (homOfGlobalSection L s) n U) =
            (F ⊗ L.tensorPow n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op t) := by
  classical
  obtain ⟨U, hU, _, hquot⟩ := nonvanishing_section_trivializes X L s
  have hs : IsFreeGenerator ((homOfGlobalSection L s).app U (unitSectionsEquiv U 1)) := by
    intro V hV
    have hb := hquot V hV
    change Function.Bijective (fun r : Γ(X, V) ↦
      r • L.presheaf.map (homOfLE hV).op
        ((homOfGlobalSection L s).app U (1 : Γ(X, U))))
    rw [homOfGlobalSection_app_one, presheaf_map_map_apply]
    constructor
    · intro a b hab
      obtain ⟨c, hc, huniq⟩ := hb
        (a • L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s)
      exact (huniq a rfl).trans (huniq b hab).symm
    · intro t
      obtain ⟨a, ha, _⟩ := hb t
      exact ⟨a, ha.symm⟩
  have hcancel (n : ℕ) : Function.Injective (fun t : Γ(F, U) ↦
      tmulSection t (tensorPowSectionOne (homOfGlobalSection L s) n U)) := by
    simpa only [presheaf_map_id_apply] using
      (IsFreeGenerator.bijective_tmulSection_right (M := F)
        (isFreeGenerator_tensorPowSectionOne (homOfGlobalSection L s) hs n) le_rfl).1
  obtain ⟨f, hscalar, hformula⟩ := exists_sectionFraction_restriction_map L F s U hs
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro z hz
    obtain ⟨n, t, rfl⟩ := fraction_normal_form L F s z
    have ht : (F ⊗ L.tensorPow n).presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op t = 0 := by
      rw [← hformula, hz, zero_tmulSection]
    have : (F ⊗ L.tensorPow n).IsQuasicoherent :=
      isQuasicoherent_tensorObj F (L.tensorPow n)
    obtain ⟨m, hm⟩ := section_restriction_s_torsion L (F ⊗ L.tensorPow n) s t U hU ht
    rw [fraction_transition L F s n m t]
    have hmul : (mulTensorPowSection (homOfGlobalSection L s) F n m).app ⊤ t = 0 := by
      rw [mulTensorPowSection_app, hm, map_zero, map_zero]
    rw [hmul, fraction_zero]
  have hsurj : Function.Surjective f := by
    intro t
    obtain ⟨n, u, hu⟩ := exists_tensorPowSection_eq_restrict_qcqs L s F U hU t
    refine ⟨sectionFraction L F s n u, hcancel n ?_⟩
    exact (hformula n u).trans hu
  refine ⟨U, hU, AddEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · exact hscalar
  · exact hformula

end AlgebraicGeometry.Scheme.Modules
