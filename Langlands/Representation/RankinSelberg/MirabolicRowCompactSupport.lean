import Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof
import Langlands.Representation.RankinSelberg.WhittakerNormData
import Langlands.Analysis.Local.QuotientTopology

/-! # Mirabolic compact translates and row tests away from zero -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped Pointwise

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- Every right translate has compact support modulo the upper unipotent group
on the actual mirabolic subgroup. This is the support part of the Kirillov model. -/
def HasMirabolicCompactTranslates
    (W : Langlands.GeneralLinear (n + 1) F → ℂ) : Prop :=
  ∀ a : Langlands.GeneralLinear (n + 1) F,
    ∃ C : Set (Langlands.GeneralLinear (n + 1) F), IsCompact C ∧
      ∀ p : mirabolic n F, W (p.val * a) ≠ 0 →
        ∃ (u : upperUnipotent (n + 1) F) (c : Langlands.GeneralLinear (n + 1) F),
          c ∈ C ∧ p.val = u.val * c

variable [IsTopologicalDivisionRing F] [T2Space F]

/-- Compact mirabolic support of the translates, together with an ambient compact
open stabilizer, bounds the quotient support after any row test vanishing at zero. -/
theorem HasMirabolicCompactTranslates.exists_compact_row_support
    {W : Langlands.GeneralLinear (n + 1) F → ℂ}
    (hmir : HasMirabolicCompactTranslates W)
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hJ : IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F)))
    (hfix : ∀ g, ∀ j : J, W (g * j.val) = W g)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (hΦ : Φ 0 = 0) :
    ∃ C : Set (LeftUnipotentQuotient n F), IsCompact C ∧
      ∀ g : Langlands.GeneralLinear (n + 1) F,
        W g ≠ 0 → Φ (lastRow g) ≠ 0 →
          leftQuotientMap (upperUnipotent (n + 1) F) g ∈ C := by
  classical
  let a : Function.support Φ → Langlands.GeneralLinear (n + 1) F :=
    fun x => EqualRankFrobenius.lift x.val
  have ha (x : Function.support Φ) : lastRow (a x) = x.val :=
    EqualRankFrobenius.lastRow_lift x.val (fun hx => x.property (hx ▸ hΦ))
  obtain ⟨t, ht⟩ := (Hecke.TestFunction.isCompact_support Φ).elim_finite_subcover
    (fun x : Function.support Φ => EqualRankFrobenius.orbitSet J.toSubgroup (a x))
    (fun x => EqualRankFrobenius.isOpen_orbitSet J.isOpen _) (fun x hx =>
      Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by
        simpa only [ha] using
          EqualRankFrobenius.lastRow_mem_orbitSet J.toSubgroup (a ⟨x, hx⟩)⟩)
  choose C hC hs using hmir
  let D : Function.support Φ → Set (LeftUnipotentQuotient n F) := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F) ''
      ((C (a x) * {a x}) * (J : Set (Langlands.GeneralLinear (n + 1) F)))
  have hD (x : Function.support Φ) : IsCompact (D x) :=
    (((hC (a x)).mul isCompact_singleton).mul hJ).image
      (leftQuotient_isOpenQuotientMap _).continuous
  refine ⟨⋃ x ∈ t, D x, t.isCompact_biUnion (fun x _ => hD x), ?_⟩
  intro g hW hrow
  obtain ⟨x, hx, hj⟩ := Set.mem_iUnion₂.mp (ht hrow)
  obtain ⟨j, hj, hroweq⟩ := hj
  let p : mirabolic n F :=
    ⟨g * (a x * j)⁻¹,
      EqualRankFrobenius.mul_inv_mem_mirabolic_of_lastRow_eq hroweq.symm⟩
  have hg : g = p.val * a x * j := by
    dsimp only [p]
    group
  have hp : W (p.val * a x) ≠ 0 := by
    rw [hg, hfix _ ⟨j, hj⟩] at hW
    exact hW
  obtain ⟨u, c, hc, hpc⟩ := hs (a x) p hp
  apply Set.mem_iUnion₂.mpr ⟨x, hx, ?_⟩
  refine ⟨c * a x * j, Set.mem_mul.mpr
    ⟨c * a x, Set.mem_mul.mpr ⟨c, hc, a x, Set.mem_singleton _, rfl⟩, j, hj, rfl⟩, ?_⟩
  apply Quotient.sound
  change QuotientGroup.rightRel (upperUnipotent (n + 1) F) (c * a x * j) g
  rw [QuotientGroup.rightRel_apply, hg, hpc]
  simpa only [mul_assoc, mul_inv_rev, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, mul_one]
    using u.property

/-- The actual quotient integrand has compact support, at every spectral point,
when the first Whittaker function has the mirabolic compact-translate property. -/
theorem HasMirabolicCompactTranslates.equalRankIntegrand_hasCompactSupport
    {ψ : UnitaryAdditiveCharacter F} {W : WhittakerFunctions ψ n}
    (hmir : HasMirabolicCompactTranslates W.val)
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hJ : IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F)))
    (hfix : ∀ g, ∀ j : J, W.val (g * j.val) = W.val g)
    (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (hΦ : Φ 0 = 0)
    (abv : AbsoluteValue F ℝ) (s : ℂ) :
    HasCompactSupport (equalRankIntegrand ψ abv W W' Φ s) := by
  let : T2Space (LeftUnipotentQuotient n F) :=
    leftQuotient_t2Space _ (GeneralLinear.UpperUnipotent.isClosed (R := F))
  obtain ⟨C, hC, hsupp⟩ := hmir.exists_compact_row_support J hJ hfix Φ hΦ
  apply HasCompactSupport.intro hC
  intro x hx
  induction x using Quotient.inductionOn with
  | h g =>
    rw [equalRankIntegrand_mk]
    by_cases hW : W.val g = 0
    · simp [hW]
    by_cases hrow : Φ (lastRow g) = 0
    · simp [hrow]
    exact False.elim (hx (hsupp g hW hrow))

end Langlands.RankinSelberg
