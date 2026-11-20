import Langlands.Global.Factors.GLPoleRegionTransport
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.Representation.RankinSelberg.SupercuspidalParameterProductProof
import Langlands.Representation.RankinSelberg.UnitaryContragredientTwistParameters
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof
import Langlands.Representation.Whittaker.CharacterChange

/-!
# Supercuspidal cases of the GL pole-region statement

Over the canonical realization of a p-adic field:

* if `π` of larger rank is irreducible supercuspidal, its pair L-polynomial against
  any `σ` of Whittaker type of smaller rank is `1` (JPSS 1983, (8.1)(i)), so there is
  no reflected common zero at all;
* in equal rank, if `σ` is irreducible supercuspidal and `π` is irreducible of
  Whittaker type, the pair L-polynomial is `∏_{a ∈ A} (1 - a X)` and the dual one is
  `∏_{a ∈ A} (1 - a⁻¹ X)` (JPSS 1983, (8.1)(ii), after swapping the pair), and all
  parameters `a ∈ A` have the same absolute value by central characters, which
  excludes a reflected common zero.
-/

noncomputable section

namespace Langlands.Global.GLPoleRegion

universe uF uV uW uG

open HarmonicAnalysis Whittaker GeneralLinear RankinSelberg Polynomial
open RankinSelberg.SegmentGammaTelescoping

section CharacterChange

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Whittaker type for `ψ⁻¹ = ψ.scale (-1)` gives Whittaker type for `ψ`. -/
theorem isOfWhittakerType_of_scale_neg_one (ψ : UnitaryAdditiveCharacter K)
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) K) V}
    (h : IsOfWhittakerType n (standardCharacter (ψ.scale (-1)) n) π) :
    IsOfWhittakerType n (standardCharacter ψ n) π := by
  refine ⟨h.1, h.2.1, ?_⟩
  obtain ⟨e⟩ := h.2.2
  exact ⟨(characterChangeFunctionalEquiv ψ π (-1)).trans e⟩

end CharacterChange

section Pairing

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

/-- A nonzero twisted invariant bilinear form between representations with central
characters `ωπ` and `ωσ` identifies the inverse of its twisting character on the
center with `ωπ ωσ`. -/
theorem character_center_eq_of_twisted_bilinear
    (ωπ ωσ : Subgroup.center G →* ℂˣ)
    (hπ : ∀ (z : Subgroup.center G) (v : V), π z v = (ωπ z : ℂ) • v)
    (hσ : ∀ (z : Subgroup.center G) (w : W), σ z w = (ωσ z : ℂ) • w)
    (χ : G →* ℂˣ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hβ : β ≠ 0)
    (hcov : ∀ g v w, β (π g v) (σ g w) = (χ g : ℂ)⁻¹ * β v w)
    (z : Subgroup.center G) :
    (χ z : ℂ)⁻¹ = (ωπ z : ℂ) * (ωσ z : ℂ) := by
  obtain ⟨v, w, hvw⟩ : ∃ v w, β v w ≠ 0 := by
    by_contra h
    push Not at h
    apply hβ
    ext v w
    exact h v w
  have hcovz := hcov z v w
  simp only [hπ, hσ, map_smul, LinearMap.smul_apply, smul_eq_mul] at hcovz
  apply mul_right_cancel₀ hvw
  rw [← hcovz]
  ring

end Pairing

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Two contragredient unramified-twist parameters `a`, `b` of a pair of
irreducible admissible representations of `GL_(r+1)` satisfy `a^(r+1) = b^(r+1)`:
at the inverse-uniformizer scalar `z = ϖ⁻¹ · 1` (`centralSpectralElement`), each
parameter satisfies `a^(r+1) = (ωπ(z) ωσ(z))⁻¹`, where `ωπ`, `ωσ` are the central
characters. Equivalently `a^(r+1) = ωπ(ϖ · 1) ωσ(ϖ · 1)`. -/
theorem IsContragredientTwistParameter.pow_eq_pow {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W} {a b : ℂ}
    (ha : IsContragredientTwistParameter F π σ a)
    (hb : IsContragredientTwistParameter F π σ b)
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπa : letI := F.canonicalTopologicalData.topology; IsAdmissible π)
    (hσa : letI := F.canonicalTopologicalData.topology; IsAdmissible σ) :
    a ^ (r + 1) = b ^ (r + 1) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (r + 1)
  obtain ⟨ωπ, ⟨_, hπact⟩, _⟩ := admissibleSchur_centralCharacter π hπa hπ
  obtain ⟨ωσ, ⟨_, hσact⟩, _⟩ := admissibleSchur_centralCharacter σ hσa hσ
  let z : Subgroup.center (Langlands.GeneralLinear (r + 1) F.Carrier) :=
    ⟨centralSpectralElement T (r + 1), centralSpectralElement_mem_center T (r + 1)⟩
  have key : ∀ c : ℂ, IsContragredientTwistParameter F π σ c →
      c ^ (r + 1) = ((ωπ z : ℂ) * (ωσ z : ℂ))⁻¹ := by
    intro c hc
    obtain ⟨u, rfl, χ, hχ, ⟨e⟩⟩ := hc
    obtain ⟨β, hβ, hcov⟩ := exists_twisted_bilinear_of_contragredient_equiv
      π σ (χ.comp determinant) hπ e
    have hn := character_center_eq_of_twisted_bilinear ωπ ωσ hπact hσact
      (χ.comp determinant) β hβ hcov z
    have hvalue : ((χ.comp determinant)
        (z : Langlands.GeneralLinear (r + 1) F.Carrier) : ℂ) =
        ((T.residueCardinality : ℂ) ^ (-u)) ^ (r + 1) := by
      rw [MonoidHom.comp_apply, hχ]
      change determinantWeight (normalizedAbsoluteValue T)
        (centralSpectralElement T (r + 1)) (-u) =
        ((T.residueCardinality : ℂ) ^ (-u)) ^ (r + 1)
      simpa only [neg_neg, spectralPoint] using
        determinantWeight_centralSpectralElement T (r + 1) u
    rw [← hvalue, ← hn, inv_inv]
  rw [key a ha, key b hb]

/-- Unequal rank, `π` supercuspidal of the larger rank: the pair L-polynomial is
`1`, so there is no reflected common zero with any polynomial. -/
theorem hasNoReflectedCommonZero_of_supercuspidal_unequalRank
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {r t : ℕ} (htr : t < r) {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
    (hiπ : Representation.IsIrreducible π)
    (hscπ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal π)
    (hσW : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ)
    {P Pdual : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν.val π σ P) :
    HasNoReflectedCommonZero F.canonicalTopologicalData.residueCardinality P Pdual := by
  have h₁ := supercuspidalUnequalRankLFactor p F ψ ν r t π σ hiπ hscπ hσW htr
  rw [hP.unique h₁]
  rintro z - ⟨h, -⟩
  simp at h

/-- Equal rank, `σ` irreducible supercuspidal and `π` irreducible, both of Whittaker
type for `ψ`: the pair L-polynomial `∏_{a ∈ A} (1 - a X)` and the dual
`∏_{a ∈ A} (1 - a⁻¹ X)` have no reflected common zero, since a common zero would
give `a = q b` for parameters of equal absolute value. -/
theorem hasNoReflectedCommonZero_of_supercuspidal_equalRank
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    (hiπ : Representation.IsIrreducible π) (hiσ : Representation.IsIrreducible σ)
    (hscσ : letI := F.canonicalTopologicalData.topology; IsSupercuspidal σ)
    (hπW : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσW : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType n (standardCharacter ψ n) σ)
    {P Pdual : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν.val π σ P)
    (hPd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsPadicPairLPolynomial F (ψ.scale (-1)) ν.val (inverseTransposePullback π)
        (inverseTransposePullback σ) Pdual) :
    HasNoReflectedCommonZero F.canonicalTopologicalData.residueCardinality P Pdual := by
  classical
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨A, hAmem, hA, hAd, -⟩ :=
    supercuspidalParameterProduct p F ψ ν n σ π hiσ hscσ hiπ hπW
  have e₁ : P = ∏ a ∈ A, linearFactor a :=
    ((isPadicPairLPolynomial_swap_equalRank F ψ ν.val π σ P).1 hP).unique hA
  have e₂ : Pdual = ∏ a ∈ A, linearFactor a⁻¹ :=
    ((isPadicPairLPolynomial_swap_equalRank F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback σ) Pdual).1 hPd).unique hAd
  subst e₁ e₂
  rintro z hz ⟨h₁, h₂⟩
  rw [eval_prod, Finset.prod_eq_zero_iff] at h₁ h₂
  obtain ⟨a, haA, ha⟩ := h₁
  obtain ⟨b, hbA, hb⟩ := h₂
  simp only [linearFactor, eval_sub, eval_one, eval_mul, eval_C, eval_X, sub_eq_zero] at ha hb
  have hpow := IsContragredientTwistParameter.pow_eq_pow ((hAmem a).1 haA) ((hAmem b).1 hbA)
    hiσ hiπ hσW.1 hπW.1
  have hnorm : ‖(a : ℂ)‖ = ‖(b : ℂ)‖ := by
    have h := congrArg norm hpow
    rw [norm_pow, norm_pow] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (Nat.succ_ne_zero n)).1 h
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  have hq0 : (F.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0 := by
    have : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by linarith
    exact_mod_cast this.ne'
  have hza : (a : ℂ) = z⁻¹ := eq_inv_of_mul_eq_one_left ha.symm
  rw [← hza] at hb
  have hab : (a : ℂ) = (F.canonicalTopologicalData.residueCardinality : ℂ) * b := by
    have hb0 : ((b : ℂˣ) : ℂ) ≠ 0 := b.ne_zero
    field_simp at hb
    rw [hb, Units.val_inv_eq_inv_val]
    field_simp
  have hn := congrArg norm hab
  rw [norm_mul, Complex.norm_natCast, hnorm] at hn
  have hb0 : 0 < ‖(b : ℂ)‖ := norm_pos_iff.2 b.ne_zero
  nlinarith

end Langlands.Global.GLPoleRegion
