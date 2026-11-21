import Langlands.Representation.Plancherel.CompactIntertwiningWeakRegularity
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Local domination on open regions of full convergence -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

universe u uG uI uV

private def positiveExpUnit (t : ℝ) : ℂˣ :=
  Units.mk0 (Complex.exp (t : ℂ)) (Complex.exp_ne_zero _)

private theorem continuous_positiveExpUnit : Continuous positiveExpUnit := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  exact Complex.continuous_exp.comp Complex.continuous_ofReal

private theorem norm_positiveExpUnit (t : ℝ) :
    ‖(positiveExpUnit t : ℂ)‖ = Real.exp t := by
  simp [positiveExpUnit, Complex.norm_exp]

private theorem zpow_le_zpow_of_nonpos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {n : ℤ} (hn : n ≤ 0) : b ^ n ≤ a ^ n := by
  have h := zpow_le_zpow_left₀ (neg_nonneg.mpr hn) (inv_pos.mpr (ha.trans_le hab)).le
    (inv_anti₀ ha hab)
  simpa only [inv_zpow, ← zpow_neg, neg_neg] using h

private theorem exists_monomial_corner_bounds {X : Type*} [TopologicalSpace X]
    {n : ℕ} (e : X ≃ₜ (Fin n → ℂˣ)) {Ω : Set X} (hΩ : IsOpen Ω) (x : Ω) :
    ∃ z : (Fin n → Bool) → Ω, ∀ᶠ y : Ω in 𝓝 x,
      ∀ a : Fin n → ℤ,
        ‖((∏ i, e y.val i ^ a i : ℂˣ) : ℂ)‖ ≤
          ‖((∏ i, e (z (fun i => decide (0 ≤ a i))).val i ^ a i : ℂˣ) : ℂ)‖ := by
  let v (b : Fin n → Bool) (t : ℝ) : X :=
    e.symm fun i => e x.val i * positiveExpUnit (if b i then t else -t)
  have hv (b : Fin n → Bool) : Continuous (v b) := by
    apply e.symm.continuous.comp (continuous_pi fun i => ?_)
    apply continuous_const.mul
    refine continuous_positiveExpUnit.comp ?_
    cases b i
    · simpa using (continuous_neg : Continuous fun t : ℝ => -t)
    · change Continuous (id : ℝ → ℝ)
      exact continuous_id
  have hv0 (b : Fin n → Bool) : v b 0 = x.val := by
    apply e.injective
    funext i
    simp [v, positiveExpUnit]
  have hnear (b : Fin n → Bool) : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), v b t ∈ Ω :=
    (hv b).continuousAt (hΩ.mem_nhds (hv0 b ▸ x.property))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((Filter.eventually_all.mpr hnear) : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ b, v b t ∈ Ω)
  let t : ℝ := ε / 2
  have ht : 0 < t := half_pos hε
  have htε : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact half_lt_self hε
  let z (b : Fin n → Bool) : Ω := ⟨v b t, hball htε b⟩
  have hz (b : Fin n → Bool) (i : Fin n) :
      ‖(e (z b).val i : ℂ)‖ = ‖(e x.val i : ℂ)‖ * Real.exp (if b i then t else -t) := by
    simp [z, v, norm_positiveExpUnit]
  have hcenter (i : Fin n) : 0 < ‖(e x.val i : ℂ)‖ :=
    norm_pos_iff.mpr (Units.ne_zero _)
  have hinterval (i : Fin n) : ∀ᶠ y : Ω in 𝓝 x,
      ‖(e x.val i : ℂ)‖ * Real.exp (-t) < ‖(e y.val i : ℂ)‖ ∧
        ‖(e y.val i : ℂ)‖ < ‖(e x.val i : ℂ)‖ * Real.exp t := by
    have hc : Continuous (fun y : Ω => ‖(e y.val i : ℂ)‖) :=
      (Units.continuous_val.comp ((continuous_apply i).comp
        (e.continuous.comp continuous_subtype_val))).norm
    have h₁ : Real.exp (-t) < 1 := by
      rw [← Real.exp_zero, Real.exp_lt_exp]
      exact neg_neg_of_pos ht
    have h₂ : 1 < Real.exp t := by
      rw [← Real.exp_zero, Real.exp_lt_exp]
      exact ht
    exact (continuousAt_const.eventually_lt hc.continuousAt
      (by simpa only [mul_one] using mul_lt_mul_of_pos_left h₁ (hcenter i))).and
      (hc.continuousAt.eventually_lt continuousAt_const
        (by simpa only [mul_one] using mul_lt_mul_of_pos_left h₂ (hcenter i)))
  refine ⟨z, (Filter.eventually_all.mpr hinterval).mono fun y hy a => ?_⟩
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, norm_prod, norm_zpow]
  apply Finset.prod_le_prod₀
    (fun i _ => zpow_nonneg (norm_nonneg _) _)
  intro i _
  rw [hz]
  by_cases hi : 0 ≤ a i
  · simpa [hi] using zpow_le_zpow_left₀ hi (norm_nonneg _) (hy i).2.le
  · simpa [hi] using zpow_le_zpow_of_nonpos (mul_pos (hcenter i) (Real.exp_pos _))
      (hy i).1.le (le_of_not_ge hi)

section Integral

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (U' : Subgroup G)
  [MeasurableSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))

/-- An open region of full convergence in a finite character torus gives
locally integrable bounds for the actual compact scalar integrands. -/
theorem compactIntegralLocallyDominatedOn_of_isOpen_of_monomials
    {n : ℕ} (e : unramifiedCharacters ν ≃ₜ (Fin n → ℂˣ))
    (hmonomial : ∀ m : M, ∃ a : Fin n → ℤ, ∀ χ : unramifiedCharacters ν,
      χ.val m = ∏ i, e χ i ^ a i)
    {Ω : Set (unramifiedCharacters ν)} (hΩ : IsOpen Ω)
    (hfull : ∀ χ : Ω, domain h hU U'
      (A.twist χ.val.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ.val)) qν = ⊤) :
    CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK ν hν hr A U' qν Ω := by
  intro f k ℓ χ₀
  obtain ⟨z, hbound⟩ := exists_monomial_corner_bounds e hΩ χ₀
  let g (χ : Ω) (q : QuotientSpace (U := U) U') :=
    ℓ.val (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f k χ.val q)
  refine ⟨fun q => ∑ b, ‖g (z b) q‖, integrable_finsetSum _ fun b _ => ?_,
    hbound.mono fun χ hχ => Filter.Eventually.of_forall fun q => ?_⟩
  · exact (unramifiedCompactIntegrand_scalar_integrable h hU hδ K hP hK hPK ν hν hr A U'
      qν (z b).val (hfull (z b)) f k ℓ).norm
  induction q using Quotient.inductionOn with
  | h u' =>
    obtain ⟨m, v, hv⟩ := unramifiedCompactExtension_eval_factor h hU hδ K hP hK hPK ν hν hr A
      f ((u' : G) * (k : G))
    obtain ⟨a, ha⟩ := hmonomial m
    let b : Fin n → Bool := fun i => decide (0 ≤ a i)
    have he (y : Ω) : ‖g y ⟦u'⟧‖ = ‖(y.val.val m : ℂ)‖ * ‖ℓ.val v‖ := by
      calc
        ‖g y ⟦u'⟧‖ = ‖ℓ.val ((y.val.val m : ℂ) • v)‖ :=
          congrArg (fun w : A => ‖ℓ.val w‖) (hv y.val)
        _ = ‖(y.val.val m : ℂ)‖ * ‖ℓ.val v‖ := by rw [map_smul, smul_eq_mul, norm_mul]
    calc
      ‖g χ ⟦u'⟧‖ ≤ ‖g (z b) ⟦u'⟧‖ := by
        rw [he χ, he (z b), ha χ.val, ha (z b).val]
        exact mul_le_mul_of_nonneg_right (hχ a) (norm_nonneg _)
      _ ≤ ∑ b', ‖g (z b') ⟦u'⟧‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg (g (z j) ⟦u'⟧)) (Finset.mem_univ b)

end Integral

section ActualCoordinates

open GroupScheme AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine M.X.left]
  {L : Type uG} [Group L] [TopologicalSpace L]

local instance openDominationRationalPointTopology : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X

variable (hM : IsConnectedReductive M) (e : rationalPoints M ≃ₜ* L)

set_option hygiene false in
local notation "νM" => (fun ψ => (rationalNormCharacters M ψ).toMul)
set_option hygiene false in
local notation "νL" => (fun ψ => (νM ψ).comp e.symm.toMulEquiv.toMonoidHom)

/-- Finite complex character coordinates on a multiplicatively homeomorphic
copy of the actual rational points, with the full transported norm family. -/
def transportedRationalUnramifiedCharacterCoordinates :
    unramifiedCharacters νL ≃ₜ* (Fin (rationalImageRank M) → ℂˣ) :=
  (unramifiedCharactersHomeomorph e νM).symm.trans
    (rationalCanonicalUnramifiedCharacterCoordinates M hM)

/-- Each transported character evaluation is the Laurent monomial of the
actual valuation image of the point. -/
theorem transportedRationalUnramifiedCharacterCoordinates_apply_eval
    (χ : unramifiedCharacters νL) (m : L) :
    χ.val m = ∏ i, transportedRationalUnramifiedCharacterCoordinates hM e χ i ^
      ((rationalReductiveValuationBasis M hM).repr
        (Additive.ofMul (rationalValuationImageProjection M (e.symm m))) i) := by
  let f := rationalCanonicalUnramifiedCharacterCoordinates M hM
  let χM := (unramifiedCharactersHomeomorph e νM).symm χ
  change χ.val m = ∏ i, f χM i ^ _
  have h := rationalCanonicalUnramifiedCharacterCoordinates_symm_apply M hM (f χM) (e.symm m)
  rw [show (rationalCanonicalUnramifiedCharacterCoordinates M hM).symm (f χM) = χM
    from f.symm_apply_apply χM] at h
  simpa only [χM, unramifiedCharactersHomeomorph_symm_apply, e.apply_symm_apply] using h

end ActualCoordinates

end Langlands.Plancherel
