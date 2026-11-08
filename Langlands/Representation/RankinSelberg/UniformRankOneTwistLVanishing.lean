import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.GodementJacquet.CompactMatrixLaurent
import Langlands.Representation.GodementJacquet.FourierRegularMatrixTests
import Langlands.Representation.GodementJacquet.MatrixTestTranslates
import Langlands.Representation.GodementJacquet.ContinuedMatrixCovariance
import Langlands.Representation.GodementJacquet.ZetaLinear
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport
import Langlands.Representation.GodementJacquet.TwoBlockZetaExpansion
import Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxFourier
import Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedProof
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
import Langlands.Representation.OrbitSpan
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalFixedDual
import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationProof
import Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.Classification.SupercuspidalContragredientAux

/-!
# Godement–Jacquet L-vanishing from a ramified principal-level eigenvector

Internal support for the level-uniform form of Jacquet–Shalika 1985,
Proposition (2.2).
-/

noncomputable section

namespace Langlands.RankinSelberg.UniformRankOneTwist

open MeasureTheory HarmonicAnalysis GodementJacquet
open scoped BigOperators

universe uF uV

section CosetSum

variable {G : Type*} [Group G] (H : Subgroup G) [Finite (G ⧸ H)]

/-- The sum of a function over chosen representatives of the left cosets of `H`. -/
def cosetSum (φ : G → ℂ) : ℂ :=
  letI := Fintype.ofFinite (G ⧸ H)
  ∑ c : G ⧸ H, φ c.out

/-- A right `H`-invariant function has a left-translation invariant coset sum. -/
theorem cosetSum_mul_left {φ : G → ℂ} (hφ : ∀ g, ∀ h ∈ H, φ (g * h) = φ g) (g₀ : G) :
    cosetSum H (fun g => φ (g₀ * g)) = cosetSum H φ := by
  let := Fintype.ofFinite (G ⧸ H)
  have key : ∀ c : G ⧸ H, φ (g₀ * c.out) = φ (g₀ • c).out := by
    intro c
    have hc : (g₀ • c : G ⧸ H) = QuotientGroup.mk (g₀ * c.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' c]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g₀ * c.out)
    rw [hc, hh, hφ _ _ h.2]
  change ∑ c : G ⧸ H, φ (g₀ * c.out) = ∑ c : G ⧸ H, φ c.out
  simp_rw [key]
  exact Equiv.sum_comp (MulAction.toPerm g₀) (fun c : G ⧸ H => φ c.out)

theorem cosetSum_const_mul (a : ℂ) (φ : G → ℂ) :
    cosetSum H (fun g => a * φ g) = a * cosetSum H φ := by
  let := Fintype.ofFinite (G ⧸ H)
  change ∑ c : G ⧸ H, a * φ c.out = a * ∑ c : G ⧸ H, φ c.out
  rw [Finset.mul_sum]

end CosetSum


section Matrix

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance uniformTwistTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance uniformTwistValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance uniformTwistLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance uniformTwistT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance uniformTwistMeasurable : MeasurableSpace F.Carrier := borel _
local instance uniformTwistBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance uniformTwistGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance uniformTwistGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- The finite twisted average `X ↦ ∑_c η(det k_c) Φ(X k_c)` over representatives
`k_c` of the cosets of `H` in `K`. -/
def averagedTest (K : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier)) (H : Subgroup K)
    [Finite (K ⧸ H)] (η : F.Carrierˣ →* ℂˣ) (Φ : MatrixTestFunction n F.Carrier) :
    MatrixTestFunction n F.Carrier :=
  let := Fintype.ofFinite (K ⧸ H)
  ∑ c : K ⧸ H, ((η (Matrix.GeneralLinearGroup.det (c.out : Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂˣ) : ℂ) •
    rectangularTranslate (c.out : Langlands.GeneralLinear (n + 1) F.Carrier) Φ

theorem averagedTest_apply (K : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (H : Subgroup K) [Finite (K ⧸ H)] (η : F.Carrierˣ →* ℂˣ)
    (Φ : MatrixTestFunction n F.Carrier) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    averagedTest F K H η Φ X = cosetSum H (fun k : K =>
      ((η (Matrix.GeneralLinearGroup.det (k : Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂˣ) : ℂ) *
        Φ (X * (k : Langlands.GeneralLinear (n + 1) F.Carrier).val)) := by
  let := Fintype.ofFinite (K ⧸ H)
  change (averagedTest F K H η Φ).1 X = _
  simp only [averagedTest, cosetSum, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl

/-- Right translation by `K` multiplies the twisted average by the inverse twist. -/
theorem averagedTest_mul (K : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (H : Subgroup K) [Finite (K ⧸ H)] (η : F.Carrierˣ →* ℂˣ)
    (Φ : MatrixTestFunction n F.Carrier)
    (hηH : ∀ k ∈ H, η (Matrix.GeneralLinearGroup.det
      ((k : K) : Langlands.GeneralLinear (n + 1) F.Carrier)) = 1)
    (hΦH : ∀ k ∈ H, ∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier,
      Φ (Y * ((k : K) : Langlands.GeneralLinear (n + 1) F.Carrier).val) = Φ Y)
    (k₀ : K) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :
    averagedTest F K H η Φ X =
      ((η (Matrix.GeneralLinearGroup.det (k₀ : Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂˣ) : ℂ) *
        averagedTest F K H η Φ (X * (k₀ : Langlands.GeneralLinear (n + 1) F.Carrier).val) := by
  rw [averagedTest_apply, averagedTest_apply, ← cosetSum_const_mul]
  rw [← cosetSum_mul_left H (g₀ := k₀)]
  · congr 1
    funext k
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul, Matrix.mul_assoc]
    ring
  · intro k h hh
    simp only [Subgroup.coe_mul, map_mul, hηH h hh, mul_one, Units.val_mul, ← Matrix.mul_assoc,
      hΦH h hh]

/-- If some element of `K` with nontrivial twist fixes `X`, the average vanishes at `X`. -/
theorem averagedTest_eq_zero_of_fix (K : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (H : Subgroup K) [Finite (K ⧸ H)] (η : F.Carrierˣ →* ℂˣ)
    (Φ : MatrixTestFunction n F.Carrier)
    (hηH : ∀ k ∈ H, η (Matrix.GeneralLinearGroup.det
      ((k : K) : Langlands.GeneralLinear (n + 1) F.Carrier)) = 1)
    (hΦH : ∀ k ∈ H, ∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier,
      Φ (Y * ((k : K) : Langlands.GeneralLinear (n + 1) F.Carrier).val) = Φ Y)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) (k₀ : K)
    (hfix : X * (k₀ : Langlands.GeneralLinear (n + 1) F.Carrier).val = X)
    (hne : η (Matrix.GeneralLinearGroup.det (k₀ : Langlands.GeneralLinear (n + 1) F.Carrier)) ≠ 1) :
    averagedTest F K H η Φ X = 0 := by
  have h := averagedTest_mul F K H η Φ hηH hΦH k₀ X
  rw [hfix] at h
  have hne' : ((η (Matrix.GeneralLinearGroup.det
      (k₀ : Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂˣ) : ℂ) ≠ 1 := by
    intro h1
    exact hne (Units.ext h1)
  have h2 : (1 - ((η (Matrix.GeneralLinearGroup.det
      (k₀ : Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂˣ) : ℂ)) *
      averagedTest F K H η Φ X = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm hne'
  · exact h3

/-- A singular matrix is fixed by an element of the principal level `m > 0` with any
prescribed determinant in the principal units of level `m`. The element is the
rank-one perturbation `1 + (u - 1) x₀ e_iᵀ` of the identity along a normalized
kernel vector `x₀` with `x₀ i = 1`. -/
theorem exists_principalLevel_fix_of_det_eq_zero {m : ℕ} (hm : 0 < m) (u : F.Carrierˣ)
    (hu : u ∈ F.canonicalTopologicalData.principalUnits m)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) (hX : X.det = 0) :
    ∃ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
      X * k.val = X ∧ Matrix.GeneralLinearGroup.det k = u := by
  classical
  obtain ⟨z, hz0, hXz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hX
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => F.canonicalTopologicalData.discreteValuation (z j))
  have hzi : z i ≠ 0 := by
    intro h0
    apply hz0
    funext j
    have hj := hi j
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at hj
    exact hj
  set x0 : Fin (n + 1) → F.Carrier := (z i)⁻¹ • z with hx0def
  set w : Fin (n + 1) → F.Carrier := ((u : F.Carrier) - 1) • x0 with hwdef
  set e : Fin (n + 1) → F.Carrier := Pi.single i 1 with hedef
  set Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier :=
    1 + Matrix.replicateCol Unit w * Matrix.replicateRow Unit e with hYdef
  have hu1 : (u : F.Carrier) - 1 ∈ UnequalRankMirabolicUnitTest.levelSet F.Carrier m := by
    rw [RankOneBox.levelSet_eq_additiveLattice F m]
    exact hu.2
  have hx0 : ∀ j, x0 j ∈ (ValuativeRel.valuation F.Carrier).integer := by
    intro j
    apply (F.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one _).2
    simp only [x0, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have hvi : F.canonicalTopologicalData.discreteValuation (z i) ≠ 0 :=
      (map_ne_zero _).mpr hzi
    rw [inv_mul_le_iff₀ (zero_lt_iff.mpr hvi), mul_one]
    exact hi j
  have he : ∀ l, e l ∈ (ValuativeRel.valuation F.Carrier).integer := by
    intro l
    by_cases hl : l = i
    · subst hl
      simp only [e, Pi.single_eq_same]
      exact Subring.one_mem _
    · simp only [e, Pi.single_eq_of_ne hl]
      exact Subring.zero_mem _
  have hY : ∀ j l, Y j l - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) j l ∈
      UnequalRankMirabolicUnitTest.levelSet F.Carrier m := by
    intro j l
    have hYjl : Y j l - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) j l =
        ((u : F.Carrier) - 1) * x0 j * e l := by
      simp [Y, w, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
      ring
    rw [hYjl]
    exact UnequalRankMirabolicUnitTest.mul_mem_levelSet
      (UnequalRankMirabolicUnitTest.mul_mem_levelSet hu1 (hx0 j)) (he l)
  obtain ⟨E, hE, hEY⟩ := UnequalRankMirabolicUnitTest.exists_mem_principalLevelSubgroup hm Y hY
  refine ⟨E, hE, ?_, ?_⟩
  · rw [hEY]
    have hXw : X.mulVec w = 0 := by
      simp [w, x0, Matrix.mulVec_smul, hXz]
    rw [hYdef, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.replicateCol_mulVec,
      hXw, Matrix.replicateCol_zero, Matrix.zero_mul, add_zero]
  · ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    change (E : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier).det = (u : F.Carrier)
    rw [hEY, hYdef, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [e, w, x0, hzi]

/-- With a nontrivial twist on the principal units of level `m > 0`, the average over
the principal level `m` vanishes on every singular matrix. -/
theorem averagedTest_mem_regularMatrixTests {m : ℕ} (hm : 0 < m)
    (H : Subgroup (Conductor.principalLevelSubgroup F.Carrier n m))
    [Finite (Conductor.principalLevelSubgroup F.Carrier n m ⧸ H)] (η : F.Carrierˣ →* ℂˣ)
    (Φ : MatrixTestFunction n F.Carrier)
    (hηH : ∀ k ∈ H, η (Matrix.GeneralLinearGroup.det
      ((k : Conductor.principalLevelSubgroup F.Carrier n m) :
        Langlands.GeneralLinear (n + 1) F.Carrier)) = 1)
    (hΦH : ∀ k ∈ H, ∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier,
      Φ (Y * ((k : Conductor.principalLevelSubgroup F.Carrier n m) :
        Langlands.GeneralLinear (n + 1) F.Carrier).val) = Φ Y)
    (u : F.Carrierˣ) (hu : u ∈ F.canonicalTopologicalData.principalUnits m) (hηu : η u ≠ 1) :
    averagedTest F (Conductor.principalLevelSubgroup F.Carrier n m) H η Φ ∈
      regularMatrixTests (K := F.Carrier) (n + 1) := by
  intro A hA
  have hdet : A.det = 0 := by
    by_contra h
    exact hA ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h))
  obtain ⟨k, hk, hfix, hkdet⟩ := exists_principalLevel_fix_of_det_eq_zero F hm u hu A hdet
  exact averagedTest_eq_zero_of_fix F _ H η Φ hηH hΦH A ⟨k, hk⟩ hfix (by simpa [hkdet] using hηu)

local notation "abvF" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "μF" => generalLinearHaar F.Carrier

/-- For a right `(K, η ∘ det)`-equivariant function, the integral against the
average is the index times the original integral. -/
theorem matrixIntegral_averagedTest (K : Subgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (H : Subgroup K) [Finite (K ⧸ H)] (η : F.Carrierˣ →* ℂˣ)
    (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hf : ∀ g, ∀ k ∈ K, f (g * k) = ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * f g)
    (hconv : ∀ k ∈ K, MatrixConverges abvF (μF n) (rectangularTranslate k Φ) s f) :
    matrixIntegral abvF (μF n) (averagedTest F K H η Φ) s f =
      (Nat.card (K ⧸ H) : ℂ) * matrixIntegral abvF (μF n) Φ s f := by
  let := Fintype.ofFinite (K ⧸ H)
  have htrans : ∀ k ∈ K, matrixIntegral abvF (μF n) (rectangularTranslate k Φ) s f =
      ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)⁻¹ * matrixIntegral abvF (μF n) Φ s f := by
    intro k hk
    rw [matrixIntegral_translate_of_norm_one abvF (μF n) k
      (TwoBlock.normalizedAbs_det_eq_one_of_mem F K hK hk) Φ s f]
    have hfun : (fun h => f (h * k⁻¹)) =
        ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)⁻¹ • f := by
      funext h
      have h1 := hf (h * k⁻¹) k hk
      rw [inv_mul_cancel_right] at h1
      rw [Pi.smul_apply, smul_eq_mul, h1, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
    rw [hfun, matrixIntegral_smul]
  have hint : (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      matrixIntegrand abvF (averagedTest F K H η Φ) s f g) =
      fun g => ∑ c : K ⧸ H, ((η (Matrix.GeneralLinearGroup.det
        (c.out : Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂˣ) : ℂ) *
        matrixIntegrand abvF (rectangularTranslate (c.out : Langlands.GeneralLinear (n + 1) F.Carrier) Φ)
          s f g := by
    funext g
    simp only [matrixIntegrand]
    rw [averagedTest_apply]
    simp only [cosetSum, Finset.sum_mul, rectangularTranslate_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  unfold matrixIntegral
  rw [hint, integral_finsetSum _ fun c _ => ((hconv _ c.out.2).const_mul _)]
  have hterm : ∀ c : K ⧸ H, ∫ g, ((η (Matrix.GeneralLinearGroup.det
        (c.out : Langlands.GeneralLinear (n + 1) F.Carrier)) : ℂˣ) : ℂ) *
        matrixIntegrand abvF (rectangularTranslate (c.out : Langlands.GeneralLinear (n + 1) F.Carrier) Φ)
          s f g ∂(μF n) = ∫ g, matrixIntegrand abvF Φ s f g ∂(μF n) := by
    intro c
    rw [integral_const_mul]
    change _ * matrixIntegral abvF (μF n) _ s f = matrixIntegral abvF (μF n) Φ s f
    rw [htrans _ c.out.2, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- The principal level is compact in the general linear group. -/
theorem isCompact_principalLevelSubgroup (m : ℕ) :
    IsCompact (Conductor.principalLevelSubgroup F.Carrier n m :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
  Conductor.isCompact_principalLevelOpenSubgroup F.Carrier n m

/-- **Laurent integrals of ramified equivariant functions.** Let `f` be continuous with
`f (g k) = η(det k) f g` on the principal level `m > 0`, where `η` is trivial on
the determinants of some open subgroup and nontrivial on the principal units of
level `m`. For every test `Φ` there is one Laurent polynomial giving the shifted
integral at every parameter where the translates of `Φ` by the level converge. -/
theorem exists_laurent_matrixIntegral_of_equivariant {m : ℕ} (hm : 0 < m)
    (η : F.Carrierˣ →* ℂˣ) (u : F.Carrierˣ)
    (hu : u ∈ F.canonicalTopologicalData.principalUnits m) (hηu : η u ≠ 1)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : ∀ k ∈ L, η (Matrix.GeneralLinearGroup.det k) = 1)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hfc : Continuous f)
    (hf : ∀ g, ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
      f (g * k) = ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * f g)
    (Φ : MatrixTestFunction n F.Carrier) :
    ∃ A : LaurentCoefficients, ∀ s : ℂ,
      (∀ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
        MatrixConverges abvF (μF n) (rectangularTranslate k Φ) (s + jpssShift n) f) →
      matrixIntegral abvF (μF n) Φ (s + jpssShift n) f =
        laurentEval (spectralUnit (Nat.zero_lt_one.trans
          F.canonicalTopologicalData.residueCardinality_gt_one) s) A := by
  let K := Conductor.principalLevelSubgroup F.Carrier n m
  have hUΦ : ∀ᶠ k in nhds (1 : Langlands.GeneralLinear (n + 1) F.Carrier),
      ∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier, Φ (Y * k.val) = Φ Y := by
    have ht : Filter.Tendsto (fun k : Langlands.GeneralLinear (n + 1) F.Carrier =>
        ((1 : Langlands.GeneralLinear (n + 1) F.Carrier), k)) (nhds 1) (nhds (1, 1)) :=
      (continuous_const.prodMk continuous_id).tendsto 1
    filter_upwards [ht.eventually (eventually_matrixTranslate_eq Φ)] with k hk Y
    simpa using hk Y
  have hKo : IsOpen (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    (Conductor.principalLevelOpenSubgroup F.Carrier n m).isOpen
  have hnhds : {k : Langlands.GeneralLinear (n + 1) F.Carrier |
      ∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier, Φ (Y * k.val) = Φ Y} ∩
      ((L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∩ K) ∈ nhds 1 :=
    Filter.inter_mem hUΦ (Filter.inter_mem (L.isOpen.mem_nhds L.one_mem)
      (hKo.mem_nhds K.one_mem))
  obtain ⟨a, -, ha⟩ := Conductor.exists_pos_principalLevelOpenSubgroup_subset F.Carrier n hnhds
  let H : Subgroup K := (Conductor.principalLevelSubgroup F.Carrier n a).subgroupOf K
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_principalLevelSubgroup F m)
  have hHo : IsOpen (H : Set K) :=
    (Conductor.principalLevelOpenSubgroup F.Carrier n a).isOpen.preimage continuous_subtype_val
  have : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  have hmemH : ∀ k ∈ H, ((k : K) : Langlands.GeneralLinear (n + 1) F.Carrier) ∈
      {k : Langlands.GeneralLinear (n + 1) F.Carrier |
        ∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier, Φ (Y * k.val) = Φ Y} ∩
      ((L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∩ K) :=
    fun k hk => ha (Subgroup.mem_subgroupOf.mp hk)
  have hηH : ∀ k ∈ H, η (Matrix.GeneralLinearGroup.det
      ((k : K) : Langlands.GeneralLinear (n + 1) F.Carrier)) = 1 :=
    fun k hk => hL _ (hmemH k hk).2.1
  have hΦH : ∀ k ∈ H, ∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier,
      Φ (Y * ((k : K) : Langlands.GeneralLinear (n + 1) F.Carrier).val) = Φ Y :=
    fun k hk => (hmemH k hk).1
  have hreg := averagedTest_mem_regularMatrixTests F hm H η Φ hηH hΦH u hu hηu
  have hc : HasCompactSupport (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      averagedTest F K H η Φ g.val * f g) :=
    (hasCompactSupport_restrict_of_mem_regularMatrixTests (n + 1) hreg).mul_right
  obtain ⟨A, hA⟩ := Padic.exists_laurent_matrixIntegral_of_hasCompactSupport F
    (averagedTest F K H η Φ) f hfc hc
  refine ⟨((Nat.card (K ⧸ H) : ℂ))⁻¹ • A, fun s hconv => ?_⟩
  have hcard : (Nat.card (K ⧸ H) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have h := matrixIntegral_averagedTest F K (isCompact_principalLevelSubgroup F m) H η Φ
    (s + jpssShift n) f hf hconv
  rw [laurentEval_smul, ← (hA s).2]
  change _ = _ * matrixIntegral abvF (μF n) (averagedTest F K H η Φ) (s + jpssShift n) f
  rw [h, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- Right translation of the coefficient moves to the test, with a determinant weight. -/
theorem matrixIntegral_comp_mul_right (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (h : Langlands.GeneralLinear (n + 1) F.Carrier) :
    matrixIntegral abvF (μF n) Φ s (fun g => f (g * h)) =
      determinantWeight abvF h⁻¹ s *
        matrixIntegral abvF (μF n) (rectangularTranslate h⁻¹ Φ) s f := by
  unfold matrixIntegral
  rw [← integral_const_mul,
    ← integral_mul_right_eq_self (fun g => matrixIntegrand abvF Φ s (fun g => f (g * h)) g) h⁻¹]
  congr 1
  funext g
  simp only [matrixIntegrand, rectangularTranslate_apply, Units.val_mul, inv_mul_cancel_right,
    determinantWeight_mul]
  ring

local notation "qPos" => Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one

/-- Every test gives a shifted integral equal to one Laurent polynomial on the
half-plane `a < Re s`. -/
def LaurentOnRight (a : ℝ) (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) : Prop :=
  ∀ Φ : MatrixTestFunction n F.Carrier, ∃ A : LaurentCoefficients, ∀ s : ℂ, a < s.re →
    matrixIntegral abvF (μF n) Φ (s + jpssShift n) f = laurentEval (spectralUnit qPos s) A

theorem LaurentOnRight.comp_mul_right {a : ℝ} {f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ}
    (hf : LaurentOnRight F a f) (h : Langlands.GeneralLinear (n + 1) F.Carrier) :
    LaurentOnRight F a (fun g => f (g * h)) := by
  intro Φ
  obtain ⟨A, hA⟩ := hf (rectangularTranslate h⁻¹ Φ)
  refine ⟨LaurentPolynomial.C (determinantWeight abvF h⁻¹ (jpssShift n)) *
    LaurentPolynomial.T (F.canonicalTopologicalData.ord (Matrix.det (h⁻¹).val)) * A,
    fun s hs => ?_⟩
  rw [matrixIntegral_comp_mul_right, hA s hs, Padic.determinantWeight_shift_spectral, map_mul,
    map_mul, laurentEval_C, laurentEval_T, coe_spectralUnit]

/-- Laurent values on a common half-plane extend from a set to its span when every
function of the span converges there. -/
theorem laurentOnRight_span {a : ℝ} (S : Set (Langlands.GeneralLinear (n + 1) F.Carrier → ℂ))
    (hconv : ∀ f ∈ Submodule.span ℂ S, ∀ (Φ : MatrixTestFunction n F.Carrier) (s : ℂ),
      a < s.re → MatrixConverges abvF (μF n) Φ (s + jpssShift n) f)
    (hS : ∀ f ∈ S, LaurentOnRight F a f) :
    ∀ f ∈ Submodule.span ℂ S, LaurentOnRight F a f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hS f hf
  | zero =>
    intro Φ
    refine ⟨0, fun s _ => ?_⟩
    simp [matrixIntegral, matrixIntegrand]
  | add f g hf hg hLf hLg =>
    intro Φ
    obtain ⟨A, hA⟩ := hLf Φ
    obtain ⟨B, hB⟩ := hLg Φ
    refine ⟨A + B, fun s hs => ?_⟩
    rw [matrixIntegral_add (hconv f hf Φ s hs) (hconv g hg Φ s hs), hA s hs, hB s hs, map_add]
  | smul c f hf hLf =>
    intro Φ
    obtain ⟨A, hA⟩ := hLf Φ
    refine ⟨c • A, fun s hs => ?_⟩
    rw [matrixIntegral_smul, hA s hs, laurentEval_smul]

/-- Laurent values for the span of right translates of one ramified equivariant
function. -/
theorem laurentOnRight_of_translates {m : ℕ} (hm : 0 < m) {a : ℝ}
    (η : F.Carrierˣ →* ℂˣ) (u : F.Carrierˣ)
    (hu : u ∈ F.canonicalTopologicalData.principalUnits m) (hηu : η u ≠ 1)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hL : ∀ k ∈ L, η (Matrix.GeneralLinearGroup.det k) = 1)
    (f₀ : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hf₀c : Continuous f₀)
    (hf₀ : ∀ g, ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
      f₀ (g * k) = ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) * f₀ g)
    (S : Set (Langlands.GeneralLinear (n + 1) F.Carrier → ℂ))
    (hS : ∀ f ∈ S, ∃ h, f = fun g => f₀ (g * h)) (hf₀S : f₀ ∈ Submodule.span ℂ S)
    (hconv : ∀ f ∈ Submodule.span ℂ S, ∀ (Φ : MatrixTestFunction n F.Carrier) (s : ℂ),
      a < s.re → MatrixConverges abvF (μF n) Φ (s + jpssShift n) f) :
    ∀ f ∈ Submodule.span ℂ S, LaurentOnRight F a f := by
  have h₀ : LaurentOnRight F a f₀ := by
    intro Φ
    obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_of_equivariant F hm η u hu hηu L hL
      f₀ hf₀c hf₀ Φ
    exact ⟨A, fun s hs => hA s fun k _ => hconv f₀ hf₀S _ s hs⟩
  apply laurentOnRight_span F S hconv
  intro f hf
  obtain ⟨h, rfl⟩ := hS f hf
  exact h₀.comp_mul_right F h

/-- Every rational value of a function with Laurent values on a half-plane is Laurent. -/
theorem laurent_of_hasShiftedRationalValue {a : ℝ}
    {f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ} (hf : LaurentOnRight F a f)
    (Φ : MatrixTestFunction n F.Carrier) (R : RationalFunctions)
    (hR : HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality abvF (μF n)
      Φ f R) :
    ∃ A : LaurentCoefficients, laurentToRatFunc A = R := by
  obtain ⟨A, hA⟩ := hf Φ
  refine ⟨A, HasRationalContinuation.unique F.canonicalTopologicalData.residueCardinality_gt_one
    ⟨a, fun s hs => ?_⟩ hR.2⟩
  obtain ⟨hd, he⟩ := laurentToRatFunc_regular_and_eval (spectralUnit qPos s) A
  exact ⟨hd, (hA s hs).trans he.symm⟩

/-- Inverse transpose of functions on the group, as a linear map. -/
def coefficientIotaLinear :
    (Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) →ₗ[ℂ]
      (Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) where
  toFun := coefficientIota
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A nonzero vector on which the principal level `m` acts through `η ∘ det`
yields an open subgroup on which `η ∘ det` is trivial. -/
theorem exists_openSubgroup_twist_trivial
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) (hρs : IsSmooth ρ)
    (η : F.Carrierˣ →* ℂˣ) (m : ℕ) {w : V} (hw0 : w ≠ 0)
    (hw : ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
      ρ k w = ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • w) :
    ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
      ∀ k ∈ L, η (Matrix.GeneralLinearGroup.det k) = 1 := by
  obtain ⟨Kw, hKw⟩ := hρs w
  refine ⟨Kw ⊓ Conductor.principalLevelOpenSubgroup F.Carrier n m, fun k hk => ?_⟩
  have h1 : ρ k w = w := hKw ⟨k, hk.1⟩
  have h2 := hw k hk.2
  rw [h1] at h2
  have h3 : (((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) - 1) • w = 0 := by
    rw [sub_smul, one_smul, ← h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact Units.ext (sub_eq_zero.mp h4)
  · exact absurd h4 hw0

/-- **L-vanishing on the original side.** Under a common convergence half-plane, every
actual bi-smooth coefficient of an irreducible smooth representation with a nonzero
ramified `(K_m, η ∘ det)`-eigenvector has Laurent shifted integrals there. -/
theorem laurentOnRight_biSmooth_of_eigenvector
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) (hρs : IsSmooth ρ)
    (hirr : Representation.IsIrreducible ρ) (η : F.Carrierˣ →* ℂˣ) {m : ℕ} (hm : 0 < m)
    (u : F.Carrierˣ) (hu : u ∈ F.canonicalTopologicalData.principalUnits m) (hηu : η u ≠ 1)
    {w : V} (hw0 : w ≠ 0)
    (hw : ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
      ρ k w = ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • w)
    {a : ℝ} (hconv : ∀ (Φ : MatrixTestFunction n F.Carrier) (f : biSmoothMatrixCoefficients ρ)
      (s : ℂ), a < s.re → MatrixConverges abvF (μF n) Φ (s + jpssShift n) f.val) :
    ∀ f ∈ biSmoothMatrixCoefficients ρ, LaurentOnRight F a f := by
  obtain ⟨L, hL⟩ := exists_openSubgroup_twist_trivial F ρ hρs η m hw0 hw
  apply laurentOnRight_span F _ (fun f hf Φ s hs => hconv Φ ⟨f, hf⟩ s hs)
  rintro _ ⟨ℓ, v, rfl⟩
  let C := matrixCoefficient ρ (smoothDualPairing ρ ℓ)
  let S : Set (Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) := Set.range fun h => C (ρ h w)
  have hSsub : Submodule.span ℂ S ≤ biSmoothMatrixCoefficients ρ := by
    rw [Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨ℓ, ⟨ρ h w, hρs _⟩, rfl⟩
  have hmem : biSmoothCoefficient ρ ℓ v ∈ Submodule.span ℂ S := by
    have hv : v.val ∈ Submodule.span ℂ (Set.range fun h => ρ h w) := by
      rw [span_range_orbit_eq_top hirr hw0]
      exact Submodule.mem_top
    have := Submodule.mem_map_of_mem (f := C) hv
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  refine laurentOnRight_of_translates F hm η u hu hηu L hL (C w) ?_ ?_ S ?_ ?_
    (fun f hf Φ s hs => hconv Φ ⟨f, hSsub hf⟩ s hs) _ hmem
  · exact continuous_of_mem_biSmoothMatrixCoefficients ρ _
      (Submodule.subset_span ⟨ℓ, ⟨w, hρs _⟩, rfl⟩)
  · intro g k hk
    change smoothDualPairing ρ ℓ (ρ (g * k) w) = _ * smoothDualPairing ρ ℓ (ρ g w)
    rw [map_mul, Module.End.mul_apply, hw k hk, map_smul, map_smul, smul_eq_mul]
  · rintro _ ⟨h, rfl⟩
    refine ⟨h, funext fun g => ?_⟩
    change smoothDualPairing ρ ℓ (ρ g (ρ h w)) = smoothDualPairing ρ ℓ (ρ (g * h) w)
    rw [map_mul, Module.End.mul_apply]
  · exact Submodule.subset_span ⟨1, by simp [C]⟩

theorem det_inverseTranspose (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    Matrix.GeneralLinearGroup.det (GeneralLinear.inverseTranspose (n + 1) F.Carrier g) =
      (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  apply Units.ext
  change Matrix.det ((g⁻¹).val.transpose) = _
  rw [Matrix.det_transpose]
  exact congrArg Units.val (map_inv Matrix.GeneralLinearGroup.det g)

/-- **L-vanishing on the inverse-transpose side.** The inverse transposes of the
bi-smooth coefficients have Laurent shifted integrals on a common convergence
half-plane; they are equivariant for the inverse twist. -/
theorem laurentOnRight_iota_biSmooth_of_eigenvector
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) (hρs : IsSmooth ρ)
    (hirr : Representation.IsIrreducible ρ) (η : F.Carrierˣ →* ℂˣ) {m : ℕ} (hm : 0 < m)
    (u : F.Carrierˣ) (hu : u ∈ F.canonicalTopologicalData.principalUnits m) (hηu : η u ≠ 1)
    {w : V} (hw0 : w ≠ 0)
    (hw : ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
      ρ k w = ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • w)
    {a : ℝ} (hconv : ∀ (Φ : MatrixTestFunction n F.Carrier) (f : biSmoothMatrixCoefficients ρ)
      (s : ℂ), a < s.re → MatrixConverges abvF (μF n) Φ (s + jpssShift n)
        (coefficientIota f.val)) :
    ∀ f ∈ biSmoothMatrixCoefficients ρ, LaurentOnRight F a (coefficientIota f) := by
  obtain ⟨L, hL⟩ := exists_openSubgroup_twist_trivial F ρ hρs η m hw0 hw
  let ι := coefficientIotaLinear F (n := n)
  let Gen : Set (Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) :=
    {f | ∃ (ℓ : SmoothDual ρ) (v : smoothVectors ρ), biSmoothCoefficient ρ ℓ v = f}
  have hconv' : ∀ f ∈ Submodule.span ℂ (ι '' Gen), ∀ (Φ : MatrixTestFunction n F.Carrier) (s : ℂ),
      a < s.re → MatrixConverges abvF (μF n) Φ (s + jpssShift n) f := by
    intro f hf Φ s hs
    rw [Submodule.span_image] at hf
    obtain ⟨f', hf', rfl⟩ := hf
    exact hconv Φ ⟨f', hf'⟩ s hs
  intro f hf
  have hιf : coefficientIota f ∈ Submodule.span ℂ (ι '' Gen) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map_of_mem hf
  refine laurentOnRight_span F (ι '' Gen) hconv' ?_ _ hιf
  rintro _ ⟨_, ⟨ℓ, v, rfl⟩, rfl⟩
  let C := matrixCoefficient ρ (smoothDualPairing ρ ℓ)
  let S : Set (Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) := Set.range fun h => ι (C (ρ h w))
  have hSsub : ∀ f ∈ Submodule.span ℂ S, ∀ (Φ : MatrixTestFunction n F.Carrier) (s : ℂ),
      a < s.re → MatrixConverges abvF (μF n) Φ (s + jpssShift n) f := by
    intro f hf Φ s hs
    have hle : Submodule.span ℂ (Set.range fun h => C (ρ h w)) ≤ biSmoothMatrixCoefficients ρ := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨ℓ, ⟨ρ h w, hρs _⟩, rfl⟩
    have hS : S = ι '' Set.range fun h => C (ρ h w) := by
      rw [← Set.range_comp]
      rfl
    rw [hS, Submodule.span_image] at hf
    obtain ⟨f', hf', rfl⟩ := hf
    exact hconv Φ ⟨f', hle hf'⟩ s hs
  have hmem : ι (biSmoothCoefficient ρ ℓ v) ∈ Submodule.span ℂ S := by
    have hv : v.val ∈ Submodule.span ℂ (Set.range fun h => ρ h w) := by
      rw [span_range_orbit_eq_top hirr hw0]
      exact Submodule.mem_top
    have := Submodule.mem_map_of_mem (f := ι ∘ₗ C) hv
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  have hηu' : η⁻¹ u ≠ 1 := by
    rw [MonoidHom.inv_apply, inv_ne_one]
    exact hηu
  refine laurentOnRight_of_translates F hm η⁻¹ u hu hηu' L ?_ (ι (C w)) ?_ ?_ S ?_ ?_ hSsub _ hmem
  · intro k hk
    rw [MonoidHom.inv_apply, hL k hk, inv_one]
  · exact (continuous_of_mem_biSmoothMatrixCoefficients ρ _
      (Submodule.subset_span ⟨ℓ, ⟨w, hρs _⟩, rfl⟩)).comp
      (GeneralLinear.continuous_inverseTranspose (n + 1) F.Carrier)
  · intro g k hk
    have hk' := Conductor.inverseTranspose_mem_principalLevelSubgroup F.Carrier n m hk
    change smoothDualPairing ρ ℓ (ρ (GeneralLinear.inverseTranspose (n + 1) F.Carrier (g * k)) w) =
      _ * smoothDualPairing ρ ℓ (ρ (GeneralLinear.inverseTranspose (n + 1) F.Carrier g) w)
    rw [map_mul, map_mul, Module.End.mul_apply, hw _ hk', map_smul, map_smul, smul_eq_mul,
      det_inverseTranspose, MonoidHom.inv_apply, map_inv]
  · rintro _ ⟨h, rfl⟩
    refine ⟨GeneralLinear.inverseTranspose (n + 1) F.Carrier h, funext fun g => ?_⟩
    change smoothDualPairing ρ ℓ (ρ (GeneralLinear.inverseTranspose (n + 1) F.Carrier g) (ρ h w)) =
      smoothDualPairing ρ ℓ (ρ (GeneralLinear.inverseTranspose (n + 1) F.Carrier
        (g * GeneralLinear.inverseTranspose (n + 1) F.Carrier h)) w)
    rw [map_mul, GeneralLinear.inverseTranspose_involutive, map_mul, Module.End.mul_apply]
  · exact Submodule.subset_span ⟨1, by simp [C]⟩

/-- **Godement–Jacquet L-vanishing from a ramified eigenvector.** Let `ρ` be an
irreducible smooth representation of `GL_(n+1)(F)` with a nonzero vector on which
the principal level `m > 0` acts through `η ∘ det`, where `η` is nontrivial on the
principal units of level `m`. Then both polynomials of any normalized matrix
functional-equation data for `ρ` equal `1`. -/
theorem eq_one_of_normalizedMatrixFunctionalEquationData
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) (hρs : IsSmooth ρ)
    (hirr : Representation.IsIrreducible ρ) (η : F.Carrierˣ →* ℂˣ) {m : ℕ} (hm : 0 < m)
    (u : F.Carrierˣ) (hu : u ∈ F.canonicalTopologicalData.principalUnits m) (hηu : η u ≠ 1)
    {w : V} (hw0 : w ≠ 0)
    (hw : ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
      ρ k w = ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • w)
    {P PDual : Polynomial ℂ} {c : ℂˣ} {e : ℤ}
    (hdata : Padic.NormalizedMatrixFunctionalEquationData F ψ ν ρ P PDual c e) :
    P = 1 ∧ PDual = 1 := by
  obtain ⟨⟨⟨a, hconv⟩, -, hgen⟩, ⟨⟨b, hconvι⟩, -, hgenι⟩, -⟩ := hdata
  constructor
  · apply normalizedGenerator_eq_one_of_laurent hgen
    rintro R ⟨Φ, f, hR⟩
    exact laurent_of_hasShiftedRationalValue F
      (laurentOnRight_biSmooth_of_eigenvector F ρ hρs hirr η hm u hu hηu hw0 hw
        (fun Φ f s hs => hconv Φ f s hs) f.val f.2) Φ R hR
  · apply normalizedGenerator_eq_one_of_laurent hgenι
    rintro R ⟨Φ, f, hR⟩
    exact laurent_of_hasShiftedRationalValue F
      (laurentOnRight_iota_biSmooth_of_eigenvector F ρ hρs hirr η hm u hu hηu hw0 hw
        (fun Φ f s hs => hconvι Φ f s hs) f.val f.2) Φ R hR

/-- **Pair L-vanishing from a ramified eigenvector.** Let `τ` be irreducible of full
Whittaker type for `ψ₀`, with a nonzero vector on which the principal level `m > 0`
acts through `η ∘ det` for `η` nontrivial on the principal units of level `m`.
Then `L(s, τ × 1) = 1` for every self-dual Haar measure. -/
theorem isPadicSymmetricLPolynomial_one_of_eigenvector
    (ψ₀ : UnitaryAdditiveCharacter F.Carrier)
    (ν₀ : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ₀)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType n (Whittaker.standardCharacter ψ₀ n) τ)
    (hirr : Representation.IsIrreducible τ) (η : F.Carrierˣ →* ℂˣ) {m : ℕ} (hm : 0 < m)
    (u : F.Carrierˣ) (hu : u ∈ F.canonicalTopologicalData.principalUnits m) (hηu : η u ≠ 1)
    {w : V} (hw0 : w ≠ 0)
    (hw : ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
      τ k w = ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • w) :
    IsPadicSymmetricLPolynomial F ψ₀ ν₀.val τ (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) 1 := by
  obtain ⟨P', hP', hgen'⟩ :=
    GodementJacquet.Padic.exists_modelMatrixNormalizedGenerator F ψ₀ τ ν₀ hτ
  obtain ⟨e₀⟩ := hτ.2.2
  let ℓ : Whittaker.glFunctionals ψ₀ n τ := e₀.symm 1
  have hℓ : ℓ.val ≠ 0 := by
    intro h
    have h0 : ℓ = 0 := Subtype.ext h
    have h1 : e₀ ℓ = 1 := e₀.apply_symm_apply 1
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  let : Representation.IsIrreducible τ := hirr
  let e := Whittaker.modelEquiv τ ℓ hℓ
  have hρirr : Representation.IsIrreducible (Whittaker.glModelRepresentation ψ₀ n τ ℓ) :=
    (isIrreducible_iff_of_equiv (W := (Whittaker.glCoefficientModel ψ₀ n τ ℓ).toSubmodule) e).mp hirr
  have hρ : IsOfWhittakerType (V := (Whittaker.glCoefficientModel ψ₀ n τ ℓ).toSubmodule) n
      (Whittaker.standardCharacter ψ₀ n) (Whittaker.glModelRepresentation ψ₀ n τ ℓ) :=
    hτ.of_equiv e
  obtain ⟨P, PDual, c, a, hdata⟩ := genericMatrixFunctionalEquation.{uF, uF} p F ψ₀ ν₀.val ν₀.2 n
    (Whittaker.glCoefficientModel ψ₀ n τ ℓ).toSubmodule (Whittaker.glModelRepresentation ψ₀ n τ ℓ)
    hρ hρirr
  have hew0 : Whittaker.modelMap τ ℓ w ≠ 0 := by
    intro h
    apply hw0
    have h' : e w = e 0 := by
      rw [map_zero]
      exact h
    exact EquivLike.injective e h'
  have hew : ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier n m,
      Whittaker.glModelRepresentation ψ₀ n τ ℓ k (Whittaker.modelMap τ ℓ w) =
        ((η (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • Whittaker.modelMap τ ℓ w := by
    intro k hk
    change Whittaker.modelRepresentation τ ℓ k (Whittaker.modelMap τ ℓ w) = _
    rw [← (Whittaker.modelMap τ ℓ).isIntertwining, hw k hk, map_smul]
  have hP1 := (eq_one_of_normalizedMatrixFunctionalEquationData F ψ₀ ν₀.val _ hρ.1.1 hρirr η hm
    u hu hηu hew0 hew hdata).1
  have hPP : P' = P := (hgen' ℓ hℓ).unique hdata.1.2.2
  rw [hPP, hP1] at hP'
  exact hP'

end Matrix

end Langlands.RankinSelberg.UniformRankOneTwist
