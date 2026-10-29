import Langlands.Analysis.Local.CompactFactorizationIntegral
import Langlands.Representation.RankinSelberg.EqualRankLastRowReductionProof
import Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationStatement
import Langlands.Group.GL.MirabolicAffine
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Analysis.Local.QuotientAverageReal
import Langlands.Analysis.Local.QuotientPositiveLifting
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal

/-!
# Proof of normalized recursive quotient integration

The rank `n + 2` unipotent Haar measure is the transported product of a column Haar
measure and the rank `n + 1` unipotent Haar measure. Haar measure on `GL_(n+2)` is
recovered from parabolic coordinates `(a, g, w)` and the integral subgroup by the
factorization integral. Together with the Weil formula of the lower quotient measure
this gives the recursive identity for nonnegative compactly supported functions; the
measure identity then follows from regularity and Riesz–Markov–Kakutani uniqueness.
-/

noncomputable section

namespace Langlands.RankinSelberg

namespace RecursiveIntegration

open MeasureTheory Measure GeneralLinear GeneralLinear.Mirabolic QuotientIntegration
  LastRowReduction
open scoped CompactlySupported

section Algebra

variable {K : Type*} [Field K] {n : ℕ}

/-- Parabolic coordinates `(a, g, w) ↦ diag(g,1) [[I,w],[0,1]] a` on the standard
parabolic subgroup of type `(n+1, 1)`. -/
def parabolicPoint (x : Kˣ × (GeneralLinear (n + 1) K × (Fin (n + 1) → K))) :
    GeneralLinear (n + 1 + 1) K :=
  rankInclusion 1 x.2.1 * col x.2.2 * GeneralLinear.scalar x.1

/-- Coordinates of `(parabolicPoint x₀)⁻¹ * parabolicPoint x`. -/
def parabolicShift (x₀ x : Kˣ × (GeneralLinear (n + 1) K × (Fin (n + 1) → K))) :
    Kˣ × (GeneralLinear (n + 1) K × (Fin (n + 1) → K)) :=
  (x₀.1⁻¹ * x.1, x₀.2.1⁻¹ * x.2.1, -((x.2.1⁻¹ * x₀.2.1).val.mulVec x₀.2.2) + x.2.2)

theorem scalar_mul_comm (a : Kˣ) (y : GeneralLinear (n + 1 + 1) K) :
    GeneralLinear.scalar a * y = y * GeneralLinear.scalar a :=
  Matrix.GeneralLinearGroup.scalar_commute a y

theorem parabolicPoint_mul_shift (x₀ x : Kˣ × (GeneralLinear (n + 1) K × (Fin (n + 1) → K))) :
    parabolicPoint x₀ * parabolicPoint (parabolicShift x₀ x) = parabolicPoint x := by
  obtain ⟨a₀, g₀, w₀⟩ := x₀
  obtain ⟨a, g, w⟩ := x
  simp only [parabolicPoint, parabolicShift]
  have hcol : col w₀ * rankInclusion 1 (g₀⁻¹ * g) =
      rankInclusion 1 (g₀⁻¹ * g) * col ((g⁻¹ * g₀).val.mulVec w₀) := by
    rw [col_mul_rankInclusion, mul_inv_rev, inv_inv]
  rw [col_add, col_neg, map_mul GeneralLinear.scalar, map_inv]
  calc rankInclusion 1 g₀ * col w₀ * GeneralLinear.scalar a₀ *
        (rankInclusion 1 (g₀⁻¹ * g) * ((col ((g⁻¹ * g₀).val.mulVec w₀))⁻¹ * col w) *
          ((GeneralLinear.scalar a₀)⁻¹ * GeneralLinear.scalar a))
      = rankInclusion 1 g₀ * col w₀ * (GeneralLinear.scalar a₀ *
        (rankInclusion 1 (g₀⁻¹ * g) * ((col ((g⁻¹ * g₀).val.mulVec w₀))⁻¹ * col w) *
          ((GeneralLinear.scalar a₀)⁻¹ * GeneralLinear.scalar a))) := by
        rw [mul_assoc]
    _ = rankInclusion 1 g₀ * col w₀ *
        (rankInclusion 1 (g₀⁻¹ * g) * ((col ((g⁻¹ * g₀).val.mulVec w₀))⁻¹ * col w) *
          (GeneralLinear.scalar a₀ *
            ((GeneralLinear.scalar a₀)⁻¹ * GeneralLinear.scalar a))) := by
        rw [← mul_assoc (GeneralLinear.scalar a₀), scalar_mul_comm]
        simp only [mul_assoc]
    _ = rankInclusion 1 g * col w * GeneralLinear.scalar a := by
        rw [mul_inv_cancel_left]
        simp only [mul_assoc]
        rw [← mul_assoc (col w₀), hcol]
        simp only [mul_assoc, mul_inv_cancel_left]
        rw [← mul_assoc, ← map_mul, mul_inv_cancel_left]

theorem parabolicPoint_shift (x₀ x : Kˣ × (GeneralLinear (n + 1) K × (Fin (n + 1) → K))) :
    parabolicPoint (parabolicShift x₀ x) = (parabolicPoint x₀)⁻¹ * parabolicPoint x := by
  rw [eq_inv_mul_iff_mul_eq, parabolicPoint_mul_shift]

/-- A matrix whose last row is `(0, …, 0, d)` lies in the image of the parabolic
coordinates. -/
theorem exists_parabolicPoint_eq (b : GeneralLinear (n + 1 + 1) K)
    (hb : ∀ j : Fin (n + 1), b (Fin.last (n + 1)) j.castSucc = 0) :
    ∃ x, b = parabolicPoint x := by
  have hd : b (Fin.last (n + 1)) (Fin.last (n + 1)) ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero b
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last (n + 1))
    intro j
    induction j using Fin.lastCases with
    | last => exact h0
    | cast j => exact hb j
  let d : Kˣ := Units.mk0 _ hd
  let m : GeneralLinear (n + 1 + 1) K := b * GeneralLinear.scalar d⁻¹
  have hm : m ∈ mirabolic (n + 1) K := by
    intro j
    change (b.val * Matrix.scalar (Fin (n + 1 + 1)) ((d⁻¹ : Kˣ) : K))
      (Fin.last (n + 1)) j = _
    rw [Matrix.scalar_apply, Matrix.mul_diagonal]
    induction j using Fin.lastCases with
    | last =>
      simp only [ite_true]
      change b (Fin.last (n + 1)) (Fin.last (n + 1)) * ((d⁻¹ : Kˣ) : K) = 1
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ hd]
    | cast j =>
      have hj : j.castSucc ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last j).ne
      simp only [hj, ↓reduceIte]
      change b (Fin.last (n + 1)) j.castSucc * _ = 0
      rw [hb j, zero_mul]
  let mm : mirabolic (n + 1) K := ⟨m, hm⟩
  have hmm := congrArg Subtype.val (eq_radicalElement_mul_levi mm)
  change m = col (lastColumn mm) * rankInclusion 1 (projection mm) at hmm
  refine ⟨(d, projection mm, ((projection mm)⁻¹).val.mulVec (lastColumn mm)), ?_⟩
  simp only [parabolicPoint]
  rw [← col_mul_rankInclusion, ← hmm]
  simp only [m, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

section Integral

variable (O : Subring K)

theorem mulVec_mem {A : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hA : ∀ i j, A i j ∈ O)
    {v : Fin (n + 1) → K} (hv : ∀ i, v i ∈ O) (i : Fin (n + 1)) : A.mulVec v i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => O.mul_mem (hA i j) (hv j)

theorem affineMatrix_entries_mem (A : GeneralLinear (n + 1) K) (v : Fin (n + 1) → K) :
    (∀ i j, (affineMatrix A v).val i j ∈ O) ↔ (∀ i j, A i j ∈ O) ∧ ∀ i, v i ∈ O := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · have := h i.castSucc j.castSucc
      rwa [show (affineMatrix A v).val i.castSucc j.castSucc = A i j from
        affineMatrix_first A v i j] at this
    · have := h i.castSucc (Fin.last (n + 1))
      rwa [show (affineMatrix A v).val i.castSucc (Fin.last (n + 1)) = v i from
        affineMatrix_last A v i] at this
  · rintro ⟨hA, hv⟩ i j
    induction i using Fin.lastCases with
    | last =>
      rw [show (affineMatrix A v).val (Fin.last (n + 1)) j =
          if j = Fin.last (n + 1) then 1 else 0 from affineMatrix_bottom A v j]
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [show (affineMatrix A v).val i.castSucc (Fin.last (n + 1)) = v i from
          affineMatrix_last A v i]
        exact hv i
      | cast j =>
        rw [show (affineMatrix A v).val i.castSucc j.castSucc = A i j from
          affineMatrix_first A v i j]
        exact hA i j

theorem affineMatrix_one_zero : affineMatrix (1 : GeneralLinear (n + 1) K) 0 = 1 := by
  simp [affineMatrix, radicalElement_zero]

theorem affineMatrix_inv (A : GeneralLinear (n + 1) K) (v : Fin (n + 1) → K) :
    (affineMatrix A v)⁻¹ = affineMatrix A⁻¹ (-((A⁻¹).val.mulVec v)) := by
  rw [inv_eq_iff_mul_eq_one, affineMatrix_mul, mul_inv_cancel, Matrix.mulVec_neg,
    Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec,
    add_neg_cancel, affineMatrix_one_zero]

/-- Integral points of the mirabolic group in affine coordinates. -/
theorem col_mul_rankInclusion_mem_iff (A : GeneralLinear (n + 1) K) (v : Fin (n + 1) → K) :
    col v * rankInclusion 1 A ∈ Conductor.integralSubgroup O (n + 1) ↔
      A ∈ Conductor.integralSubgroup O n ∧ ∀ i, v i ∈ O := by
  have hval : col v * rankInclusion 1 A = (affineMatrix A v).val := rfl
  have hinv : (col v * rankInclusion 1 A)⁻¹ =
      (affineMatrix A⁻¹ (-((A⁻¹).val.mulVec v))).val := by
    rw [hval, ← Subgroup.coe_inv, affineMatrix_inv]
  rw [Conductor.mem_integralSubgroup, Conductor.mem_integralSubgroup, hinv, hval,
    affineMatrix_entries_mem, affineMatrix_entries_mem]
  constructor
  · rintro ⟨⟨hA, hv⟩, hAi, -⟩
    exact ⟨⟨hA, hAi⟩, hv⟩
  · rintro ⟨⟨hA, hAi⟩, hv⟩
    refine ⟨⟨hA, hv⟩, hAi, fun i => O.neg_mem (mulVec_mem O hAi hv i)⟩

theorem scalar_mem_integralSubgroup (m : ℕ) {a : Kˣ} (ha : a ∈ integralUnits O) :
    (GeneralLinear.scalar a : GeneralLinear (m + 1) K) ∈ Conductor.integralSubgroup O m := by
  rw [mem_integralUnits] at ha
  rw [Conductor.mem_integralSubgroup]
  constructor
  · intro i j
    change Matrix.scalar (Fin (m + 1)) (a : K) i j ∈ O
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact ha.1
    · exact O.zero_mem
  · intro i j
    rw [← map_inv]
    change Matrix.scalar (Fin (m + 1)) ((a⁻¹ : Kˣ) : K) i j ∈ O
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact ha.2
    · exact O.zero_mem

theorem mul_scalar_mem_iff (m : mirabolic (n + 1) K) (a : Kˣ) :
    m.val * GeneralLinear.scalar a ∈ Conductor.integralSubgroup O (n + 1) ↔
      a ∈ integralUnits O ∧ m.val ∈ Conductor.integralSubgroup O (n + 1) := by
  constructor
  · intro h
    have hlast : ∀ y : mirabolic (n + 1) K, ∀ c : Kˣ,
        (y.val * GeneralLinear.scalar c : GeneralLinear (n + 1 + 1) K)
          (Fin.last (n + 1)) (Fin.last (n + 1)) = c := by
      intro y c
      change (y.val.val * Matrix.scalar (Fin (n + 1 + 1)) (c : K))
        (Fin.last (n + 1)) (Fin.last (n + 1)) = c
      rw [Matrix.scalar_apply, Matrix.mul_diagonal]
      have := y.property (Fin.last (n + 1))
      simp only [ite_true] at this
      rw [this, one_mul]
    have ha : a ∈ integralUnits O := by
      rw [mem_integralUnits]
      rw [Conductor.mem_integralSubgroup] at h
      refine ⟨?_, ?_⟩
      · have := h.1 (Fin.last (n + 1)) (Fin.last (n + 1))
        rwa [hlast m a] at this
      · have := h.2 (Fin.last (n + 1)) (Fin.last (n + 1))
        rwa [mul_inv_rev, ← map_inv, scalar_mul_comm, ← Subgroup.coe_inv, hlast] at this
    refine ⟨ha, ?_⟩
    have hs := scalar_mem_integralSubgroup O (n + 1) (inv_mem ha)
    have := mul_mem h hs
    rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at this
  · rintro ⟨ha, hm⟩
    exact mul_mem hm (scalar_mem_integralSubgroup O (n + 1) ha)

/-- Integral points in parabolic coordinates. -/
theorem parabolicPoint_mem_iff (x : Kˣ × (GeneralLinear (n + 1) K × (Fin (n + 1) → K))) :
    parabolicPoint x ∈ Conductor.integralSubgroup O (n + 1) ↔
      x.1 ∈ integralUnits O ∧ x.2.1 ∈ Conductor.integralSubgroup O n ∧
        ∀ i, x.2.2 i ∈ O := by
  obtain ⟨a, g, w⟩ := x
  have h : parabolicPoint (a, g, w) = (affineMatrix g (g.val.mulVec w)).val *
      GeneralLinear.scalar a := by
    simp only [parabolicPoint, rankInclusion_mul_col]
    rfl
  rw [h, mul_scalar_mem_iff]
  change a ∈ integralUnits O ∧ col (g.val.mulVec w) * rankInclusion 1 g ∈ _ ↔ _
  rw [col_mul_rankInclusion_mem_iff]
  constructor
  · rintro ⟨ha, hg, hw⟩
    refine ⟨ha, hg, fun i => ?_⟩
    have hgi := ((Conductor.mem_integralSubgroup O n g).mp hg).2
    have := mulVec_mem O hgi hw i
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at this
  · rintro ⟨ha, hg, hw⟩
    exact ⟨ha, hg, mulVec_mem O ((Conductor.mem_integralSubgroup O n g).mp hg).1 hw⟩

end Integral

end Algebra

section Topology

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

theorem continuous_parabolicPoint :
    Continuous (parabolicPoint : Kˣ × (GeneralLinear (n + 1) K × (Fin (n + 1) → K)) →
      GeneralLinear (n + 1 + 1) K) :=
  (((rankInclusionContinuous 1).continuous.comp (continuous_fst.comp continuous_snd)).mul
    (continuous_col.comp (continuous_snd.comp continuous_snd))).mul
    (GeneralLinear.scalarContinuous.continuous.comp continuous_fst)

theorem continuous_parabolicShift (x₀ : Kˣ × (GeneralLinear (n + 1) K × (Fin (n + 1) → K))) :
    Continuous (parabolicShift x₀) := by
  unfold parabolicShift
  refine (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul (continuous_fst.comp continuous_snd)).prodMk ?_)
  refine (Continuous.neg ?_).add (continuous_snd.comp continuous_snd)
  exact (Units.continuous_val.comp ((continuous_inv.comp (continuous_fst.comp continuous_snd)).mul
    continuous_const)).matrix_mulVec continuous_const

/-- The shear `(g, w) ↦ (g, g w)`. -/
def shearHomeomorph :
    GeneralLinear (n + 1) K × (Fin (n + 1) → K) ≃ₜ GeneralLinear (n + 1) K × (Fin (n + 1) → K) where
  toFun p := (p.1, p.1.val.mulVec p.2)
  invFun p := (p.1, (p.1⁻¹).val.mulVec p.2)
  left_inv p := by
    refine Prod.ext rfl ?_
    change (p.1⁻¹).val.mulVec (p.1.val.mulVec p.2) = p.2
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv p := by
    refine Prod.ext rfl ?_
    change p.1.val.mulVec ((p.1⁻¹).val.mulVec p.2) = p.2
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  continuous_toFun :=
    continuous_fst.prodMk ((Units.continuous_val.comp continuous_fst).matrix_mulVec continuous_snd)
  continuous_invFun :=
    continuous_fst.prodMk ((Units.continuous_coe_inv.comp continuous_fst).matrix_mulVec
      continuous_snd)

/-- `(g, w) ↦ diag(g,1) [[I,w],[0,1]]` is a closed embedding onto the mirabolic group. -/
theorem isClosedEmbedding_rankInclusion_mul_col [T2Space K] :
    Topology.IsClosedEmbedding (fun p : GeneralLinear (n + 1) K × (Fin (n + 1) → K) =>
      rankInclusion 1 p.1 * col p.2) := by
  have h : (fun p : GeneralLinear (n + 1) K × (Fin (n + 1) → K) =>
      rankInclusion 1 p.1 * col p.2) =
      Subtype.val ∘ (affineHomeomorph (n := n + 1) (F := K)).symm ∘ shearHomeomorph := by
    funext p
    exact rankInclusion_mul_col p.1 p.2
  rw [h]
  exact (Mirabolic.isClosed (n := n + 1) (F := K)).isClosedEmbedding_subtypeVal.comp
    ((affineHomeomorph (n := n + 1) (F := K)).symm.isClosedEmbedding.comp
      shearHomeomorph.isClosedEmbedding)

end Topology

section Support

/-- Integrating out one factor of a compactly supported continuous function on a
product gives a compactly supported continuous function. -/
theorem continuous_hasCompactSupport_integral {X Y : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [FirstCountableTopology X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Y) [IsLocallyFiniteMeasure μ] {Φ : X × Y → ℝ} (hΦ : Continuous Φ)
    (hc : HasCompactSupport Φ) :
    Continuous (fun x => ∫ y, Φ (x, y) ∂μ) ∧ HasCompactSupport (fun x => ∫ y, Φ (x, y) ∂μ) := by
  have hzero : ∀ x y, (x, y) ∉ tsupport Φ → Φ (x, y) = 0 :=
    fun x y h => image_eq_zero_of_notMem_tsupport h
  constructor
  · have hs : IsCompact (Prod.snd '' tsupport Φ) := hc.image continuous_snd
    have heq : (fun x => ∫ y, Φ (x, y) ∂μ) = fun x => ∫ y in Prod.snd '' tsupport Φ, Φ (x, y) ∂μ := by
      funext x
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
      exact hzero x y fun hxy => hy ⟨(x, y), hxy, rfl⟩
    rw [heq]
    exact continuous_parametric_integral_of_continuous (f := fun x y => Φ (x, y))
      (by simpa only [Function.uncurry_def] using hΦ) hs
  · refine HasCompactSupport.intro (hc.image continuous_fst) fun x hx => ?_
    have : (fun y => Φ (x, y)) = fun _ => 0 := by
      funext y
      exact hzero x y fun hxy => hx ⟨(x, y), hxy, rfl⟩
    simp only [this, integral_zero]

end Support

section Weil

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
  [MeasurableSpace H] [MeasurableMul H]
  (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (μH : Measure H) [IsMulRightInvariant μH]
  [MeasurableSpace (LeftQuotient H)]

/-- The Weil formula of a compatible measure, for a nonnegative compactly supported
continuous real function, as an identity of lower Lebesgue integrals. -/
theorem lintegral_quotientAverageReal (ν : Measure (LeftQuotient H))
    (hν : IsCompatible H μG μH ν) (h : G → ℝ) (hc : Continuous h) (hcs : HasCompactSupport h)
    (h0 : ∀ g, 0 ≤ h g) :
    ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH h q) ∂ν = ∫⁻ g, ENNReal.ofReal (h g) ∂μG := by
  have hcc : Continuous fun g => (h g : ℂ) := Complex.continuous_ofReal.comp hc
  have hcs' : HasCompactSupport fun g => (h g : ℂ) := hcs.comp_left Complex.ofReal_zero
  have hav : quotientAverage H μH (fun g => (h g : ℂ)) =
      fun q => (quotientAverageReal H μH h q : ℂ) := funext (quotientAverage_ofReal H μH h)
  have hi := hν.averaging_integrable _ hcc hcs'
  rw [hav] at hi
  have hi' : Integrable (quotientAverageReal H μH h) ν := by
    refine hi.re.congr (Filter.Eventually.of_forall fun q => ?_)
    simp
  have hf := hν.integral_formula _ hcc hcs'
  rw [hav, integral_complex_ofReal, integral_complex_ofReal] at hf
  have hf' := Complex.ofReal_injective hf
  rw [← ofReal_integral_eq_lintegral_ofReal hi'
      (Filter.Eventually.of_forall (quotientAverageReal_nonneg H μH h h0)),
    ← ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hcs)
      (Filter.Eventually.of_forall h0), hf']

end Weil

section Factorization

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) {n : ℕ}

/-- Iwasawa factorization `G = P K` in parabolic coordinates. -/
theorem exists_parabolicPoint_mul (y : GeneralLinear (n + 1 + 1) K) :
    ∃ x₀, ∃ k₀ ∈ Conductor.integralSubgroup v.integer (n + 1), y = parabolicPoint x₀ * k₀ := by
  obtain ⟨b, hb, k, hk, rfl⟩ := Iwasawa.exists_upperTriangular_mul v y
  obtain ⟨x₀, rfl⟩ := exists_parabolicPoint_eq b fun j => hb (Fin.castSucc_lt_last j)
  exact ⟨x₀, k, hk, rfl⟩

end Factorization

section Measure

open scoped NNReal ENNReal

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F] [SecondCountableTopology F]

private instance matrix_locallyCompact (m : ℕ) :
    LocallyCompactSpace (Matrix (Fin m) (Fin m) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → F))

private instance gl_locallyCompact (m : ℕ) : LocallyCompactSpace (GeneralLinear m F) :=
  inferInstance

private instance gl_secondCountable (m : ℕ) : SecondCountableTopology (GeneralLinear m F) := by
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → F))
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private instance unipotent_secondCountable (m : ℕ) :
    SecondCountableTopology (GeneralLinear.upperUnipotent m F) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (GeneralLinear.upperUnipotent m F : Set (GeneralLinear m F))

private instance unipotent_locallyCompact (m : ℕ) :
    LocallyCompactSpace (GeneralLinear.upperUnipotent m F) :=
  UpperUnipotent.locallyCompactSpace

private instance units_secondCountable : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

private instance units_locallyCompact : LocallyCompactSpace Fˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F)).locallyCompactSpace

private instance quotient_secondCountable (m : ℕ) :
    SecondCountableTopology (LeftUnipotentQuotient m F) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap (GeneralLinear.upperUnipotent (m + 1) F))

variable (F) in
/-- The integral column vectors `O^(n+1)`, a compact open subset of `F^(n+1)`. -/
def columnIntegers (n : ℕ) : TopologicalSpace.PositiveCompacts (Fin (n + 1) → F) where
  carrier := Set.univ.pi fun _ => ((ValuativeRel.valuation F).integer : Set F)
  isCompact' := isCompact_univ_pi fun _ =>
    HarmonicAnalysis.GeneralLocalField.isCompact_integer F
  interior_nonempty' := by
    rw [(isOpen_set_pi Set.finite_univ fun _ _ =>
      HarmonicAnalysis.GeneralLocalField.isOpen_integer F).interior_eq]
    exact ⟨0, fun i _ => (ValuativeRel.valuation F).integer.zero_mem⟩

omit [T2Space F] [SecondCountableTopology F] in
@[simp] theorem mem_columnIntegers {n : ℕ} (w : Fin (n + 1) → F) :
    w ∈ columnIntegers F n ↔ ∀ i, w i ∈ (ValuativeRel.valuation F).integer := by
  change w ∈ Set.univ.pi _ ↔ _
  simp

omit [T2Space F] [SecondCountableTopology F] in
theorem isOpen_columnIntegers (n : ℕ) :
    IsOpen (columnIntegers F n : Set (Fin (n + 1) → F)) :=
  isOpen_set_pi Set.finite_univ fun _ _ => HarmonicAnalysis.GeneralLocalField.isOpen_integer F

variable [MeasurableSpace F] [BorelSpace F]

variable (F) in
/-- Additive Haar measure on `F^(n+1)` giving the integral columns mass one. -/
def columnHaar (n : ℕ) : Measure (Fin (n + 1) → F) :=
  Measure.addHaarMeasure (columnIntegers F n)

instance columnHaar_isAddHaar (n : ℕ) : (columnHaar F n).IsAddHaarMeasure := by
  unfold columnHaar
  infer_instance

omit [T2Space F] in
@[simp] theorem columnHaar_integers (n : ℕ) :
    columnHaar F n (columnIntegers F n) = 1 :=
  Measure.addHaarMeasure_self

omit [T2Space F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
theorem mem_levelOpenSubgroup_zero (m : ℕ) (x : GeneralLinear (m + 1) F) :
    x ∈ Conductor.levelOpenSubgroup F m 0 ↔
      x ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer m := by
  change x ∈ Conductor.levelSubgroup F m 0 ↔ _
  rw [Conductor.levelSubgroup_zero]

/-- The transported product measure of `columnHaar` and the rank `n+1` unipotent Haar
measure is exactly the rank `n+2` unipotent Haar measure. -/
theorem coordinateMeasure_columnHaar {n : ℕ} (χ : F →*₀ ℝ≥0)
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, M.det ≠ 0 →
      (columnHaar F n).map (Matrix.toLin' M) = (χ M.det)⁻¹ • columnHaar F n)
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1 + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1 + 1) F)] :
    coordinateMeasure (columnHaar F n) (unipotentHaar F n) = unipotentHaar F (n + 1) := by
  obtain ⟨κ, hκ⟩ := exists_coordinateMeasure_eq_smul χ (columnHaar F n) hdet
    (unipotentHaar F n) (unipotentHaar F (n + 1))
  have hS : MeasurableSet (unipotentIntegralOpen F (n + 1) :
      Set (GeneralLinear.upperUnipotent (n + 1 + 1) F)) :=
    (unipotentIntegralOpen F (n + 1)).isOpen.measurableSet
  have hpre : unipotentCoordinates ⁻¹' (unipotentIntegralOpen F (n + 1) :
        Set (GeneralLinear.upperUnipotent (n + 1 + 1) F)) =
      (columnIntegers F n : Set (Fin (n + 1) → F)) ×ˢ
        (unipotentIntegralOpen F n : Set (GeneralLinear.upperUnipotent (n + 1) F)) := by
    ext ⟨w, u⟩
    simp only [Set.mem_preimage, Set.mem_prod, SetLike.mem_coe]
    change col w * rankInclusion 1 u.val ∈ Conductor.levelOpenSubgroup F (n + 1) 0 ↔
      w ∈ columnIntegers F n ∧ u.val ∈ Conductor.levelOpenSubgroup F n 0
    rw [mem_levelOpenSubgroup_zero, mem_levelOpenSubgroup_zero, col_mul_rankInclusion_mem_iff,
      mem_columnIntegers, and_comm]
  have h1 := congrArg (fun μ => μ (unipotentIntegralOpen F (n + 1) :
    Set (GeneralLinear.upperUnipotent (n + 1 + 1) F))) hκ
  rw [coordinateMeasure, Measure.map_apply measurable_unipotentCoordinates hS, hpre,
    Measure.prod_prod, columnHaar_integers, unipotentHaar_integral, one_mul,
    Measure.smul_apply, unipotentHaar_integral, ENNReal.smul_def, smul_eq_mul, mul_one] at h1
  have hκ1 : κ = 1 := by exact_mod_cast h1.symm
  rw [hκ, hκ1, one_smul]

omit [T2Space F] in
/-- Moving `diag(g,1)` across the column coordinates costs the determinant factor. -/
theorem lintegral_col_mul_rankInclusion {n : ℕ} (χ : F →*₀ ℝ≥0)
    (vol : Measure (Fin (n + 1) → F))
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, M.det ≠ 0 →
      vol.map (Matrix.toLin' M) = (χ M.det)⁻¹ • vol)
    [MeasurableSpace (GeneralLinear (n + 1 + 1) F)] [BorelSpace (GeneralLinear (n + 1 + 1) F)]
    (g : GeneralLinear (n + 1) F) (Φ : GeneralLinear (n + 1 + 1) F → ℝ≥0∞) (hΦ : Measurable Φ) :
    ((χ g.val.det : ℝ≥0∞))⁻¹ * ∫⁻ v, Φ (col v * rankInclusion 1 g) ∂vol =
      ∫⁻ w, Φ (rankInclusion 1 g * col w) ∂vol := by
  have hmeas : Measurable fun w => Φ (rankInclusion 1 g * col w) :=
    hΦ.comp (continuous_const.mul continuous_col).measurable
  have hL : Measurable (Matrix.toLin' (g⁻¹).val) := (LinearMap.continuous_on_pi _).measurable
  have hdet0 : (g⁻¹).val.det ≠ 0 := (Matrix.isUnits_det_units g⁻¹).ne_zero
  have hχ : χ (g⁻¹).val.det = (χ g.val.det)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one, map_one]
  have hne : (χ g.val.det : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    exact (map_ne_zero χ).mpr (Matrix.isUnits_det_units g).ne_zero
  calc ((χ g.val.det : ℝ≥0∞))⁻¹ * ∫⁻ v, Φ (col v * rankInclusion 1 g) ∂vol
      = ((χ g.val.det : ℝ≥0∞))⁻¹ * ∫⁻ v, (fun w => Φ (rankInclusion 1 g * col w))
          (Matrix.toLin' (g⁻¹).val v) ∂vol := by
        congr 1
        apply lintegral_congr
        intro v
        simp only [Matrix.toLin'_apply, col_mul_rankInclusion]
    _ = ((χ g.val.det : ℝ≥0∞))⁻¹ * ∫⁻ w, Φ (rankInclusion 1 g * col w)
          ∂(vol.map (Matrix.toLin' (g⁻¹).val)) := by
        rw [lintegral_map hmeas hL]
    _ = ∫⁻ w, Φ (rankInclusion 1 g * col w) ∂vol := by
        rw [hdet _ hdet0, lintegral_smul_measure, hχ, inv_inv, ENNReal.smul_def, smul_eq_mul,
          ← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top, one_mul]

omit [T2Space F] in
/-- Left translation in parabolic coordinates preserves `dMult × (dg × dw)`. -/
theorem measurePreserving_parabolicShift {n : ℕ} [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    [MeasurableSpace (GeneralLinear (n + 1) F)] [BorelSpace (GeneralLinear (n + 1) F)]
    (dMult : Measure Fˣ) [SFinite dMult] [IsMulLeftInvariant dMult]
    (μG' : Measure (GeneralLinear (n + 1) F)) [SFinite μG'] [IsMulLeftInvariant μG']
    (vol : Measure (Fin (n + 1) → F)) [SFinite vol] [IsAddLeftInvariant vol]
    (x₀ : Fˣ × (GeneralLinear (n + 1) F × (Fin (n + 1) → F))) :
    MeasurePreserving (parabolicShift x₀) (dMult.prod (μG'.prod vol))
      (dMult.prod (μG'.prod vol)) := by
  have h1 : MeasurePreserving (fun a : Fˣ => x₀.1⁻¹ * a) dMult dMult :=
    measurePreserving_mul_left dMult x₀.1⁻¹
  have hgm : Measurable (Function.uncurry fun (g : GeneralLinear (n + 1) F)
      (w : Fin (n + 1) → F) => -((g⁻¹ * x₀.2.1).val.mulVec x₀.2.2) + w) := by
    apply Continuous.measurable
    exact ((Units.continuous_val.comp ((continuous_inv.comp continuous_fst).mul
      continuous_const)).matrix_mulVec continuous_const).neg.add continuous_snd
  have h2 := (measurePreserving_mul_left μG' x₀.2.1⁻¹).skew_product hgm
    (Filter.Eventually.of_forall fun g => map_add_left_eq_self vol _)
  exact h1.prod h2

/-- The parabolic coordinates of the integral subgroup have total mass one. -/
theorem measure_parabolicPoint_preimage {n : ℕ} [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    [MeasurableSpace (GeneralLinear (n + 1) F)] [BorelSpace (GeneralLinear (n + 1) F)] :
    ((localMultiplicativeHaar F).prod ((generalLinearHaar F n).prod (columnHaar F n)))
      (parabolicPoint ⁻¹' (Conductor.integralSubgroup (ValuativeRel.valuation F).integer
        (n + 1) : Set (GeneralLinear (n + 1 + 1) F))) = 1 := by
  have hpre : parabolicPoint ⁻¹' (Conductor.integralSubgroup (ValuativeRel.valuation F).integer
        (n + 1) : Set (GeneralLinear (n + 1 + 1) F)) =
      (integralUnits (ValuativeRel.valuation F).integer : Set Fˣ) ×ˢ
        ((Conductor.integralSubgroup (ValuativeRel.valuation F).integer n :
          Set (GeneralLinear (n + 1) F)) ×ˢ (columnIntegers F n : Set (Fin (n + 1) → F))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, SetLike.mem_coe, mem_columnIntegers]
    exact parabolicPoint_mem_iff (ValuativeRel.valuation F).integer x
  rw [hpre, Measure.prod_prod, Measure.prod_prod, localMultiplicativeHaar_integerUnits,
    generalLinearHaar_integralSubgroup, columnHaar_integers, one_mul, one_mul]

omit [IsNonarchimedeanLocalField F] [SecondCountableTopology F] [MeasurableSpace F]
  [BorelSpace F] in
/-- The slices of a compactly supported function on a product are compactly supported. -/
theorem hasCompactSupport_slice {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {Φ : X × Y → ℝ} (hc : HasCompactSupport Φ) (x : X) :
    HasCompactSupport fun y => Φ (x, y) := by
  refine HasCompactSupport.intro (hc.image continuous_snd) fun y hy => ?_
  exact image_eq_zero_of_notMem_tsupport fun hxy => hy ⟨(x, y), hxy, rfl⟩

section Pointwise

variable {n : ℕ}

/-- The integrand `(g, w) ↦ f(diag(g,1) [[I,w],[0,1]] x)` of the column integral. -/
def columnIntegrand (f : GeneralLinear (n + 2) F → ℝ) (x : GeneralLinear (n + 2) F)
    (p : GeneralLinear (n + 1) F × (Fin (n + 1) → F)) : ℝ :=
  f (rankInclusion 1 p.1 * col p.2 * x)

/-- The column integral `h_x(g) = ∫ f(diag(g,1) [[I,w],[0,1]] x) dw`. -/
def columnIntegral (f : GeneralLinear (n + 2) F → ℝ) (x : GeneralLinear (n + 2) F)
    (g : GeneralLinear (n + 1) F) : ℝ :=
  ∫ w, columnIntegrand f x (g, w) ∂columnHaar F n

omit [T2Space F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
theorem continuous_columnIntegrand (f : GeneralLinear (n + 2) F → ℝ)
    (hfc : Continuous f) (x : GeneralLinear (n + 2) F) :
    Continuous (columnIntegrand f x) :=
  hfc.comp ((((rankInclusionContinuous 1).continuous.comp continuous_fst).mul
    (continuous_col.comp continuous_snd)).mul continuous_const)

omit [T2Space F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
theorem continuous_columnIntegrand_joint (f : GeneralLinear (n + 2) F → ℝ)
    (hfc : Continuous f) :
    Continuous (fun z : GeneralLinear (n + 2) F × (GeneralLinear (n + 1) F × (Fin (n + 1) → F)) =>
      columnIntegrand f z.1 z.2) :=
  hfc.comp ((((rankInclusionContinuous 1).continuous.comp (continuous_fst.comp continuous_snd)).mul
    (continuous_col.comp (continuous_snd.comp continuous_snd))).mul continuous_fst)

omit [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
theorem hasCompactSupport_columnIntegrand (f : GeneralLinear (n + 2) F → ℝ)
    (hfs : HasCompactSupport f) (x : GeneralLinear (n + 2) F) :
    HasCompactSupport (columnIntegrand f x) :=
  hfs.comp_isClosedEmbedding ((Homeomorph.mulRight x).isClosedEmbedding.comp
    isClosedEmbedding_rankInclusion_mul_col)

theorem columnIntegral_continuous_hasCompactSupport (f : GeneralLinear (n + 2) F → ℝ)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (x : GeneralLinear (n + 2) F) :
    Continuous (columnIntegral f x) ∧ HasCompactSupport (columnIntegral f x) :=
  continuous_hasCompactSupport_integral (columnHaar F n) (continuous_columnIntegrand f hfc x)
    (hasCompactSupport_columnIntegrand f hfs x)

theorem ofReal_columnIntegral (f : GeneralLinear (n + 2) F → ℝ)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hf0 : ∀ y, 0 ≤ f y)
    (x : GeneralLinear (n + 2) F) (g : GeneralLinear (n + 1) F) :
    ENNReal.ofReal (columnIntegral f x g) =
      ∫⁻ w, ENNReal.ofReal (columnIntegrand f x (g, w)) ∂columnHaar F n := by
  have hslice : HasCompactSupport fun w => columnIntegrand f x (g, w) :=
    hasCompactSupport_slice (hasCompactSupport_columnIntegrand f hfs x) g
  have hcs : Continuous fun w => columnIntegrand f x (g, w) :=
    (continuous_columnIntegrand f hfc x).comp (Continuous.prodMk_right g)
  exact ofReal_integral_eq_lintegral_ofReal (hcs.integrable_of_hasCompactSupport hslice)
    (Filter.Eventually.of_forall fun w => hf0 _)

/-- Unfolding the larger unipotent average: the column variable and the smaller
unipotent group. -/
theorem ofReal_integral_unipotentHaar
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 2) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 2) F)] (χ : F →*₀ ℝ≥0)
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, M.det ≠ 0 →
      (columnHaar F n).map (Matrix.toLin' M) = (χ M.det)⁻¹ • columnHaar F n)
    (f : GeneralLinear (n + 2) F → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hf0 : ∀ y, 0 ≤ f y) (y : GeneralLinear (n + 2) F) :
    ENNReal.ofReal (∫ u : GeneralLinear.upperUnipotent (n + 2) F, f (u.val * y)
        ∂unipotentHaar F (n + 1)) =
      ∫⁻ u : GeneralLinear.upperUnipotent (n + 1) F, ∫⁻ v,
        ENNReal.ofReal (f (col v * rankInclusion 1 u.val * y)) ∂columnHaar F n
          ∂unipotentHaar F n := by
  have hint := integrable_subgroup_mul_of_hasCompactSupport
    (GeneralLinear.upperUnipotent (n + 2) F) (UpperUnipotent.isClosed (R := F))
    (unipotentHaar F (n + 1)) f hfc hfs y
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun u => hf0 _),
    ← coordinateMeasure_columnHaar χ hdet, coordinateMeasure,
    lintegral_map _ measurable_unipotentCoordinates]
  · rw [lintegral_prod_symm']
    · rfl
    · exact (ENNReal.continuous_ofReal.comp (hfc.comp
        ((continuous_subtype_val.comp unipotentCoordinates.continuous).mul
          continuous_const))).measurable
  · exact (ENNReal.continuous_ofReal.comp (hfc.comp
      (continuous_subtype_val.mul continuous_const))).measurable

/-- The pointwise identity behind the recursion: the inverse determinant times the
larger unipotent average equals the smaller unipotent average of the column integral. -/
theorem inv_mul_ofReal_average
    [MeasurableSpace (GeneralLinear (n + 2) F)] [BorelSpace (GeneralLinear (n + 2) F)]
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 2) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 2) F)] (χ : F →*₀ ℝ≥0)
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, M.det ≠ 0 →
      (columnHaar F n).map (Matrix.toLin' M) = (χ M.det)⁻¹ • columnHaar F n)
    (f : GeneralLinear (n + 2) F → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hf0 : ∀ y, 0 ≤ f y) (x : GeneralLinear (n + 2) F) (g : GeneralLinear (n + 1) F) :
    ((χ g.val.det : ℝ≥0∞))⁻¹ * ENNReal.ofReal (∫ u : GeneralLinear.upperUnipotent (n + 2) F,
        f (u.val * (rankInclusion 1 g * x)) ∂unipotentHaar F (n + 1)) =
      ENNReal.ofReal (∫ u : GeneralLinear.upperUnipotent (n + 1) F,
        columnIntegral f x (u.val * g) ∂unipotentHaar F n) := by
  have hne : (χ g.val.det : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    exact (map_ne_zero χ).mpr (Matrix.isUnits_det_units g).ne_zero
  obtain ⟨hcc, hcs⟩ := columnIntegral_continuous_hasCompactSupport f hfc hfs x
  have hint := integrable_subgroup_mul_of_hasCompactSupport
    (GeneralLinear.upperUnipotent (n + 1) F) (UpperUnipotent.isClosed (R := F))
    (unipotentHaar F n) (columnIntegral f x) hcc hcs g
  have hnn : ∀ g', 0 ≤ columnIntegral f x g' := fun g' => integral_nonneg fun w => hf0 _
  rw [ofReal_integral_unipotentHaar χ hdet f hfc hfs hf0,
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun u => hnn _),
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hne)]
  apply lintegral_congr
  intro u
  rw [ofReal_columnIntegral f hfc hfs hf0 x (u.val * g)]
  simp only [columnIntegrand]
  have hΦ : Measurable fun z : GeneralLinear (n + 1 + 1) F => ENNReal.ofReal (f (z * x)) :=
    (ENNReal.continuous_ofReal.comp (hfc.comp (continuous_id.mul continuous_const))).measurable
  have hconv := lintegral_col_mul_rankInclusion χ (columnHaar F n) hdet (u.val * g)
    (fun z => ENNReal.ofReal (f (z * x))) hΦ
  have hdetu : (u.val * g).val.det = g.val.det := by
    rw [Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]
  rw [hdetu] at hconv
  rw [← hconv]
  congr 1
  apply lintegral_congr
  intro v
  simp only [map_mul, mul_assoc]

end Pointwise

omit [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] in
/-- Every nonnegative compactly supported continuous function on the larger quotient is
the unipotent average of a nonnegative compactly supported continuous function. -/
theorem exists_nonneg_average_eq {n : ℕ}
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 2) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 2) F)]
    [IsMulRightInvariant (unipotentHaar F (n + 1))]
    (φ : C_c(LeftUnipotentQuotient (n + 1) F, ℝ)) (hφ : ∀ q, 0 ≤ φ q) :
    ∃ f : C_c(GeneralLinear (n + 2) F, ℝ), (∀ y, 0 ≤ f y) ∧
      ∀ q, quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
        (unipotentHaar F (n + 1)) f q = φ q := by
  obtain ⟨f, hf, hf0⟩ := realQuotientPositiveLifting (GeneralLinear.upperUnipotent (n + 2) F)
    (UpperUnipotent.isClosed (R := F)) (unipotentHaar F (n + 1)) φ
  refine ⟨f, hf0 hφ, fun q => ?_⟩
  induction q using Quotient.inductionOn with
  | h g => exact hf g

section Main

variable {n : ℕ}
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (GeneralLinear (n + 1) F)] [BorelSpace (GeneralLinear (n + 1) F)]
  [MeasurableSpace (GeneralLinear (n + 2) F)] [BorelSpace (GeneralLinear (n + 2) F)]
  [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
  [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)]
  [MeasurableSpace (GeneralLinear.upperUnipotent (n + 2) F)]
  [BorelSpace (GeneralLinear.upperUnipotent (n + 2) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient (n + 1) F)]
  [BorelSpace (LeftUnipotentQuotient (n + 1) F)]

/-- **The recursive identity for lower integrals.** For a nonnegative compactly
supported continuous `f` on `GL_(n+2)`, the recursive measure integrates the unipotent
average of `f` to the Haar integral of `f`. -/
theorem lintegral_ofReal_average_map (χ : F →*₀ ℝ≥0) (abv : AbsoluteValue F ℝ)
    (habv : ∀ x, abv x = χ x) (habvc : Continuous fun x : F => abv x)
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, M.det ≠ 0 →
      (columnHaar F n).map (Matrix.toLin' M) = (χ M.det)⁻¹ • columnHaar F n)
    [IsMulRightInvariant (unipotentHaar F n)] [IsMulRightInvariant (unipotentHaar F (n + 1))]
    (μsmall : Measure (LeftUnipotentQuotient n F))
    (hsmall : IsCompatible (GeneralLinear.upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) μsmall)
    (f : C_c(GeneralLinear (n + 2) F, ℝ)) (hf0 : ∀ y, 0 ≤ f y) :
    ∫⁻ q, ENNReal.ofReal (quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
        (unipotentHaar F (n + 1)) f q)
        ∂(Measure.map (recursiveQuotientCoordinates (F := F) n)
          ((μsmall.prod ((localMultiplicativeHaar F).prod
            ((generalLinearHaar F (n + 1)).restrict
              (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
                Set (GeneralLinear (n + 2) F))))).withDensity
            fun z => ENNReal.ofReal ((quotientDeterminantAbs abv n z.1)⁻¹))) =
      ∫⁻ y, ENNReal.ofReal (f y) ∂generalLinearHaar F (n + 1) := by
  have hKo : IsOpen (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
      Set (GeneralLinear (n + 2) F)) :=
    Conductor.isOpen_integralSubgroup _ _ (Valuation.isOpen_integer (v := ValuativeRel.valuation F))
  -- continuity of the weight, of the average and of the coordinates
  have hdetc : Continuous fun g : GeneralLinear (n + 1) F => abv (Matrix.det g.val) :=
    habvc.comp (Continuous.matrix_det Units.continuous_val)
  have hqc : Continuous (quotientDeterminantAbs abv n) := hdetc.quotient_lift _
  have hwc : Continuous fun q : LeftUnipotentQuotient n F =>
      ENNReal.ofReal ((quotientDeterminantAbs abv n q)⁻¹) :=
    ENNReal.continuous_ofReal.comp
      (hqc.inv₀ fun q => (quotientDeterminantAbs_pos abv n q).ne')
  have havc : Continuous fun q => ENNReal.ofReal (quotientAverageReal
      (GeneralLinear.upperUnipotent (n + 2) F) (unipotentHaar F (n + 1)) f q) :=
    ENNReal.continuous_ofReal.comp (continuous_quotientAverageReal _
      (UpperUnipotent.isClosed (R := F)) _ f)
  have hcoord := continuous_recursiveQuotientCoordinates (F := F) n
  -- the inner integral over the lower quotient, for fixed scalar and compact coordinates
  have hinner : ∀ p : Fˣ × GeneralLinear (n + 2) F,
      ∫⁻ q, ENNReal.ofReal ((quotientDeterminantAbs abv n q)⁻¹) *
          ENNReal.ofReal (quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
            (unipotentHaar F (n + 1)) f (recursiveQuotientCoordinates n (q, p))) ∂μsmall =
        ∫⁻ g, ∫⁻ w, ENNReal.ofReal (columnIntegrand f (GeneralLinear.scalar p.1 * p.2) (g, w))
          ∂columnHaar F n ∂generalLinearHaar F n := by
    intro p
    obtain ⟨a, k⟩ := p
    obtain ⟨hcc, hcs⟩ := columnIntegral_continuous_hasCompactSupport f f.continuous
      f.hasCompactSupport (GeneralLinear.scalar a * k)
    have hnn : ∀ g, 0 ≤ columnIntegral f (GeneralLinear.scalar a * k) g :=
      fun g => integral_nonneg fun w => hf0 _
    rw [← lintegral_congr fun g => ofReal_columnIntegral f f.continuous f.hasCompactSupport hf0
      (GeneralLinear.scalar a * k) g,
      ← lintegral_quotientAverageReal (GeneralLinear.upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μsmall hsmall _ hcc hcs hnn]
    apply lintegral_congr
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      have hne : (χ g.val.det : ℝ≥0∞) ≠ 0 := by
        rw [ENNReal.coe_ne_zero]
        exact (map_ne_zero χ).mpr (Matrix.isUnits_det_units g).ne_zero
      have hw : ENNReal.ofReal ((quotientDeterminantAbs abv n (Quotient.mk _ g))⁻¹) =
          ((χ g.val.det : ℝ≥0∞))⁻¹ := by
        rw [quotientDeterminantAbs_mk, habv, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal,
          ENNReal.coe_inv (by exact_mod_cast hne)]
      rw [hw, recursiveQuotientCoordinates_mk]
      change ((χ g.val.det : ℝ≥0∞))⁻¹ * ENNReal.ofReal
          (∫ u : GeneralLinear.upperUnipotent (n + 2) F,
            f (u.val * (rankInclusion 1 g * GeneralLinear.scalar a * k))
              ∂unipotentHaar F (n + 1)) =
        ENNReal.ofReal (∫ u : GeneralLinear.upperUnipotent (n + 1) F,
          columnIntegral f (GeneralLinear.scalar a * k) (u.val * g) ∂unipotentHaar F n)
      rw [← inv_mul_ofReal_average χ hdet f f.continuous f.hasCompactSupport hf0, mul_assoc]
  have : μsmall.Regular := hsmall.regular
  have := leftQuotient_locallyCompactSpace (GeneralLinear.upperUnipotent (n + 1) F)
  have hFm : Measurable fun z : LeftUnipotentQuotient n F × (Fˣ × GeneralLinear (n + 2) F) =>
      ENNReal.ofReal ((quotientDeterminantAbs abv n z.1)⁻¹) *
        ENNReal.ofReal (quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
          (unipotentHaar F (n + 1)) f (recursiveQuotientCoordinates n z)) :=
    (hwc.comp continuous_fst).measurable.mul (havc.comp hcoord).measurable
  have hΘ : Measurable fun z : ((Fˣ × GeneralLinear (n + 2) F) × GeneralLinear (n + 1) F) ×
      (Fin (n + 1) → F) =>
      ENNReal.ofReal (columnIntegrand f (GeneralLinear.scalar z.1.1.1 * z.1.1.2) (z.1.2, z.2)) :=
    (ENNReal.continuous_ofReal.comp ((continuous_columnIntegrand_joint f f.continuous).comp
      (((GeneralLinear.scalarContinuous.continuous.comp
        (continuous_fst.comp (continuous_fst.comp continuous_fst))).mul
        (continuous_snd.comp (continuous_fst.comp continuous_fst))).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))).measurable
  have hΨ : Measurable fun p : Fˣ × GeneralLinear (n + 2) F =>
      ∫⁻ g, ∫⁻ w, ENNReal.ofReal (columnIntegrand f (GeneralLinear.scalar p.1 * p.2) (g, w))
        ∂columnHaar F n ∂generalLinearHaar F n :=
    (Measurable.lintegral_prod_right' (ν := columnHaar F n) hΘ).lintegral_prod_right'
      (ν := generalLinearHaar F n)
  have h7 : ∀ k : GeneralLinear (n + 2) F,
      ∫⁻ a, ∫⁻ g, ∫⁻ w, ENNReal.ofReal (columnIntegrand f (GeneralLinear.scalar a * k) (g, w))
          ∂columnHaar F n ∂generalLinearHaar F n ∂localMultiplicativeHaar F =
        ∫⁻ x, ENNReal.ofReal (f (parabolicPoint x * k))
          ∂(localMultiplicativeHaar F).prod ((generalLinearHaar F n).prod (columnHaar F n)) := by
    intro k
    have hm1 : Measurable fun x : Fˣ × (GeneralLinear (n + 1) F × (Fin (n + 1) → F)) =>
        ENNReal.ofReal (f (parabolicPoint x * k)) :=
      (ENNReal.continuous_ofReal.comp (f.continuous.comp
        (continuous_parabolicPoint.mul continuous_const))).measurable
    rw [lintegral_prod _ hm1.aemeasurable]
    apply lintegral_congr
    intro a
    have hm2 : Measurable fun y : GeneralLinear (n + 1) F × (Fin (n + 1) → F) =>
        ENNReal.ofReal (f (parabolicPoint (a, y) * k)) :=
      (ENNReal.continuous_ofReal.comp (f.continuous.comp
        ((continuous_parabolicPoint.comp (Continuous.prodMk_right a)).mul
          continuous_const))).measurable
    rw [lintegral_prod _ hm2.aemeasurable]
    apply lintegral_congr
    intro g
    apply lintegral_congr
    intro w
    simp only [columnIntegrand, parabolicPoint, mul_assoc]
  calc ∫⁻ q, ENNReal.ofReal (quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
          (unipotentHaar F (n + 1)) f q)
          ∂(Measure.map (recursiveQuotientCoordinates (F := F) n)
            ((μsmall.prod ((localMultiplicativeHaar F).prod
              ((generalLinearHaar F (n + 1)).restrict
                (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
                  Set (GeneralLinear (n + 2) F))))).withDensity
              fun z => ENNReal.ofReal ((quotientDeterminantAbs abv n z.1)⁻¹)))
      = ∫⁻ z, ENNReal.ofReal ((quotientDeterminantAbs abv n z.1)⁻¹) *
          ENNReal.ofReal (quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
            (unipotentHaar F (n + 1)) f (recursiveQuotientCoordinates n z))
          ∂(μsmall.prod ((localMultiplicativeHaar F).prod
              ((generalLinearHaar F (n + 1)).restrict
                (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
                  Set (GeneralLinear (n + 2) F))))) := by
        have hwm : Measurable fun z : LeftUnipotentQuotient n F × (Fˣ × GeneralLinear (n + 2) F) =>
            ENNReal.ofReal ((quotientDeterminantAbs abv n z.1)⁻¹) :=
          (hwc.comp continuous_fst).measurable
        have hFm2 : Measurable fun z : LeftUnipotentQuotient n F × (Fˣ × GeneralLinear (n + 2) F) =>
            ENNReal.ofReal (quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
              (unipotentHaar F (n + 1)) f (recursiveQuotientCoordinates n z)) :=
          (havc.comp hcoord).measurable
        rw [lintegral_map havc.measurable hcoord.measurable,
          lintegral_withDensity_eq_lintegral_mul _ hwm hFm2]
        rfl
    _ = ∫⁻ p, ∫⁻ q, ENNReal.ofReal ((quotientDeterminantAbs abv n q)⁻¹) *
          ENNReal.ofReal (quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
            (unipotentHaar F (n + 1)) f (recursiveQuotientCoordinates n (q, p))) ∂μsmall
          ∂((localMultiplicativeHaar F).prod
              ((generalLinearHaar F (n + 1)).restrict
                (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
                  Set (GeneralLinear (n + 2) F)))) :=
        lintegral_prod_symm _ hFm.aemeasurable
    _ = ∫⁻ p, ∫⁻ g, ∫⁻ w,
          ENNReal.ofReal (columnIntegrand f (GeneralLinear.scalar p.1 * p.2) (g, w))
          ∂columnHaar F n ∂generalLinearHaar F n
          ∂((localMultiplicativeHaar F).prod
              ((generalLinearHaar F (n + 1)).restrict
                (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
                  Set (GeneralLinear (n + 2) F)))) :=
        lintegral_congr hinner
    _ = ∫⁻ k, ∫⁻ a, ∫⁻ g, ∫⁻ w,
          ENNReal.ofReal (columnIntegrand f (GeneralLinear.scalar a * k) (g, w))
          ∂columnHaar F n ∂generalLinearHaar F n ∂localMultiplicativeHaar F
          ∂((generalLinearHaar F (n + 1)).restrict
                (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
                  Set (GeneralLinear (n + 2) F))) :=
        lintegral_prod_symm _ hΨ.aemeasurable
    _ = ∫⁻ k, ∫⁻ x, ENNReal.ofReal (f (parabolicPoint x * k))
          ∂(localMultiplicativeHaar F).prod ((generalLinearHaar F n).prod (columnHaar F n))
          ∂((generalLinearHaar F (n + 1)).restrict
                (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
                  Set (GeneralLinear (n + 2) F))) :=
        lintegral_congr h7
    _ = ((localMultiplicativeHaar F).prod ((generalLinearHaar F n).prod (columnHaar F n)))
          (parabolicPoint ⁻¹' (Conductor.integralSubgroup (ValuativeRel.valuation F).integer
            (n + 1) : Set (GeneralLinear (n + 1 + 1) F))) *
          ∫⁻ y, ENNReal.ofReal (f y) ∂generalLinearHaar F (n + 1) :=
        CompactFactorization.lintegral_restrict_lintegral_mul (generalLinearHaar F (n + 1))
          (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1))
          hKo.measurableSet _ parabolicPoint continuous_parabolicPoint.measurable
          (fun y => exists_parabolicPoint_mul (ValuativeRel.valuation F) y)
          (fun x₀ => ⟨parabolicShift x₀, measurePreserving_parabolicShift _ _ _ x₀,
            fun x => parabolicPoint_shift x₀ x⟩)
          (fun y => ENNReal.ofReal (f y)) (ENNReal.continuous_ofReal.comp f.continuous).measurable
    _ = ∫⁻ y, ENNReal.ofReal (f y) ∂generalLinearHaar F (n + 1) := by
        rw [measure_parabolicPoint_preimage, one_mul]

/-- **Recursive quotient integration, over a general nonarchimedean local field.** -/
theorem eq_map_recursiveQuotientCoordinates (χ : F →*₀ ℝ≥0) (abv : AbsoluteValue F ℝ)
    (habv : ∀ x, abv x = χ x) (habvc : Continuous fun x : F => abv x)
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, M.det ≠ 0 →
      (columnHaar F n).map (Matrix.toLin' M) = (χ M.det)⁻¹ • columnHaar F n)
    [IsMulRightInvariant (unipotentHaar F n)] [IsMulRightInvariant (unipotentHaar F (n + 1))]
    (μsmall : Measure (LeftUnipotentQuotient n F))
    (μlarge : Measure (LeftUnipotentQuotient (n + 1) F))
    (hsmall : IsCompatible (GeneralLinear.upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) μsmall)
    (hlarge : IsCompatible (GeneralLinear.upperUnipotent (n + 2) F)
      (generalLinearHaar F (n + 1)) (unipotentHaar F (n + 1)) μlarge) :
    μlarge = Measure.map (recursiveQuotientCoordinates (F := F) n)
      ((μsmall.prod ((localMultiplicativeHaar F).prod
        ((generalLinearHaar F (n + 1)).restrict
          (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
            Set (GeneralLinear (n + 2) F))))).withDensity
        fun z => ENNReal.ofReal ((quotientDeterminantAbs abv n z.1)⁻¹)) := by
  have := leftQuotient_t2Space (GeneralLinear.upperUnipotent (n + 2) F)
    (UpperUnipotent.isClosed (R := F))
  have := leftQuotient_locallyCompactSpace (GeneralLinear.upperUnipotent (n + 2) F)
  have hL := lintegral_ofReal_average_map χ abv habv habvc hdet μsmall hsmall
  set ν := Measure.map (recursiveQuotientCoordinates (F := F) n)
      ((μsmall.prod ((localMultiplicativeHaar F).prod
        ((generalLinearHaar F (n + 1)).restrict
          (Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n + 1) :
            Set (GeneralLinear (n + 2) F))))).withDensity
        fun z => ENNReal.ofReal ((quotientDeterminantAbs abv n z.1)⁻¹)) with hν
  have hfin : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨u, hu1, -, hucs, hu01⟩ :=
      exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
    let φ : C_c(LeftUnipotentQuotient (n + 1) F, ℝ) := ⟨u, hucs⟩
    obtain ⟨f, hf0, hfavg⟩ := exists_nonneg_average_eq φ fun q => (hu01 q).1
    calc ν C = ∫⁻ q, C.indicator 1 q ∂ν := (lintegral_indicator_one hC.isClosed.measurableSet).symm
      _ ≤ ∫⁻ q, ENNReal.ofReal (quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
            (unipotentHaar F (n + 1)) f q) ∂ν := by
          apply lintegral_mono
          intro q
          dsimp only
          rw [hfavg q]
          by_cases hq : q ∈ C
          · rw [Set.indicator_of_mem hq]
            change (1 : ENNReal) ≤ ENNReal.ofReal (u q)
            rw [hu1 hq, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hq]
            exact zero_le
      _ = ∫⁻ y, ENNReal.ofReal (f y) ∂generalLinearHaar F (n + 1) := hL f hf0
      _ < ⊤ := (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).lintegral_lt_top
  have : ν.Regular := inferInstance
  have : μlarge.Regular := hlarge.regular
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro φ
  let φr : C_c(LeftUnipotentQuotient (n + 1) F, ℝ) :=
    ⟨⟨fun q => (φ q : ℝ), NNReal.continuous_coe.comp φ.continuous⟩,
      φ.hasCompactSupport.comp_left NNReal.coe_zero⟩
  obtain ⟨f, hf0, hfavg⟩ := exists_nonneg_average_eq φr fun q => (φ q).coe_nonneg
  have key : ∀ μ' : Measure (LeftUnipotentQuotient (n + 1) F),
      ∫⁻ q, ENNReal.ofReal (quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
          (unipotentHaar F (n + 1)) f q) ∂μ' =
        ∫⁻ y, ENNReal.ofReal (f y) ∂generalLinearHaar F (n + 1) →
      ∫ q, (φ q : ℝ) ∂μ' = (∫⁻ y, ENNReal.ofReal (f y) ∂generalLinearHaar F (n + 1)).toReal := by
    intro μ' h
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun q => (φ q).coe_nonneg)
      (NNReal.continuous_coe.comp φ.continuous).aestronglyMeasurable, ← h]
    congr 1
    apply lintegral_congr
    intro q
    rw [hfavg q]
    rfl
  rw [key μlarge (lintegral_quotientAverageReal (GeneralLinear.upperUnipotent (n + 2) F)
      (generalLinearHaar F (n + 1)) (unipotentHaar F (n + 1)) μlarge hlarge f f.continuous
      f.hasCompactSupport hf0),
    key ν (hL f hf0)]

end Main

end Measure

end RecursiveIntegration

open MeasureTheory GeneralLinear QuotientIntegration RecursiveIntegration

universe uF

/-- **Normalized recursive quotient integration for JPSS central coordinates.** -/
theorem recursiveQuotientIntegration {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) : RecursiveQuotientIntegrationStatement F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 2) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 2) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 2) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 2) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (n + 1) F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient (n + 1) F.Carrier) := ⟨rfl⟩
  intro _ _ μsmall μlarge hsmall hlarge
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier, M.det ≠ 0 →
      (columnHaar F.Carrier n).map (Matrix.toLin' M) =
        (T.normalizedAbsHom M.det)⁻¹ • columnHaar F.Carrier n :=
    fun M hM => HarmonicAnalysis.haarMeasure_map_matrix (Measure.addHaar : Measure F.Carrier)
      T.normalizedAbsHom hχ _ hM
  have habvc : Continuous fun x : F.Carrier => normalizedAbsoluteValue T x :=
    NNReal.continuous_coe.comp T.continuous_normalizedAbsHom
  exact eq_map_recursiveQuotientCoordinates T.normalizedAbsHom (normalizedAbsoluteValue T)
    (fun _ => rfl) habvc hdet μsmall μlarge hsmall hlarge

end Langlands.RankinSelberg
