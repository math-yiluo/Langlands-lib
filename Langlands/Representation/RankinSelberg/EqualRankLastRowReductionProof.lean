import Langlands.Topology.CompactNormCharacter
import Langlands.Representation.RankinSelberg.EqualRankLastRowReductionStatement
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Group.GL.MirabolicProjection
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.Representation.Smooth.SmallRealizationProof

/-!
# Equal-rank integrals with a last-row orbit cutoff: proof
-/

noncomputable section

namespace Langlands.RankinSelberg

namespace LastRowReduction

open MeasureTheory GeneralLinear GeneralLinear.Mirabolic QuotientIntegration

section Algebra

variable {K : Type*} [Field K] {n : ℕ}

/-- The radical matrix `[[I, v], [0, 1]]` of `GL_(n+2)`. -/
def col (v : Fin (n + 1) → K) : Langlands.GeneralLinear (n + 1 + 1) K :=
  (radicalElement (n := n + 1) v).val.val

theorem col_add (v w : Fin (n + 1) → K) : col (v + w) = col v * col w := by
  unfold col
  rw [radicalElement_add]
  rfl

@[simp] theorem col_zero : col (0 : Fin (n + 1) → K) = 1 := by
  unfold col
  rw [radicalElement_zero]
  rfl

theorem col_neg (v : Fin (n + 1) → K) : col (-v) = (col v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← col_add, neg_add_cancel, col_zero]

theorem col_mem (v : Fin (n + 1) → K) :
    col v ∈ GeneralLinear.upperUnipotent (n + 1 + 1) K :=
  radical_le_upperUnipotent (radicalElement (n := n + 1) v).property

/-- `diag(g,1) [[I,v],[0,1]] = [[I,g v],[0,1]] diag(g,1)`. -/
theorem rankInclusion_mul_col (g : Langlands.GeneralLinear (n + 1) K)
    (v : Fin (n + 1) → K) :
    rankInclusion 1 g * col v = col (g.val.mulVec v) * rankInclusion 1 g :=
  congrArg Subtype.val (levi_mul_radicalElement g v)

theorem col_mul_rankInclusion (g : Langlands.GeneralLinear (n + 1) K)
    (v : Fin (n + 1) → K) :
    col v * rankInclusion 1 g = rankInclusion 1 g * col ((g⁻¹).val.mulVec v) := by
  rw [rankInclusion_mul_col, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

theorem rankInclusion_mem (u : GeneralLinear.upperUnipotent (n + 1) K) :
    rankInclusion 1 u.val ∈ GeneralLinear.upperUnipotent (n + 1 + 1) K :=
  corankOne_mem_unipotent u

/-- The upper-left block of an upper-unipotent mirabolic matrix is upper unipotent. -/
theorem projection_mem (x : mirabolic (n + 1) K)
    (hx : x.val ∈ GeneralLinear.upperUnipotent (n + 1 + 1) K) :
    projection x ∈ GeneralLinear.upperUnipotent (n + 1) K := by
  constructor
  · intro i j hij
    change x.val.val i.castSucc j.castSucc = 0
    exact hx.1 (Fin.castSucc_lt_castSucc_iff.mpr hij)
  · intro i
    change x.val.val i.castSucc i.castSucc = 1
    exact hx.2 i.castSucc

/-- Every upper-unipotent matrix of `GL_(n+2)` is `[[I,v],[0,1]] diag(u,1)`. -/
theorem exists_col_mul_rankInclusion (x : Langlands.GeneralLinear (n + 1 + 1) K)
    (hx : x ∈ GeneralLinear.upperUnipotent (n + 1 + 1) K) :
    ∃ (v : Fin (n + 1) → K) (u : GeneralLinear.upperUnipotent (n + 1) K),
      x = col v * rankInclusion 1 u.val := by
  let p : mirabolic (n + 1) K := ⟨x, upperUnipotent_le_mirabolic hx⟩
  refine ⟨lastColumn p, ⟨projection p, projection_mem p hx⟩, ?_⟩
  exact congrArg Subtype.val (eq_radicalElement_mul_levi p)

/-- Coordinates in `[[u,v],[0,1]] = [[I,v],[0,1]] diag(u,1)` are unique. -/
theorem col_mul_rankInclusion_inj {v v' : Fin (n + 1) → K}
    {g g' : Langlands.GeneralLinear (n + 1) K}
    (h : col v * rankInclusion 1 g = col v' * rankInclusion 1 g') : v = v' ∧ g = g' := by
  have h' : (radicalElement v).val * levi g = (radicalElement v').val * levi g' :=
    Subtype.ext h
  have := (eq_radicalElement_mul_levi_iff ((radicalElement v').val * levi g') v g).mp h'.symm
  simpa using this

/-- Multiplying `[[I,v],[0,1]] diag(u,1)` by `diag(g,1)⁻¹` and `diag(h,1)`. -/
theorem conj_col_mul_rankInclusion' (g h u : Langlands.GeneralLinear (n + 1) K)
    (v : Fin (n + 1) → K) :
    (rankInclusion 1 g)⁻¹ * (col v * rankInclusion 1 u) * rankInclusion 1 h =
      col ((g⁻¹).val.mulVec v) * rankInclusion 1 (g⁻¹ * u * h) := by
  rw [← map_inv, map_mul, map_mul, ← mul_assoc, ← mul_assoc, rankInclusion_mul_col]
  group

/-- Conjugating `[[I,v],[0,1]] diag(u,1)` by `diag(h,1)`. -/
theorem conj_col_mul_rankInclusion (h u : Langlands.GeneralLinear (n + 1) K)
    (v : Fin (n + 1) → K) :
    (rankInclusion 1 h)⁻¹ * (col v * rankInclusion 1 u) * rankInclusion 1 h =
      col ((h⁻¹).val.mulVec v) * rankInclusion 1 (h⁻¹ * u * h) :=
  conj_col_mul_rankInclusion' h h u v

theorem col_mul_rankInclusion_mul (v₀ v : Fin (n + 1) → K)
    (u₀ u : Langlands.GeneralLinear (n + 1) K) :
    col v₀ * rankInclusion 1 u₀ * (col v * rankInclusion 1 u) =
      col (v₀ + u₀.val.mulVec v) * rankInclusion 1 (u₀ * u) := by
  rw [mul_assoc, ← mul_assoc (rankInclusion 1 u₀), rankInclusion_mul_col, col_add, map_mul]
  group

end Algebra

section PiecewiseConstant

open scoped NNReal ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- Integrability and integral of a function that is constant on each member of a
countable disjoint family of measurable sets of finite measure and vanishes off
their union. -/
theorem piecewiseConstant_integral (μ : Measure X) {ι : Type*} [Countable ι]
    (E : ι → Set X) (hE : ∀ i, MeasurableSet (E i)) (hd : Pairwise (Function.onFun Disjoint E))
    (hfin : ∀ i, μ (E i) ≠ ⊤) (f : X → ℂ) (hf : AEStronglyMeasurable f μ) (a : ι → ℂ)
    (ha : ∀ i, ∀ x ∈ E i, f x = a i) (h0 : ∀ x, (∀ i, x ∉ E i) → f x = 0) :
    (Integrable f μ ↔ Summable fun i => ‖a i‖ * μ.real (E i)) ∧
      (Integrable f μ → ∫ x, f x ∂μ = ∑' i, μ.real (E i) • a i) := by
  have hsupp : ∀ x, x ∉ ⋃ i, E i → f x = 0 := fun x hx =>
    h0 x fun i hi => hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hlint : ∫⁻ x, ‖f x‖ₑ ∂μ =
      ∑' i, ((‖a i‖₊ * (μ (E i)).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [← setLIntegral_eq_of_support_subset (s := ⋃ i, E i), lintegral_iUnion hE hd]
    · congr 1
      funext i
      rw [setLIntegral_congr_fun (hE i) (g := fun _ => ‖a i‖ₑ)
          (fun x hx => by simp only [ha i x hx]),
        setLIntegral_const, ENNReal.coe_mul, ENNReal.coe_toNNReal (hfin i), enorm_eq_nnnorm]
    · intro x hx
      by_contra hxU
      exact hx (by simp [hsupp x hxU])
  have hreal (i : ι) : (((‖a i‖₊ * (μ (E i)).toNNReal : ℝ≥0)) : ℝ) = ‖a i‖ * μ.real (E i) := by
    simp [measureReal_def, ENNReal.coe_toNNReal_eq_toReal]
  have hint : Integrable f μ ↔ Summable fun i => ‖a i‖ * μ.real (E i) := by
    constructor
    · intro hi
      have h := hi.2
      rw [hasFiniteIntegral_def, hlint] at h
      have := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp h.ne
      simpa only [hreal] using this
    · intro hs
      refine ⟨hf, ?_⟩
      rw [hasFiniteIntegral_def, hlint, lt_top_iff_ne_top]
      exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr (by simpa only [hreal] using hs)
  refine ⟨hint, fun hi => ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    integral_iUnion hE hd hi.integrableOn]
  congr 1
  funext i
  rw [setIntegral_congr_fun (hE i) (g := fun _ => a i) (fun x hx => ha i x hx),
    setIntegral_const]

end PiecewiseConstant

section CompactDeterminant

open scoped NNReal

end CompactDeterminant

section Level

variable {K : Type*} [Field K] {n : ℕ}

/-- The image in `GL_(n+1)` of the mirabolic part of a subgroup of `GL_(n+2)`. -/
def level (J : Subgroup (Langlands.GeneralLinear (n + 1 + 1) K)) :
    Subgroup (Langlands.GeneralLinear (n + 1) K) :=
  (J.comap (mirabolic (n + 1) K).subtype).map projection

theorem mem_level {J : Subgroup (Langlands.GeneralLinear (n + 1 + 1) K)}
    {a : Langlands.GeneralLinear (n + 1) K} :
    a ∈ level J ↔ ∃ w : Fin (n + 1) → K, col w * rankInclusion 1 a ∈ J := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨lastColumn p, ?_⟩
    have he : col (lastColumn p) * rankInclusion 1 (projection p) = p.val :=
      (congrArg Subtype.val (eq_radicalElement_mul_levi p)).symm
    rw [he]
    exact hp
  · rintro ⟨w, hw⟩
    exact ⟨(radicalElement w).val * levi a, hw, projection_radicalElement_mul_levi w a⟩

/-- For `a` in the level, the admissible last columns form a translate of `Y₀`. -/
theorem col_mul_mem_iff {J : Subgroup (Langlands.GeneralLinear (n + 1 + 1) K)}
    {a : Langlands.GeneralLinear (n + 1) K} {w₀ : Fin (n + 1) → K}
    (h₀ : col w₀ * rankInclusion 1 a ∈ J) (w : Fin (n + 1) → K) :
    col w * rankInclusion 1 a ∈ J ↔ col (w - w₀) ∈ J := by
  have he : col (w - w₀) = (col w * rankInclusion 1 a) * (col w₀ * rankInclusion 1 a)⁻¹ := by
    rw [sub_eq_add_neg, col_add, col_neg]
    group
  rw [he]
  constructor
  · intro h
    exact J.mul_mem h (J.inv_mem h₀)
  · intro h
    simpa using J.mul_mem h h₀

end Level

section Coordinates

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

theorem continuous_col :
    Continuous (col : (Fin (n + 1) → K) → Langlands.GeneralLinear (n + 1 + 1) K) :=
  continuous_subtype_val.comp (continuous_subtype_val.comp continuous_radicalElement)

theorem isOpen_level (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)) :
    IsOpen (level J.toSubgroup : Set (Langlands.GeneralLinear (n + 1) K)) := by
  rw [isOpen_iff_forall_mem_open]
  intro a ha
  obtain ⟨w, hw⟩ := mem_level.mp ha
  refine ⟨(fun b => col w * rankInclusion 1 b) ⁻¹'
      (J : Set (Langlands.GeneralLinear (n + 1 + 1) K)),
    fun b hb => mem_level.mpr ⟨w, hb⟩, ?_, hw⟩
  exact J.isOpen.preimage (continuous_const.mul (rankInclusionContinuous 1).continuous)

omit [IsTopologicalRing K] in
theorem isCompact_level [T2Space K] (J : Subgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (hJ : IsCompact (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) :
    IsCompact (level J : Set (Langlands.GeneralLinear (n + 1) K)) := by
  have hc : IsCompact ((Subtype.val : mirabolic (n + 1) K → _) ⁻¹'
      (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) :=
    (GeneralLinear.Mirabolic.isClosed (n := n + 1) (F := K)).isClosedEmbedding_subtypeVal
      |>.isCompact_preimage hJ
  have := hc.image (continuous_projection (n := n + 1) (F := K))
  exact this

/-- The level of a compact open subgroup, as an open subgroup. -/
def levelOpen (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)) :
    OpenSubgroup (Langlands.GeneralLinear (n + 1) K) where
  toSubgroup := level J.toSubgroup
  isOpen' := isOpen_level J

@[simp] theorem mem_levelOpen {J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)}
    {a : Langlands.GeneralLinear (n + 1) K} :
    a ∈ levelOpen J ↔ ∃ w : Fin (n + 1) → K, col w * rankInclusion 1 a ∈ J :=
  mem_level

/-- Coordinates `(v, u) ↦ [[I, v], [0, 1]] diag(u, 1)` on the upper-unipotent group. -/
def unipotentCoordinates :
    (Fin (n + 1) → K) × GeneralLinear.upperUnipotent (n + 1) K ≃ₜ
      GeneralLinear.upperUnipotent (n + 1 + 1) K where
  toFun p := ⟨col p.1 * rankInclusion 1 p.2.val,
    mul_mem (col_mem p.1) (rankInclusion_mem p.2)⟩
  invFun x :=
    (lastColumn (⟨x.val, upperUnipotent_le_mirabolic x.property⟩ : mirabolic (n + 1) K),
      ⟨projection ⟨x.val, upperUnipotent_le_mirabolic x.property⟩,
        projection_mem ⟨x.val, upperUnipotent_le_mirabolic x.property⟩ x.property⟩)
  left_inv p := by
    obtain ⟨v, u⟩ := p
    refine Prod.ext ?_ (Subtype.ext ?_)
    · exact lastColumn_radicalElement_mul_levi v u.val
    · exact projection_radicalElement_mul_levi v u.val
  right_inv x := by
    apply Subtype.ext
    exact (congrArg Subtype.val
      (eq_radicalElement_mul_levi ⟨x.val, upperUnipotent_le_mirabolic x.property⟩)).symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_col.comp continuous_fst).mul
      ((rankInclusionContinuous 1).continuous.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have hp : Continuous fun x : GeneralLinear.upperUnipotent (n + 1 + 1) K =>
        (⟨x.val, upperUnipotent_le_mirabolic x.property⟩ : mirabolic (n + 1) K) :=
      continuous_subtype_val.subtype_mk _
    exact (continuous_lastColumn.comp hp).prodMk
      ((continuous_projection.comp hp).subtype_mk _)

@[simp] theorem unipotentCoordinates_apply_val (v : Fin (n + 1) → K)
    (u : GeneralLinear.upperUnipotent (n + 1) K) :
    (unipotentCoordinates (v, u)).val = col v * rankInclusion 1 u.val := rfl

end Coordinates


section HaarFiber

open scoped NNReal ENNReal
open Measure

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}
  [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) K)]
  [BorelSpace (GeneralLinear.upperUnipotent (n + 1) K)]
  [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1 + 1) K)]
  [BorelSpace (GeneralLinear.upperUnipotent (n + 1 + 1) K)]

theorem measurable_unipotentCoordinates :
    Measurable (unipotentCoordinates (K := K) (n := n)) :=
  unipotentCoordinates.continuous.measurable

/-- The product of a measure on columns and a measure on `N_(n+1)`, transported to
`N_(n+2)` by `unipotentCoordinates`. -/
def coordinateMeasure (vol : Measure (Fin (n + 1) → K))
    (μN' : Measure (GeneralLinear.upperUnipotent (n + 1) K)) :
    Measure (GeneralLinear.upperUnipotent (n + 1 + 1) K) :=
  (vol.prod μN').map unipotentCoordinates

theorem isMulLeftInvariant_coordinateMeasure [LocallyCompactSpace K] (χ : K →*₀ ℝ≥0)
    (vol : Measure (Fin (n + 1) → K)) [IsAddHaarMeasure vol]
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, M.det ≠ 0 →
      vol.map (Matrix.toLin' M) = (χ M.det)⁻¹ • vol)
    (μN' : Measure (GeneralLinear.upperUnipotent (n + 1) K)) [SFinite μN']
    [Measure.IsMulLeftInvariant μN'] :
    Measure.IsMulLeftInvariant (coordinateMeasure vol μN') := by
  constructor
  intro x₀
  obtain ⟨⟨v₀, u₀⟩, rfl⟩ := unipotentCoordinates.surjective x₀
  let L : (Fin (n + 1) → K) × GeneralLinear.upperUnipotent (n + 1) K →
      (Fin (n + 1) → K) × GeneralLinear.upperUnipotent (n + 1) K :=
    Prod.map (fun v => v₀ + Matrix.toLin' u₀.val.val v) (fun u => u₀ * u)
  have h1 : MeasurePreserving (Matrix.toLin' u₀.val.val) vol vol := by
    refine ⟨(LinearMap.continuous_on_pi _).measurable, ?_⟩
    rw [hdet _ (by simp), unipotent_det, map_one, inv_one, one_smul]
  have hL : MeasurePreserving L (vol.prod μN') (vol.prod μN') :=
    ((measurePreserving_add_left vol v₀).comp h1).prod (measurePreserving_mul_left μN' u₀)
  have hcomm : (fun x => unipotentCoordinates (v₀, u₀) * x) ∘ unipotentCoordinates =
      unipotentCoordinates ∘ L := by
    funext ⟨v, u⟩
    apply Subtype.ext
    simp only [Function.comp_apply, Subgroup.coe_mul, unipotentCoordinates_apply_val, L,
      Prod.map_apply, Matrix.toLin'_apply]
    exact col_mul_rankInclusion_mul v₀ v u₀.val u.val
  unfold coordinateMeasure
  rw [Measure.map_map (measurable_const_mul _) measurable_unipotentCoordinates, hcomm,
    ← Measure.map_map measurable_unipotentCoordinates hL.measurable, hL.map_eq]

theorem isFiniteMeasureOnCompacts_coordinateMeasure (vol : Measure (Fin (n + 1) → K))
    [IsFiniteMeasureOnCompacts vol] (μN' : Measure (GeneralLinear.upperUnipotent (n + 1) K))
    [SFinite μN'] [IsFiniteMeasureOnCompacts μN'] :
    IsFiniteMeasureOnCompacts (coordinateMeasure vol μN') :=
  Measure.IsFiniteMeasureOnCompacts.map (vol.prod μN') unipotentCoordinates

/-- The transported product measure is a positive multiple of a Haar measure on `N_(n+2)`. -/
theorem exists_coordinateMeasure_eq_smul [LocallyCompactSpace K] [T2Space K]
    [LocallyCompactSpace (Langlands.GeneralLinear (n + 1 + 1) K)]
    [SecondCountableTopology (Langlands.GeneralLinear (n + 1 + 1) K)] (χ : K →*₀ ℝ≥0)
    (vol : Measure (Fin (n + 1) → K)) [IsAddHaarMeasure vol]
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, M.det ≠ 0 →
      vol.map (Matrix.toLin' M) = (χ M.det)⁻¹ • vol)
    (μN' : Measure (GeneralLinear.upperUnipotent (n + 1) K)) [SFinite μN']
    [IsHaarMeasure μN'] (μN : Measure (GeneralLinear.upperUnipotent (n + 1 + 1) K))
    [IsHaarMeasure μN] :
    ∃ κ : ℝ≥0, coordinateMeasure vol μN' = κ • μN := by
  have : LocallyCompactSpace (GeneralLinear.upperUnipotent (n + 1 + 1) K) :=
    UpperUnipotent.locallyCompactSpace
  have : SecondCountableTopology (GeneralLinear.upperUnipotent (n + 1 + 1) K) :=
    TopologicalSpace.Subtype.secondCountableTopology
      (GeneralLinear.upperUnipotent (n + 1 + 1) K : Set (Langlands.GeneralLinear (n + 1 + 1) K))
  have := isMulLeftInvariant_coordinateMeasure χ vol hdet μN'
  have := isFiniteMeasureOnCompacts_coordinateMeasure vol μN'
  exact ⟨_, isMulLeftInvariant_eq_smul _ μN⟩

/-- The coordinate measure of the conjugate `(diag(h,1))⁻¹ x diag(h,1) ∈ J` condition:
the column fibres are translates of `Y₀ = col⁻¹ J` under `h`, and the block condition
is `h⁻¹ u h ∈ level J`. -/
theorem coordinateMeasure_conj (χ : K →*₀ ℝ≥0) (vol : Measure (Fin (n + 1) → K))
    [SFinite vol] [vol.IsAddRightInvariant]
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, M.det ≠ 0 →
      vol.map (Matrix.toLin' M) = (χ M.det)⁻¹ • vol)
    (μN' : Measure (GeneralLinear.upperUnipotent (n + 1) K)) [SFinite μN']
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (h : Langlands.GeneralLinear (n + 1) K) :
    coordinateMeasure vol μN'
        {x | (rankInclusion 1 h)⁻¹ * x.val * rankInclusion 1 h ∈ J} =
      (χ h.val.det : ℝ≥0∞) * vol (col ⁻¹' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) *
        μN' {u | h⁻¹ * u.val * h ∈ levelOpen J} := by
  have hS : MeasurableSet {x : GeneralLinear.upperUnipotent (n + 1 + 1) K |
      (rankInclusion 1 h)⁻¹ * x.val * rankInclusion 1 h ∈ J} :=
    (J.isOpen.preimage ((continuous_const.mul continuous_subtype_val).mul
      continuous_const)).measurableSet
  have hA : MeasurableSet {u : GeneralLinear.upperUnipotent (n + 1) K |
      h⁻¹ * u.val * h ∈ levelOpen J} :=
    ((levelOpen J).isOpen.preimage ((continuous_const.mul continuous_subtype_val).mul
      continuous_const)).measurableSet
  have hY : MeasurableSet (col ⁻¹' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) :=
    (J.isOpen.preimage continuous_col).measurableSet
  have hpre : unipotentCoordinates ⁻¹' {x : GeneralLinear.upperUnipotent (n + 1 + 1) K |
      (rankInclusion 1 h)⁻¹ * x.val * rankInclusion 1 h ∈ J} =
      {p | col ((h⁻¹).val.mulVec p.1) * rankInclusion 1 (h⁻¹ * p.2.val * h) ∈ J} := by
    ext ⟨v, u⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, unipotentCoordinates_apply_val,
      conj_col_mul_rankInclusion]
  have hdeth : χ (h⁻¹).val.det * χ h.val.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one, map_one]
  have hfib (u : GeneralLinear.upperUnipotent (n + 1) K) :
      vol ((fun v => (v, u)) ⁻¹'
        {p : (Fin (n + 1) → K) × GeneralLinear.upperUnipotent (n + 1) K |
          col ((h⁻¹).val.mulVec p.1) * rankInclusion 1 (h⁻¹ * p.2.val * h) ∈ J}) =
      {u : GeneralLinear.upperUnipotent (n + 1) K | h⁻¹ * u.val * h ∈ levelOpen J}.indicator
        (fun _ => (χ h.val.det : ℝ≥0∞) *
          vol (col ⁻¹' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K)))) u := by
    by_cases ha : h⁻¹ * u.val * h ∈ levelOpen J
    · rw [Set.indicator_of_mem (show u ∈ {u : GeneralLinear.upperUnipotent (n + 1) K |
        h⁻¹ * u.val * h ∈ levelOpen J} from ha)]
      obtain ⟨w₀, hw₀⟩ := mem_levelOpen.mp ha
      have hset : (fun v => (v, u)) ⁻¹'
          {p : (Fin (n + 1) → K) × GeneralLinear.upperUnipotent (n + 1) K |
            col ((h⁻¹).val.mulVec p.1) * rankInclusion 1 (h⁻¹ * p.2.val * h) ∈ J} =
          Matrix.toLin' (h⁻¹).val ⁻¹' ((· + -w₀) ⁻¹'
            (col ⁻¹' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K)))) := by
        ext v
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Matrix.toLin'_apply, SetLike.mem_coe]
        rw [← sub_eq_add_neg]
        exact col_mul_mem_iff (J := J.toSubgroup) hw₀ _
      have hmeas : Measurable (Matrix.toLin' (h⁻¹).val) :=
        (LinearMap.continuous_on_pi _).measurable
      rw [hset, ← Measure.map_apply hmeas ((measurable_add_const _) hY),
        hdet _ ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero,
        Measure.smul_apply, measure_preimage_add_right,
        inv_eq_of_mul_eq_one_left (by rw [mul_comm]; exact hdeth), ENNReal.smul_def,
        smul_eq_mul]
    · rw [Set.indicator_of_notMem (show u ∉ {u : GeneralLinear.upperUnipotent (n + 1) K |
        h⁻¹ * u.val * h ∈ levelOpen J} from ha)]
      convert measure_empty (μ := vol)
      ext v
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hv => ha (mem_levelOpen.mpr ⟨_, hv⟩)
  unfold coordinateMeasure
  rw [Measure.map_apply measurable_unipotentCoordinates hS, hpre,
    Measure.prod_apply_symm (hpre ▸ hS.preimage measurable_unipotentCoordinates)]
  simp_rw [hfib]
  rw [lintegral_indicator_const hA]

end HaarFiber

section Orbits

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

/-- `h ~ h'` when `h' ∈ N_(n+1) h A`, where `A` is the level of `J`. -/
def orbitSetoid (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)) :
    Setoid (Langlands.GeneralLinear (n + 1) K) where
  r h h' := ∃ u : GeneralLinear.upperUnipotent (n + 1) K, ∃ a ∈ levelOpen J,
    h' = u.val * h * a
  iseqv := {
    refl := fun h => ⟨1, 1, one_mem _, by simp⟩
    symm := by
      rintro h h' ⟨u, a, ha, rfl⟩
      refine ⟨u⁻¹, a⁻¹, inv_mem ha, ?_⟩
      simp only [InvMemClass.coe_inv]
      group
    trans := by
      rintro h h' h'' ⟨u, a, ha, rfl⟩ ⟨u', a', ha', rfl⟩
      refine ⟨u' * u, a * a', mul_mem ha ha', ?_⟩
      simp only [Subgroup.coe_mul]
      group }

theorem exists_eq_of_orbitRel {J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)}
    {h h' : Langlands.GeneralLinear (n + 1) K} (hr : orbitSetoid J h h') :
    ∃ x : GeneralLinear.upperUnipotent (n + 1 + 1) K, ∃ k ∈ J,
      rankInclusion 1 h' = x.val * rankInclusion 1 h * k := by
  obtain ⟨u, a, ha, rfl⟩ := hr
  obtain ⟨w, hw⟩ := mem_levelOpen.mp ha
  refine ⟨⟨rankInclusion 1 u.val * col (-(h.val.mulVec w)),
    mul_mem (rankInclusion_mem u) (col_mem _)⟩, col w * rankInclusion 1 a, hw, ?_⟩
  have e := rankInclusion_mul_col h w
  simp only [col_neg, map_mul, mul_assoc]
  rw [← mul_assoc (rankInclusion 1 h) (col w), e]
  group

theorem orbitRel_of_eq {J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)}
    {h h' : Langlands.GeneralLinear (n + 1) K}
    {x : GeneralLinear.upperUnipotent (n + 1 + 1) K}
    {k k' : Langlands.GeneralLinear (n + 1 + 1) K} (hk : k ∈ J) (hk' : k' ∈ J)
    (he : rankInclusion 1 h' * k' = x.val * rankInclusion 1 h * k) :
    orbitSetoid J h h' := by
  obtain ⟨v, u, hx⟩ := exists_col_mul_rankInclusion x.val x.property
  have hmem : (rankInclusion 1 h')⁻¹ * (col v * rankInclusion 1 u.val) * rankInclusion 1 h ∈ J := by
    have : (rankInclusion 1 h')⁻¹ * (col v * rankInclusion 1 u.val) * rankInclusion 1 h =
        k' * k⁻¹ := by
      rw [← hx, eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, ← mul_assoc x.val, ← he,
        inv_mul_cancel_left]
    rw [this]
    exact mul_mem hk' (inv_mem hk)
  rw [conj_col_mul_rankInclusion'] at hmem
  have ha : h'⁻¹ * u.val * h ∈ levelOpen J := mem_levelOpen.mpr ⟨_, hmem⟩
  refine ⟨u, (h'⁻¹ * u.val * h)⁻¹, inv_mem ha, ?_⟩
  group

/-- The classes of `orbitSetoid` are open. -/
theorem isOpen_orbitClass (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (i : Quotient (orbitSetoid J)) :
    IsOpen {g : Langlands.GeneralLinear (n + 1) K | Quotient.mk (orbitSetoid J) g = i} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(g⁻¹ * ·) ⁻¹' (levelOpen J : Set (Langlands.GeneralLinear (n + 1) K)), ?_,
    (levelOpen J).isOpen.preimage (continuous_const.mul continuous_id), by simp⟩
  intro g' hg'
  change Quotient.mk (orbitSetoid J) g' = i
  rw [← hg]
  exact (Quotient.sound (s := orbitSetoid J) (a := g) (b := g')
    ⟨1, g⁻¹ * g', hg', by simp⟩).symm

/-- There are countably many classes. -/
theorem countable_orbitQuotient [SecondCountableTopology (Langlands.GeneralLinear (n + 1) K)]
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)) :
    Countable (Quotient (orbitSetoid J)) := by
  refine Pairwise.countable_of_isOpen_disjoint
    (s := fun i => {g : Langlands.GeneralLinear (n + 1) K | Quotient.mk (orbitSetoid J) g = i})
    ?_ (isOpen_orbitClass J) ?_
  · intro i i' hii'
    rw [Function.onFun, Set.disjoint_left]
    intro g hg hg'
    exact hii' (hg.symm.trans hg')
  · intro i
    exact ⟨i.out, Quotient.out_eq i⟩

end Orbits

section OrbitMass

open scoped ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The orbit image `q(g K)` of an open subgroup is open in the left quotient. -/
theorem isOpen_orbit (H : Subgroup G) (K : OpenSubgroup G) (g : G) :
    IsOpen ((fun k : G => leftQuotientMap H (g * k)) '' (K : Set G)) := by
  have : (fun k : G => leftQuotientMap H (g * k)) '' (K : Set G) =
      leftQuotientMap H '' ((g * ·) '' (K : Set G)) := by
    rw [Set.image_image]
  rw [this]
  exact (leftQuotient_isOpenQuotientMap H).isOpenMap _ ((isOpenMap_mul_left g) _ K.isOpen)

variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

set_option linter.overlappingInstances false in
/-- The mass of a compact-open orbit for a compatible quotient measure. -/
theorem orbit_measure (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μG : Measure G) (μH : Measure H)
    [Measure.IsHaarMeasure μG] [μG.Regular]
    [Measure.IsHaarMeasure μH] [μH.Regular] [Measure.IsMulRightInvariant μH]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (μ : Measure (LeftQuotient H)) (hμ : IsCompatible H μG μH μ) (g : G) :
    0 < μH {h : H | g⁻¹ * (h : G) * g ∈ K} ∧ μH {h : H | g⁻¹ * (h : G) * g ∈ K} < ⊤ ∧
      μ ((fun k : G => leftQuotientMap H (g * k)) '' (K : Set G)) =
        (μH {h : H | g⁻¹ * (h : G) * g ∈ K})⁻¹ * μG K := by
  have hres := compactOpenOrbitMeasure H hH μG μH K hK μ hμ g
  dsimp only at hres
  obtain ⟨hc0, hctop, hres⟩ := hres
  refine ⟨hc0, hctop, ?_⟩
  have hp : Measurable (fun k : G => leftQuotientMap H (g * k)) :=
    ((leftQuotient_isOpenQuotientMap H).continuous.comp
      (continuous_const.mul continuous_id)).measurable
  have hCm : MeasurableSet ((fun k : G => leftQuotientMap H (g * k)) '' (K : Set G)) :=
    (isOpen_orbit H K g).measurableSet
  have := DFunLike.congr_fun hres ((fun k : G => leftQuotientMap H (g * k)) '' (K : Set G))
  rw [Measure.restrict_apply_self, Measure.smul_apply, Measure.map_apply hp hCm,
    Measure.restrict_apply (hp hCm), Set.inter_eq_right.mpr ?_, smul_eq_mul] at this
  · exact this
  · intro k hk
    exact ⟨k, hk, rfl⟩

end OrbitMass

section LocallyConstant

/-- A function invariant under right translation by an open subgroup is continuous. -/
theorem continuous_of_rightInvariant {G Y : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace Y] (J : OpenSubgroup G) (f : G → Y)
    (hf : ∀ x, ∀ j ∈ J, f (x * j) = f x) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  have hn : (x * ·) '' (J : Set G) ∈ nhds x :=
    ((isOpenMap_mul_left x) _ J.isOpen).mem_nhds ⟨1, one_mem J, mul_one x⟩
  refine (continuousAt_const : ContinuousAt (fun _ : G => f x) x).congr ?_
  filter_upwards [hn]
  rintro _ ⟨j, hj, rfl⟩
  exact (hf x j hj).symm

/-- Descent of a continuous function to the left quotient is continuous. -/
theorem continuous_descend {G Y : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace Y] (H : Subgroup G) (f : G → Y)
    (hf : ∀ h : H, ∀ g, f (h.val * g) = f g) (hc : Continuous f) :
    Continuous (descend H f hf) :=
  (leftQuotient_isOpenQuotientMap H).isQuotientMap.continuous_iff.mpr hc

end LocallyConstant

section Compare

/-- Two piecewise-constant functions on countable disjoint families whose termwise
contributions differ by the factor `C > 0`. -/
theorem piecewiseConstant_compare {X X' : Type*} [MeasurableSpace X] [MeasurableSpace X']
    (μ : Measure X) (μ' : Measure X') {ι : Type*} [Countable ι]
    (E : ι → Set X) (E' : ι → Set X') (hE : ∀ i, MeasurableSet (E i))
    (hE' : ∀ i, MeasurableSet (E' i)) (hd : Pairwise (Function.onFun Disjoint E))
    (hd' : Pairwise (Function.onFun Disjoint E')) (hfin : ∀ i, μ (E i) ≠ ⊤)
    (hfin' : ∀ i, μ' (E' i) ≠ ⊤) (f : X → ℂ) (f' : X' → ℂ)
    (hf : AEStronglyMeasurable f μ) (hf' : AEStronglyMeasurable f' μ') (a a' : ι → ℂ)
    (ha : ∀ i, ∀ x ∈ E i, f x = a i) (ha' : ∀ i, ∀ x ∈ E' i, f' x = a' i)
    (h0 : ∀ x, (∀ i, x ∉ E i) → f x = 0) (h0' : ∀ x, (∀ i, x ∉ E' i) → f' x = 0)
    (C : ℝ) (hC : 0 < C)
    (hterm : ∀ i, μ.real (E i) • a i = (C : ℂ) * (μ'.real (E' i) • a' i)) :
    (Integrable f μ ↔ Integrable f' μ') ∧ ∫ x, f x ∂μ = (C : ℂ) * ∫ x, f' x ∂μ' := by
  obtain ⟨hi, hint⟩ := piecewiseConstant_integral μ E hE hd hfin f hf a ha h0
  obtain ⟨hi', hint'⟩ := piecewiseConstant_integral μ' E' hE' hd' hfin' f' hf' a' ha' h0'
  have hnorm : ∀ i, ‖a i‖ * μ.real (E i) = C * (‖a' i‖ * μ'.real (E' i)) := by
    intro i
    have := congrArg norm (hterm i)
    simp only [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg measureReal_nonneg, abs_of_pos hC] at this
    linear_combination this
  have hiff : Integrable f μ ↔ Integrable f' μ' := by
    rw [hi, hi']
    simp_rw [hnorm]
    exact summable_mul_left_iff hC.ne'
  refine ⟨hiff, ?_⟩
  by_cases hfi : Integrable f μ
  · rw [hint hfi, hint' (hiff.mp hfi), ← tsum_mul_left]
    exact tsum_congr hterm
  · rw [integral_undef hfi, integral_undef (fun h => hfi (hiff.mpr h)), mul_zero]

end Compare


section Invariance

open HarmonicAnalysis Whittaker
open scoped NNReal

variable {K : Type*} [Field K] [TopologicalSpace K] {n : ℕ}

omit [TopologicalSpace K] in
/-- `diag(g, 1)` has the determinant of `g`. -/
theorem rankInclusion_det (g : Langlands.GeneralLinear (n + 1) K) :
    Matrix.det (rankInclusion 1 g).val = Matrix.det g.val := by
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g.val 0 0 (1 : Langlands.GeneralLinear 1 K).val)) = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Units.val_one, Matrix.det_one,
    mul_one]

omit [TopologicalSpace K] in
theorem det_col_mul (w : Fin (n + 1) → K) (a : Langlands.GeneralLinear (n + 1) K) :
    Matrix.det (col w * rankInclusion 1 a).val = Matrix.det a.val := by
  rw [Units.val_mul, Matrix.det_mul, rankInclusion_det]
  have : Matrix.det (col w).val = 1 := unipotent_det ⟨col w, col_mem w⟩
  rw [this, one_mul]

omit [TopologicalSpace K] in
theorem rankInclusion_mul_eq (h a : Langlands.GeneralLinear (n + 1) K) (w : Fin (n + 1) → K) :
    rankInclusion 1 (h * a) =
      col (h.val.mulVec (-w)) * (rankInclusion 1 h * (col w * rankInclusion 1 a)) := by
  rw [← mul_assoc (rankInclusion 1 h), rankInclusion_mul_col, Matrix.mulVec_neg, col_neg,
    map_mul]
  group

omit [TopologicalSpace K] in
/-- Right translation by `J` preserves membership in the last-row orbit of `J`. -/
theorem lastRow_mul_mem_iff {m : ℕ} (J : Subgroup (Langlands.GeneralLinear (m + 1) K))
    (g j : Langlands.GeneralLinear (m + 1) K) (hj : j ∈ J) :
    lastRow (g * j) ∈ lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) K)) ↔
      lastRow g ∈ lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) K)) := by
  constructor
  · rintro ⟨k, hk, hkg⟩
    refine ⟨k * j⁻¹, mul_mem hk (inv_mem hj), ?_⟩
    rw [lastRow_mul_eq_vecMul, hkg, ← lastRow_mul_eq_vecMul, mul_inv_cancel_right]
  · rintro ⟨k, hk, hkg⟩
    exact ⟨k * j, mul_mem hk hj, by rw [lastRow_mul_eq_vecMul, hkg, ← lastRow_mul_eq_vecMul]⟩

omit [TopologicalSpace K] in
/-- `diag(r, 1) k` lies in the last-row orbit for `k ∈ J`. -/
theorem lastRow_rankInclusion_mul_mem (J : Subgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (r : Langlands.GeneralLinear (n + 1) K) {k : Langlands.GeneralLinear (n + 1 + 1) K}
    (hk : k ∈ J) :
    lastRow (rankInclusion 1 r * k) ∈
      lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K)) :=
  (lastRow_mem_image_iff J _).mpr ⟨levi r, ⟨k, hk⟩, rfl⟩

variable [IsTopologicalRing K]

theorem level_det_eq_one (χ : K →*₀ ℝ≥0)
    {J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)}
    (hJ1 : ∀ j ∈ J, χ (Matrix.det j.val) = 1) {a : Langlands.GeneralLinear (n + 1) K}
    (ha : a ∈ levelOpen J) : χ (Matrix.det a.val) = 1 := by
  obtain ⟨w, hw⟩ := mem_levelOpen.mp ha
  rw [← det_col_mul w a]
  exact hJ1 _ hw

/-- The product `W(diag(h,1)) W'(diag(h,1))` is right invariant under the level of `J`. -/
theorem whittaker_level_invariant (ψ : UnitaryAdditiveCharacter K)
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ (n + 1))
    (hW : ∀ (g : Langlands.GeneralLinear (n + 1 + 1) K) (j : J), W.val (g * j.val) = W.val g)
    (hW' : ∀ (g : Langlands.GeneralLinear (n + 1 + 1) K) (j : J),
      W'.val (g * j.val) = W'.val g)
    (h : Langlands.GeneralLinear (n + 1) K) {a : Langlands.GeneralLinear (n + 1) K}
    (ha : a ∈ levelOpen J) :
    W.val (rankInclusion 1 (h * a)) * W'.val (rankInclusion 1 (h * a)) =
      W.val (rankInclusion 1 h) * W'.val (rankInclusion 1 h) := by
  obtain ⟨w, hw⟩ := mem_levelOpen.mp ha
  rw [rankInclusion_mul_eq h a w]
  have h0 : W.val (col (h.val.mulVec (-w)) * (rankInclusion 1 h * (col w * rankInclusion 1 a))) *
      W'.val (col (h.val.mulVec (-w)) * (rankInclusion 1 h * (col w * rankInclusion 1 a))) =
      W.val (rankInclusion 1 h * (col w * rankInclusion 1 a)) *
        W'.val (rankInclusion 1 h * (col w * rankInclusion 1 a)) :=
    whittaker_product_invariant ψ W W' ⟨_, col_mem (h.val.mulVec (-w))⟩ _
  have h1 : W.val (rankInclusion 1 h * (col w * rankInclusion 1 a)) =
      W.val (rankInclusion 1 h) := hW _ ⟨_, hw⟩
  have h2 : W'.val (rankInclusion 1 h * (col w * rankInclusion 1 a)) =
      W'.val (rankInclusion 1 h) := hW' _ ⟨_, hw⟩
  rw [h0, h1, h2]

/-- The corank-one function is right invariant under the level of `J`. -/
theorem corankOneFunction_level_invariant (ψ : UnitaryAdditiveCharacter K)
    (abv : AbsoluteValue K ℝ) (χ : K →*₀ ℝ≥0) (habv : ∀ x, abv x = χ x)
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (hJ1 : ∀ j ∈ J, χ (Matrix.det j.val) = 1)
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ (n + 1))
    (W'' : InverseWhittakerFunctions ψ n)
    (hW : ∀ (g : Langlands.GeneralLinear (n + 1 + 1) K) (j : J), W.val (g * j.val) = W.val g)
    (hW' : ∀ (g : Langlands.GeneralLinear (n + 1 + 1) K) (j : J),
      W'.val (g * j.val) = W'.val g)
    (hW'' : ∀ h : Langlands.GeneralLinear (n + 1) K, W''.val h = W'.val (rankInclusion 1 h))
    (s : ℂ) (h : Langlands.GeneralLinear (n + 1) K) {a : Langlands.GeneralLinear (n + 1) K}
    (ha : a ∈ levelOpen J) :
    corankOneFunction ψ abv W W'' s (h * a) = corankOneFunction ψ abv W W'' s h := by
  unfold corankOneFunction determinantWeight
  rw [hW'' (h * a), hW'' h, whittaker_level_invariant ψ J W W' hW hW' h ha, Units.val_mul,
    Matrix.det_mul, map_mul, habv (Matrix.det a.val), level_det_eq_one χ hJ1 ha]
  simp

omit [IsTopologicalRing K] in
/-- The equal-rank function is right invariant under `J`. -/
theorem equalRankFunction_right_invariant (ψ : UnitaryAdditiveCharacter K)
    (abv : AbsoluteValue K ℝ) (χ : K →*₀ ℝ≥0) (habv : ∀ x, abv x = χ x)
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (hJ1 : ∀ j ∈ J, χ (Matrix.det j.val) = 1)
    (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ (n + 1))
    (hW : ∀ (g : Langlands.GeneralLinear (n + 1 + 1) K) (j : J), W.val (g * j.val) = W.val g)
    (hW' : ∀ (g : Langlands.GeneralLinear (n + 1 + 1) K) (j : J),
      W'.val (g * j.val) = W'.val g)
    (Φ : SchwartzBruhat (Fin (n + 1 + 1) → K))
    (hΦ : (Φ : (Fin (n + 1 + 1) → K) → ℂ) =
      (lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))).indicator
        (fun _ => (1 : ℂ)))
    (s : ℂ) (g : Langlands.GeneralLinear (n + 1 + 1) K) (j : J) :
    equalRankFunction ψ abv W W' Φ s (g * j.val) = equalRankFunction ψ abv W W' Φ s g := by
  unfold equalRankFunction determinantWeight
  have hΦj : Φ (lastRow (g * j.val)) = Φ (lastRow g) := by
    have e : lastRow (g * j.val) ∈ lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K)) ↔
        lastRow g ∈ lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K)) :=
      lastRow_mul_mem_iff J.toSubgroup g j.val j.property
    rw [hΦ]
    by_cases hg : lastRow g ∈ lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (e.mpr hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (e.mp h))]
  rw [hW g j, hW' g j, hΦj, Units.val_mul, Matrix.det_mul, map_mul,
    habv (Matrix.det j.val.val), hJ1 j.val j.property]
  simp

end Invariance

section OrbitIndex

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}

/-- The orbit `N_(n+2) \ N_(n+2) diag(r,1) J` in the rank-`(n+2)` quotient. -/
def orbitImage (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (r : Langlands.GeneralLinear (n + 1) K) : Set (LeftUnipotentQuotient (n + 1) K) :=
  (fun k => leftQuotientMap (GeneralLinear.upperUnipotent (n + 1 + 1) K)
    (rankInclusion 1 r * k)) '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))

/-- The orbit `N_(n+1) \ N_(n+1) r A` in the rank-`(n+1)` quotient, `A` the level of `J`. -/
def orbitImage' (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (r : Langlands.GeneralLinear (n + 1) K) : Set (LeftUnipotentQuotient n K) :=
  (fun a => leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) K) (r * a)) ''
    (levelOpen J : Set (Langlands.GeneralLinear (n + 1) K))

/-- A matrix whose last row lies in the last-row orbit of `J` lies, modulo `N_(n+2)`,
in the orbit `diag(r,1) J` of a class representative `r`. -/
theorem exists_orbit_of_lastRow (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (g : Langlands.GeneralLinear (n + 1 + 1) K)
    (hg : lastRow g ∈ lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) :
    ∃ i : Quotient (orbitSetoid J), ∃ k ∈ J,
      leftQuotientMap (GeneralLinear.upperUnipotent (n + 1 + 1) K) g =
        leftQuotientMap (GeneralLinear.upperUnipotent (n + 1 + 1) K)
          (rankInclusion 1 i.out * k) := by
  obtain ⟨p, j, rfl⟩ := (lastRow_mem_image_iff J.toSubgroup g).mp hg
  have hp : p.val = col (lastColumn p) * rankInclusion 1 (projection p) :=
    congrArg Subtype.val (eq_radicalElement_mul_levi p)
  obtain ⟨x, k, hk, hx⟩ := exists_eq_of_orbitRel
    (Quotient.mk_out (s := orbitSetoid J) (projection p))
  refine ⟨Quotient.mk (orbitSetoid J) (projection p), k * j.val, mul_mem hk j.property, ?_⟩
  simp only [leftQuotientMap_apply]
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.mpr ?_
  have e : rankInclusion 1 (Quotient.mk (orbitSetoid J) (projection p)).out * (k * j.val) *
      (p.val * j.val)⁻¹ = (x.val)⁻¹ * (col (lastColumn p))⁻¹ := by
    rw [hp, hx]
    group
  rw [e]
  exact mul_mem (inv_mem x.property) (inv_mem (col_mem _))

/-- Distinct classes give disjoint orbits `N_(n+2) \ N_(n+2) diag(r,1) J`. -/
theorem eq_of_orbit_mk_eq {J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)}
    {i i' : Quotient (orbitSetoid J)} {k k' : Langlands.GeneralLinear (n + 1 + 1) K}
    (hk : k ∈ J) (hk' : k' ∈ J)
    (he : leftQuotientMap (GeneralLinear.upperUnipotent (n + 1 + 1) K)
        (rankInclusion 1 i.out * k) =
      leftQuotientMap (GeneralLinear.upperUnipotent (n + 1 + 1) K)
        (rankInclusion 1 i'.out * k')) : i = i' := by
  simp only [leftQuotientMap_apply] at he
  have hx := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  let x : GeneralLinear.upperUnipotent (n + 1 + 1) K := ⟨_, hx⟩
  have he' : rankInclusion 1 i'.out * k' = x.val * rankInclusion 1 i.out * k := by
    simp only [x]
    group
  have hr := orbitRel_of_eq hk hk' he'
  rw [← Quotient.out_eq i, ← Quotient.out_eq i']
  exact Quotient.sound hr

/-- Distinct classes give disjoint orbits `N_(n+1) \ N_(n+1) r A`. -/
theorem eq_of_orbit'_mk_eq {J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K)}
    {i i' : Quotient (orbitSetoid J)} {a a' : Langlands.GeneralLinear (n + 1) K}
    (ha : a ∈ levelOpen J) (ha' : a' ∈ levelOpen J)
    (he : leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) K) (i.out * a) =
      leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) K) (i'.out * a')) : i = i' := by
  simp only [leftQuotientMap_apply] at he
  have hx := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  have hr : orbitSetoid J i.out i'.out := by
    refine ⟨⟨_, hx⟩, a * a'⁻¹, mul_mem ha (inv_mem ha'), ?_⟩
    simp only
    group
  rw [← Quotient.out_eq i, ← Quotient.out_eq i']
  exact Quotient.sound hr

/-- Every coset of `N_(n+1)` lies in the orbit of its class representative. -/
theorem exists_orbit' (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (h : Langlands.GeneralLinear (n + 1) K) :
    ∃ a ∈ levelOpen J, leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) K) h =
      leftQuotientMap (GeneralLinear.upperUnipotent (n + 1) K)
        ((Quotient.mk (orbitSetoid J) h).out * a) := by
  obtain ⟨u, a, ha, hu⟩ := Quotient.mk_out (s := orbitSetoid J) h
  refine ⟨a, ha, ?_⟩
  generalize (Quotient.mk (orbitSetoid J) h).out = r at hu ⊢
  subst hu
  simp only [leftQuotientMap_apply]
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.mpr ?_
  have e : r * a * (u.val * r * a)⁻¹ = (u.val)⁻¹ := by
    group
  rw [e]
  exact inv_mem u.property

end OrbitIndex

section Main

open HarmonicAnalysis Whittaker
open scoped NNReal ENNReal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [SecondCountableTopology K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}
  [T2Space (Langlands.GeneralLinear (n + 1) K)]
  [LocallyCompactSpace (Langlands.GeneralLinear (n + 1) K)]
  [SecondCountableTopology (Langlands.GeneralLinear (n + 1) K)]
  [T2Space (Langlands.GeneralLinear (n + 1 + 1) K)]
  [LocallyCompactSpace (Langlands.GeneralLinear (n + 1 + 1) K)]
  [SecondCountableTopology (Langlands.GeneralLinear (n + 1 + 1) K)]
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) K)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) K)]
  [MeasurableSpace (Langlands.GeneralLinear (n + 1 + 1) K)]
  [BorelSpace (Langlands.GeneralLinear (n + 1 + 1) K)]
  [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) K)]
  [BorelSpace (GeneralLinear.upperUnipotent (n + 1) K)]
  [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1 + 1) K)]
  [BorelSpace (GeneralLinear.upperUnipotent (n + 1 + 1) K)]
  [MeasurableSpace (LeftUnipotentQuotient n K)] [BorelSpace (LeftUnipotentQuotient n K)]
  [MeasurableSpace (LeftUnipotentQuotient (n + 1) K)]
  [BorelSpace (LeftUnipotentQuotient (n + 1) K)]

set_option linter.overlappingInstances false in
/-- The orbit masses `μ(N \ N diag(r,1) J)` and `μ'(N' \ N' r A)` differ by the factor
`|det r|` up to one positive constant independent of `r`. -/
theorem orbit_mass_relation (χ : K →*₀ ℝ≥0)
    (vol : Measure (Fin (n + 1) → K)) [Measure.IsAddHaarMeasure vol]
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, M.det ≠ 0 →
      vol.map (Matrix.toLin' M) = (χ M.det)⁻¹ • vol)
    (μG : Measure (Langlands.GeneralLinear (n + 1 + 1) K)) [Measure.IsHaarMeasure μG]
    [μG.Regular]
    (μN : Measure (GeneralLinear.upperUnipotent (n + 1 + 1) K)) [Measure.IsHaarMeasure μN]
    [μN.Regular] [Measure.IsMulRightInvariant μN]
    (μG' : Measure (Langlands.GeneralLinear (n + 1) K)) [Measure.IsHaarMeasure μG']
    [μG'.Regular]
    (μN' : Measure (GeneralLinear.upperUnipotent (n + 1) K)) [Measure.IsHaarMeasure μN']
    [μN'.Regular] [Measure.IsMulRightInvariant μN']
    (μ : Measure (LeftUnipotentQuotient (n + 1) K)) (μ' : Measure (LeftUnipotentQuotient n K))
    (hμ : IsCompatible (GeneralLinear.upperUnipotent (n + 1 + 1) K) μG μN μ)
    (hμ' : IsCompatible (GeneralLinear.upperUnipotent (n + 1) K) μG' μN' μ')
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (hJ : IsCompact (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Langlands.GeneralLinear (n + 1) K,
      μ (orbitImage J r) ≠ ⊤ ∧ μ' (orbitImage' J r) ≠ ⊤ ∧
        μ.real (orbitImage J r) * (χ (Matrix.det r.val) : ℝ) = C * μ'.real (orbitImage' J r) := by
  have : LocallyCompactSpace (GeneralLinear.upperUnipotent (n + 1) K) :=
    UpperUnipotent.locallyCompactSpace
  have : SecondCountableTopology (GeneralLinear.upperUnipotent (n + 1) K) :=
    TopologicalSpace.Subtype.secondCountableTopology
      (GeneralLinear.upperUnipotent (n + 1) K : Set (Langlands.GeneralLinear (n + 1) K))
  obtain ⟨κ, hκ⟩ := exists_coordinateMeasure_eq_smul χ vol hdet μN' μN
  have hN : IsClosed (GeneralLinear.upperUnipotent (n + 1 + 1) K :
      Set (Langlands.GeneralLinear (n + 1 + 1) K)) :=
    GeneralLinear.UpperUnipotent.isClosed
  have hN' : IsClosed (GeneralLinear.upperUnipotent (n + 1) K :
      Set (Langlands.GeneralLinear (n + 1) K)) :=
    GeneralLinear.UpperUnipotent.isClosed
  have hA : IsCompact (levelOpen J : Set (Langlands.GeneralLinear (n + 1) K)) :=
    isCompact_level J.toSubgroup hJ
  have hY₀o : IsOpen (col ⁻¹' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) :=
    J.isOpen.preimage continuous_col
  have hvpos : 0 < vol (col ⁻¹' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) :=
    hY₀o.measure_pos vol ⟨0, by simp⟩
  have hO := fun r : Langlands.GeneralLinear (n + 1) K =>
    orbit_measure _ hN μG μN J hJ μ hμ (rankInclusion 1 r)
  have hO' := fun r : Langlands.GeneralLinear (n + 1) K =>
    orbit_measure _ hN' μG' μN' (levelOpen J) hA μ' hμ' r
  have hrel (r : Langlands.GeneralLinear (n + 1) K) :
      (κ : ℝ≥0∞) * μN {x | (rankInclusion 1 r)⁻¹ * x.val * rankInclusion 1 r ∈ J} =
        (χ r.val.det : ℝ≥0∞) *
          vol (col ⁻¹' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) *
          μN' {u | r⁻¹ * u.val * r ∈ levelOpen J} := by
    rw [← coordinateMeasure_conj χ vol hdet μN' J r, hκ, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul]
  have hχ1 : (χ (1 : Langlands.GeneralLinear (n + 1) K).val.det : ℝ≥0∞) = 1 := by simp
  have hvtop : vol (col ⁻¹' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))) ≠ ⊤ := by
    intro htop
    have h := hrel 1
    rw [htop, hχ1, one_mul, ENNReal.top_mul (hO' 1).1.ne'] at h
    exact (ENNReal.mul_lt_top ENNReal.coe_lt_top (hO 1).2.1).ne h
  have hκ0 : (κ : ℝ≥0∞) ≠ 0 := by
    intro h0
    have h := hrel 1
    rw [h0, zero_mul, hχ1, one_mul] at h
    exact (ENNReal.mul_pos hvpos.ne' (hO' 1).1.ne').ne h
  have hJpos : 0 < μG J := J.isOpen.measure_pos μG ⟨1, one_mem J⟩
  have hJtop : μG J < ⊤ := hJ.measure_lt_top
  have hApos : 0 < μG' (levelOpen J) := (levelOpen J).isOpen.measure_pos μG' ⟨1, one_mem _⟩
  have hAtop : μG' (levelOpen J) < ⊤ := hA.measure_lt_top
  have hκr : (0 : ℝ) < κ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (by simpa using hκ0))
  have hJr := ENNReal.toReal_pos hJpos.ne' hJtop.ne
  have hAr := ENNReal.toReal_pos hApos.ne' hAtop.ne
  have hvr := ENNReal.toReal_pos hvpos.ne' hvtop
  refine ⟨κ * (μG J).toReal /
      ((vol (col ⁻¹' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K)))).toReal *
        (μG' (levelOpen J)).toReal),
    div_pos (mul_pos hκr hJr) (mul_pos hvr hAr), fun r => ?_⟩
  obtain ⟨hc0, hctop, hE⟩ := hO r
  obtain ⟨hc0', hctop', hE'⟩ := hO' r
  unfold orbitImage orbitImage'
  refine ⟨?_, ?_, ?_⟩
  · rw [hE]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0.ne') hJtop.ne
  · rw [hE']
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0'.ne') hAtop.ne
  · have key := congrArg ENNReal.toReal (hrel r)
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at key
    have hcr := ENNReal.toReal_pos hc0.ne' hctop.ne
    have hcr' := ENNReal.toReal_pos hc0'.ne' hctop'.ne
    rw [measureReal_def, measureReal_def, hE, hE', ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_inv]
    field_simp
    linear_combination -key

set_option linter.overlappingInstances false in
/-- The last-row reduction for arbitrary compatible Haar data over a locally compact field:
the two integrals are sums over the orbit classes, termwise proportional. -/
theorem lastRowReduction (χ : K →*₀ ℝ≥0) (abv : AbsoluteValue K ℝ) (habv : ∀ x, abv x = χ x)
    (vol : Measure (Fin (n + 1) → K)) [Measure.IsAddHaarMeasure vol]
    (hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K, M.det ≠ 0 →
      vol.map (Matrix.toLin' M) = (χ M.det)⁻¹ • vol)
    (μG : Measure (Langlands.GeneralLinear (n + 1 + 1) K)) [Measure.IsHaarMeasure μG]
    [μG.Regular]
    (μN : Measure (GeneralLinear.upperUnipotent (n + 1 + 1) K)) [Measure.IsHaarMeasure μN]
    [μN.Regular] [Measure.IsMulRightInvariant μN]
    (μG' : Measure (Langlands.GeneralLinear (n + 1) K)) [Measure.IsHaarMeasure μG']
    [μG'.Regular]
    (μN' : Measure (GeneralLinear.upperUnipotent (n + 1) K)) [Measure.IsHaarMeasure μN']
    [μN'.Regular] [Measure.IsMulRightInvariant μN']
    (μ : Measure (LeftUnipotentQuotient (n + 1) K)) (μ' : Measure (LeftUnipotentQuotient n K))
    (hμ : IsCompatible (GeneralLinear.upperUnipotent (n + 1 + 1) K) μG μN μ)
    (hμ' : IsCompatible (GeneralLinear.upperUnipotent (n + 1) K) μG' μN' μ')
    (J : OpenSubgroup (Langlands.GeneralLinear (n + 1 + 1) K))
    (hJ : IsCompact (J : Set (Langlands.GeneralLinear (n + 1 + 1) K)))
    (hJ1 : ∀ j ∈ J, χ (Matrix.det j.val) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ψ : UnitaryAdditiveCharacter K)
        (W : WhittakerFunctions ψ (n + 1)) (W' : InverseWhittakerFunctions ψ (n + 1))
        (W'' : InverseWhittakerFunctions ψ n)
        (Φ : SchwartzBruhat (Fin (n + 1 + 1) → K)),
        (∀ (g : Langlands.GeneralLinear (n + 1 + 1) K) (j : J),
          W.val (g * j.val) = W.val g) →
        (∀ (g : Langlands.GeneralLinear (n + 1 + 1) K) (j : J),
          W'.val (g * j.val) = W'.val g) →
        (∀ h : Langlands.GeneralLinear (n + 1) K,
          W''.val h = W'.val (rankInclusion 1 h)) →
        (Φ : (Fin (n + 1 + 1) → K) → ℂ) =
          (lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))).indicator
            (fun _ => (1 : ℂ)) →
        ∀ s : ℂ,
          (EqualRankConverges ψ abv μ W W' Φ s ↔
            CorankOneConverges ψ abv μ' W W'' (s - 1 / 2)) ∧
          equalRankIntegral ψ abv μ W W' Φ s =
            (c : ℂ) * corankOneIntegral ψ abv μ' W W'' (s - 1 / 2) := by
  obtain ⟨C, hC, hmass⟩ := orbit_mass_relation χ vol hdet μG μN μG' μN' μ μ' hμ hμ' J hJ
  refine ⟨C, hC, ?_⟩
  intro ψ W W' W'' Φ hW hW' hW'' hΦ s
  have := countable_orbitQuotient J
  have hinv : ∀ x, ∀ j ∈ J,
      equalRankFunction ψ abv W W' Φ s (x * j) = equalRankFunction ψ abv W W' Φ s x :=
    fun x j hj => equalRankFunction_right_invariant ψ abv χ habv J hJ1 W W' hW hW' Φ hΦ s x
      ⟨j, hj⟩
  have hinv' : ∀ x, ∀ a ∈ levelOpen J,
      corankOneFunction ψ abv W W'' (s - 1 / 2) (x * a) =
        corankOneFunction ψ abv W W'' (s - 1 / 2) x :=
    fun x a ha => corankOneFunction_level_invariant ψ abv χ habv J hJ1 W W' W'' hW hW' hW''
      (s - 1 / 2) x ha
  have hcont : Continuous (equalRankIntegrand ψ abv W W' Φ s) :=
    continuous_descend _ _ _ (continuous_of_rightInvariant J _ hinv)
  have hcont' : Continuous (corankOneIntegrand ψ abv W W'' (s - 1 / 2)) :=
    continuous_descend _ _ _ (continuous_of_rightInvariant (levelOpen J) _ hinv')
  have hterm (r : Langlands.GeneralLinear (n + 1) K) :
      μ.real (orbitImage J r) • equalRankFunction ψ abv W W' Φ s (rankInclusion 1 r) =
        (C : ℂ) * (μ'.real (orbitImage' J r) •
          corankOneFunction ψ abv W W'' (s - 1 / 2) r) := by
    obtain ⟨-, -, hrelr⟩ := hmass r
    have hrelC : (μ.real (orbitImage J r) : ℂ) * (abv (Matrix.det r.val) : ℂ) =
        (C : ℂ) * (μ'.real (orbitImage' J r) : ℂ) := by
      rw [habv]
      exact_mod_cast hrelr
    have hd0 : Matrix.det r.val ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero
    have habs0 : (abv (Matrix.det r.val) : ℂ) ≠ 0 := by
      exact_mod_cast (abv.pos hd0).ne'
    have hm : lastRow (rankInclusion 1 r * 1) ∈
        lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K)) :=
      lastRow_rankInclusion_mul_mem J.toSubgroup r (one_mem J.toSubgroup)
    rw [mul_one] at hm
    have hΦ1 : Φ (lastRow (rankInclusion 1 r)) = 1 := by
      rw [hΦ, Set.indicator_of_mem hm]
    have hpow : (abv (Matrix.det r.val) : ℂ) ^ s =
        (abv (Matrix.det r.val) : ℂ) ^ (s - 1 / 2 - 1 / 2) * (abv (Matrix.det r.val) : ℂ) := by
      conv_lhs => rw [show s = (s - 1 / 2 - 1 / 2) + 1 by ring]
      rw [Complex.cpow_add _ _ habs0, Complex.cpow_one]
    simp only [Complex.real_smul]
    unfold equalRankFunction corankOneFunction determinantWeight
    rw [hΦ1, rankInclusion_det, hW'' r, hpow]
    linear_combination (W.val (rankInclusion 1 r) * W'.val (rankInclusion 1 r) *
      (abv (Matrix.det r.val) : ℂ) ^ (s - 1 / 2 - 1 / 2)) * hrelC
  unfold EqualRankConverges CorankOneConverges equalRankIntegral corankOneIntegral
  refine piecewiseConstant_compare μ μ' (fun i : Quotient (orbitSetoid J) => orbitImage J i.out)
    (fun i => orbitImage' J i.out) (fun i => (isOpen_orbit _ J _).measurableSet)
    (fun i => (isOpen_orbit _ (levelOpen J) _).measurableSet) ?_ ?_
    (fun i => (hmass i.out).1) (fun i => (hmass i.out).2.1)
    (equalRankIntegrand ψ abv W W' Φ s) (corankOneIntegrand ψ abv W W'' (s - 1 / 2))
    hcont.aestronglyMeasurable hcont'.aestronglyMeasurable
    (fun i => equalRankFunction ψ abv W W' Φ s (rankInclusion 1 i.out))
    (fun i => corankOneFunction ψ abv W W'' (s - 1 / 2) i.out) ?_ ?_ ?_ ?_ C hC
    (fun i => hterm i.out)
  · intro i i' hii'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨k, hk, rfl⟩ ⟨k', hk', he⟩
    exact hii' (eq_of_orbit_mk_eq hk hk' he.symm)
  · intro i i' hii'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨a', ha', he⟩
    exact hii' (eq_of_orbit'_mk_eq ha ha' he.symm)
  · rintro i _ ⟨k, hk, rfl⟩
    exact hinv _ k hk
  · rintro i _ ⟨a, ha, rfl⟩
    exact hinv' _ a ha
  · intro x hx
    obtain ⟨g, rfl⟩ := Quotient.exists_rep x
    by_cases hg : lastRow g ∈ lastRow '' (J : Set (Langlands.GeneralLinear (n + 1 + 1) K))
    · obtain ⟨i, k, hk, he⟩ := exists_orbit_of_lastRow J g hg
      exact (hx i ⟨k, hk, he.symm⟩).elim
    · change equalRankFunction ψ abv W W' Φ s g = 0
      unfold equalRankFunction
      rw [hΦ, Set.indicator_of_notMem hg]
      simp
  · intro x hx
    obtain ⟨g, rfl⟩ := Quotient.exists_rep x
    obtain ⟨a, ha, he⟩ := exists_orbit' J g
    exact (hx _ ⟨a, ha, he.symm⟩).elim

end Main

end LastRowReduction

open MeasureTheory GeneralLinear QuotientIntegration LastRowReduction

universe uF

set_option linter.overlappingInstances false in
/-- The last-row reduction over a `p`-adic field: specialize the general theorem to
`χ = |·|_F`, additive Haar measure on the last column, and the normalized Haar measures. -/
theorem equalRankLastRowReduction {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) : EqualRankLastRowReductionStatement F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have := T.generalLinearT2Space (n + 1)
  have := T.generalLinearLocallyCompactSpace (n + 1)
  have := T.generalLinearSecondCountableTopology (n + 1)
  have := T.generalLinearT2Space (n + 1 + 1)
  have := T.generalLinearLocallyCompactSpace (n + 1 + 1)
  have := T.generalLinearSecondCountableTopology (n + 1 + 1)
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1 + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (n + 1 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1 + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (n + 1) F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient (n + 1) F.Carrier) := ⟨rfl⟩
  intro _ _ μ μ' hμ hμ' J hJ
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier, M.det ≠ 0 →
      (Measure.addHaar : Measure (Fin (n + 1) → F.Carrier)).map (Matrix.toLin' M) =
        (T.normalizedAbsHom M.det)⁻¹ • Measure.addHaar :=
    fun M hM => HarmonicAnalysis.haarMeasure_map_matrix (Measure.addHaar : Measure F.Carrier)
      T.normalizedAbsHom hχ _ hM
  have hJ1 : ∀ j ∈ J, T.normalizedAbsHom (Matrix.det j.val) = 1 := by
    intro j hj
    have h := eq_one_of_isCompact (T.determinantNorm (n + 1 + 1))
      (T.determinantNormContinuous (n + 1 + 1)).continuous J.toSubgroup hJ hj
    exact congrArg Units.val h
  exact lastRowReduction T.normalizedAbsHom (normalizedAbsoluteValue T) (fun _ => rfl)
    Measure.addHaar hdet (generalLinearHaar F.Carrier (n + 1)) (unipotentHaar F.Carrier (n + 1))
    (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ μ' hμ hμ' J hJ hJ1

end Langlands.RankinSelberg
