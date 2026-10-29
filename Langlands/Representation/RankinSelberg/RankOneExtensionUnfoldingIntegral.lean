import Langlands.Representation.RankinSelberg.RankOneExtensionCellTopology
import Langlands.Representation.RankinSelberg.RankOneExtensionUnfoldingMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integral form of the open-cell exchange

For a function `Ψ` on `(H \ GL_(t+1)) × GL_(1+(t+1))` that is compatible with right
translation by the lower blocks `B(r, 0, 1)`, the integral of
`Ψ(q, u(y) B(1, x, h))` equals the integral of `w(h) Ψ(q, B(1, x, h) u(y))`, where
`w(h)` is the scaling factor of the row measure under `y ↦ h y`. This is the change of
variables of JPSS (1983), Lemma 5.5, in integral form.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Matrix GeneralLinear QuotientIntegration
open scoped ENNReal NNReal

section Cells

variable {K : Type*} [Field K] {t : ℕ}

/-- The entry of an element of `B⁻_1`, as a unit. -/
def lowerScalarUnit (h : lowerTriangularSubgroup 1 K) : Kˣ :=
  Units.mk0 (lowerScalarEntry h) (lowerScalarEntry_ne_zero h)

@[simp] theorem lowerScalarUnit_val (h : lowerTriangularSubgroup 1 K) :
    (lowerScalarUnit h : K) = lowerScalarEntry h := rfl

theorem lowerScalarUnit_mul (h h' : lowerTriangularSubgroup 1 K) :
    lowerScalarUnit (h * h') = lowerScalarUnit h * lowerScalarUnit h' :=
  Units.ext (lowerScalarEntry_mul h h')

@[simp] theorem rankOneExtensionLowerBlock_one_zero_one :
    rankOneExtensionLowerBlock t (1 : Langlands.GeneralLinear (t + 1) K) 0 1 = 1 := by
  apply rankOneExtensionCellBlocks_injective
  rw [rankOneExtensionCellBlocks_lowerBlock]
  simp only [rankOneExtensionCellBlocks, map_one, Units.val_one]
  rw [← Matrix.fromBlocks_one]
  congr 1
  ext i j
  rw [Subsingleton.elim i j]
  simp

theorem rankOneExtensionLowerBlock_one_inv (x : Fin (t + 1) → K) (a : Kˣ) :
    (rankOneExtensionLowerBlock t 1 x a)⁻¹ =
      rankOneExtensionLowerBlock t 1 (-((a⁻¹ : Kˣ) : K) • x) a⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  rw [rankOneExtensionLowerBlock_mul]
  convert rankOneExtensionLowerBlock_one_zero_one (K := K) (t := t) using 2
  · simp
  · simp [smul_smul]
  · simp

/-- The lower cell `B(1, x, h) = [I, 0; x, h]`, for a `1 × (t + 1)` row matrix `x` and
`h ∈ B⁻_1`. -/
def rankOneExtensionLowerCell (x : Matrix (Fin 1) (Fin (t + 1)) K)
    (h : lowerTriangularSubgroup 1 K) : Langlands.GeneralLinear (1 + (t + 1)) K :=
  rankOneExtensionLowerBlock t 1 (x 0) (lowerScalarUnit h)

/-- The open-cell exchange `u(y) B(1, x, h) = B(r, 0, 1) B(1, x, h') u(h' y)`, with
`r = I + y x`, `s = 1 + x · y ≠ 0` and `h' = h s⁻¹`. -/
theorem rankOneExtensionUpperCell_mul_lowerCell (x : Matrix (Fin 1) (Fin (t + 1)) K)
    (y : Fin (t + 1) → K) (h : lowerTriangularSubgroup 1 K) (hs : 1 + x 0 ⬝ᵥ y ≠ 0) :
    rankOneExtensionUpperCell t y * rankOneExtensionLowerCell x h =
      rankOneExtensionLowerBlock t (rankOneExtensionCellShear (x 0) y) 0 1 *
        (rankOneExtensionLowerCell x (h * rankOneExtensionCellScalarInv (x 0) y) *
          rankOneExtensionUpperCell t
            (lowerScalarEntry (h * rankOneExtensionCellScalarInv (x 0) y) • y)) := by
  have key := rankOneExtensionUpperCell_mulVec_mul_lowerBlock (t := t) 1
    (rankOneExtensionCellShear (x 0) y) (x 0) y (lowerScalarUnit h)
    (lowerScalarUnit (h * rankOneExtensionCellScalarInv (x 0) y))
    (by rw [rankOneExtensionCellShear_val hs, Units.val_one, one_mul])
    (by
      simp only [lowerScalarUnit_val, lowerScalarEntry_mul]
      rw [lowerScalarEntry_cellScalarInv hs, mul_assoc, inv_mul_cancel₀ hs, mul_one])
  rw [Units.val_one, Matrix.one_mulVec] at key
  simp only [rankOneExtensionLowerCell]
  rw [key, ← mul_assoc, rankOneExtensionLowerBlock_mul]
  simp

end Cells

section Topology

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] {t : ℕ}

theorem continuous_rankOneExtensionLowerCell :
    Continuous fun p : Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K =>
      rankOneExtensionLowerCell p.1 p.2 := by
  have hval : ∀ (x : Fin (t + 1) → K) (a : Kˣ), (rankOneExtensionLowerBlock t 1 x a).val =
      Matrix.reindex (rankOneExtensionCellCoordinates t) (rankOneExtensionCellCoordinates t)
        (Matrix.fromBlocks 1 0 (Matrix.of fun (_ : Fin 1) => x)
          (Matrix.of fun (_ _ : Fin 1) => (a : K))) := by
    intro x a
    rw [rankOneExtensionCellBlocks_val, rankOneExtensionCellBlocks_lowerBlock, Units.val_one]
  have hblock : ∀ {x : Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K →
      Fin (t + 1) → K} {a : Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K → K},
      Continuous x → Continuous a → Continuous fun z =>
        Matrix.reindex (rankOneExtensionCellCoordinates t) (rankOneExtensionCellCoordinates t)
          (Matrix.fromBlocks (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) K) 0
            (Matrix.of fun (_ : Fin 1) => x z) (Matrix.of fun (_ _ : Fin 1) => a z)) := by
    intro x a hx ha
    exact (continuous_const.matrix_fromBlocks continuous_const
      (continuous_matrix fun _ j => (continuous_apply j).comp hx)
      (continuous_matrix fun _ _ => ha)).matrix_reindex _ _
  have he : Continuous fun p : Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K =>
      lowerScalarEntry p.2 :=
    continuous_lowerScalarEntry.comp continuous_snd
  have hx : Continuous fun p : Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K =>
      p.1 0 :=
    continuous_pi fun j => continuous_fst.matrix_elem 0 j
  have hinv := he.inv₀ fun p => lowerScalarEntry_ne_zero p.2
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (hblock hx he).congr fun p => (hval (p.1 0) (lowerScalarUnit p.2)).symm
  · refine (hblock (hinv.neg.smul hx) hinv).congr fun p => ?_
    simp only [rankOneExtensionLowerCell]
    rw [rankOneExtensionLowerBlock_one_inv, hval]
    simp

end Topology

section Reorder

variable {Q X Hg Y : Type*} [MeasurableSpace Q] [MeasurableSpace X] [MeasurableSpace Hg]
  [MeasurableSpace Y]

/-- The reordering `((q, (x, h)), y) ↦ ((x, y), (q, h))` of the cell parameters. -/
def cellReorder : (Q × (X × Hg)) × Y ≃ᵐ (X × Y) × (Q × Hg) where
  toFun z := ((z.1.2.1, z.2), (z.1.1, z.1.2.2))
  invFun w := ((w.2.1, (w.1.1, w.2.2)), w.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun :=
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd).prodMk
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  measurable_invFun :=
    ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_fst)

@[simp] theorem cellReorder_apply (z : (Q × (X × Hg)) × Y) :
    cellReorder z = ((z.1.2.1, z.2), (z.1.1, z.1.2.2)) := rfl

theorem measurePreserving_cellReorder (μQ : Measure Q) (dx : Measure X) (ρ : Measure Hg)
    (dy : Measure Y) [SFinite μQ] [SFinite dx] [SFinite ρ] [SFinite dy] :
    MeasurePreserving (cellReorder : (Q × (X × Hg)) × Y ≃ᵐ (X × Y) × (Q × Hg))
      ((μQ.prod (dx.prod ρ)).prod dy) ((dx.prod dy).prod (μQ.prod ρ)) := by
  have h1 := measurePreserving_prodAssoc μQ (dx.prod ρ) dy
  have g1 := measurePreserving_prodAssoc dx ρ dy
  have g2 := (MeasurePreserving.id dx).prod (Measure.measurePreserving_swap (μ := ρ) (ν := dy))
  have g3 := (measurePreserving_prodAssoc dx dy ρ).symm _
  have h2 := (MeasurePreserving.id μQ).prod (g3.comp (g2.comp g1))
  have h3 := Measure.measurePreserving_swap (μ := μQ) (ν := (dx.prod dy).prod ρ)
  have h4 := measurePreserving_prodAssoc (dx.prod dy) ρ μQ
  have h5 := (MeasurePreserving.id (dx.prod dy)).prod
    (Measure.measurePreserving_swap (μ := ρ) (ν := μQ))
  have h := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  refine ⟨cellReorder.measurable, ?_⟩
  rw [← h.map_eq]
  congr 1

end Reorder

section Integral

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] {t : ℕ}
  (H : Subgroup (Langlands.GeneralLinear (t + 1) K))
  [MeasurableSpace (Langlands.GeneralLinear (t + 1) K)]
  [BorelSpace (Langlands.GeneralLinear (t + 1) K)]
  [MeasurableSpace (Langlands.GeneralLinear (1 + (t + 1)) K)]
  [BorelSpace (Langlands.GeneralLinear (1 + (t + 1)) K)]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  [MeasurableSpace (lowerTriangularSubgroup 1 K)] [BorelSpace (lowerTriangularSubgroup 1 K)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [T1Space K] [MeasurableSpace (Langlands.GeneralLinear (t + 1) K)]
  [BorelSpace (Langlands.GeneralLinear (t + 1) K)] [BorelSpace (LeftQuotient H)] in
/-- The map `((x, y), (q, h)) ↦ (q, B(1, x, h) u(y))` is measurable. -/
theorem measurable_lowerCell_mul_upperCell :
    Measurable fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
        (LeftQuotient H × lowerTriangularSubgroup 1 K) =>
      (z.2.1, rankOneExtensionLowerCell z.1.1 z.2.2 * rankOneExtensionUpperCell t z.1.2) := by
  have := secondCountable_lowerTriangular (K := K)
  have := secondCountable_generalLinear (K := K) (1 + (t + 1))
  have : SecondCountableTopology (Matrix (Fin 1) (Fin (t + 1)) K) :=
    inferInstanceAs (SecondCountableTopology (Fin 1 → Fin (t + 1) → K))
  have : OpensMeasurableSpace (Matrix (Fin 1) (Fin (t + 1)) K) :=
    inferInstanceAs (OpensMeasurableSpace (Fin 1 → Fin (t + 1) → K))
  have : OpensMeasurableSpace
      (Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K) := inferInstance
  have : MeasurableMul₂ (Langlands.GeneralLinear (1 + (t + 1)) K) :=
    ContinuousMul.measurableMul₂
  have hl : Measurable fun p : Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K =>
      rankOneExtensionLowerCell p.1 p.2 :=
    continuous_rankOneExtensionLowerCell.measurable
  have hu : Measurable (rankOneExtensionUpperCell (K := K) t) :=
    (continuous_rankOneExtensionUpperCell t).measurable
  -- Composites are elaborated without an expected type: unifying `?g ∘ ?f` against the
  -- target lambda unfolds the cell definitions and times out.
  have hp : Measurable fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
      (LeftQuotient H × lowerTriangularSubgroup 1 K) => (z.1.1, z.2.2) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have hy : Measurable fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
      (LeftQuotient H × lowerTriangularSubgroup 1 K) => z.1.2 :=
    measurable_snd.comp measurable_fst
  have hlz : Measurable fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
      (LeftQuotient H × lowerTriangularSubgroup 1 K) => rankOneExtensionLowerCell z.1.1 z.2.2 := by
    have h := hl.comp hp
    exact h
  have huz : Measurable fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
      (LeftQuotient H × lowerTriangularSubgroup 1 K) => rankOneExtensionUpperCell t z.1.2 := by
    have h := hu.comp hy
    exact h
  have hmul := hlz.mul huz
  exact (measurable_fst.comp measurable_snd).prodMk hmul

/-- Integral form of the open-cell exchange, in the order `((x, y), (q, h))`. -/
theorem integral_cellExchange (dx : Measure (Matrix (Fin 1) (Fin (t + 1)) K)) [SFinite dx]
    (ν : Measure K) [SigmaFinite ν] [NullSingletonClass ν]
    (μQ : Measure (LeftQuotient H)) [SFinite μQ]
    (hμQ : ∀ g, MeasurePreserving (rightTranslate H g) μQ μQ)
    (ρ : Measure (lowerTriangularSubgroup 1 K)) [SFinite ρ] [ρ.IsMulRightInvariant]
    (χ : K →*₀ ℝ≥0) (hχm : Measurable χ)
    (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)
    (Ψ : LeftQuotient H × Langlands.GeneralLinear (1 + (t + 1)) K → E)
    (hΨm : StronglyMeasurable Ψ)
    (hΨ : ∀ q r z, Ψ (q, rankOneExtensionLowerBlock t r 0 1 * z) =
      Ψ (rightTranslate H r q, z)) :
    (Integrable (fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
        (LeftQuotient H × lowerTriangularSubgroup 1 K) =>
        Ψ (z.2.1, rankOneExtensionUpperCell t z.1.2 * rankOneExtensionLowerCell z.1.1 z.2.2))
        ((dx.prod (Measure.pi fun _ : Fin (t + 1) => ν)).prod (μQ.prod ρ)) ↔
      Integrable (fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
        (LeftQuotient H × lowerTriangularSubgroup 1 K) =>
        (χ (lowerScalarEntry z.2.2))⁻¹ ^ (t + 1) •
          Ψ (z.2.1, rankOneExtensionLowerCell z.1.1 z.2.2 * rankOneExtensionUpperCell t z.1.2))
        ((dx.prod (Measure.pi fun _ : Fin (t + 1) => ν)).prod (μQ.prod ρ))) ∧
    ∫ z, Ψ (z.2.1, rankOneExtensionUpperCell t z.1.2 * rankOneExtensionLowerCell z.1.1 z.2.2)
        ∂((dx.prod (Measure.pi fun _ : Fin (t + 1) => ν)).prod (μQ.prod ρ)) =
      ∫ z, (χ (lowerScalarEntry z.2.2))⁻¹ ^ (t + 1) •
          Ψ (z.2.1, rankOneExtensionLowerCell z.1.1 z.2.2 * rankOneExtensionUpperCell t z.1.2)
        ∂((dx.prod (Measure.pi fun _ : Fin (t + 1) => ν)).prod (μQ.prod ρ)) := by
  set wN : K → ℝ≥0 := fun a => (χ a)⁻¹ ^ (t + 1) with hwN
  have hwNm : Measurable wN := hχm.inv.pow_const _
  have hdy : ∀ a : K, a ≠ 0 → (Measure.pi fun _ : Fin (t + 1) => ν).map (fun y => a • y) =
      ((wN a : ℝ≥0) : ℝ≥0∞) • Measure.pi fun _ : Fin (t + 1) => ν := by
    intro a ha
    rw [productMeasure_map_const_smul ν χ hχ ha, Fintype.card_fin]
  have hxrow : Measurable fun x : Matrix (Fin 1) (Fin (t + 1)) K => x 0 :=
    measurable_pi_apply 0
  have hmap := map_cellExchange H (fun x : Matrix (Fin 1) (Fin (t + 1)) K => x 0) hxrow dx
    (Measure.pi fun _ : Fin (t + 1) => ν) μQ hμQ ρ (fun a => ((wN a : ℝ≥0) : ℝ≥0∞))
    hwNm.coe_nnreal_ennreal hdy
  have hTm := measurable_rankOneExtensionCellExchange H
    (fun x : Matrix (Fin 1) (Fin (t + 1)) K => x 0) hxrow
  set M := (dx.prod (Measure.pi fun _ : Fin (t + 1) => ν)).prod (μQ.prod ρ) with hM
  set T := rankOneExtensionCellExchange H (fun x : Matrix (Fin 1) (Fin (t + 1)) K => x 0)
    with hT
  set G : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
      (LeftQuotient H × lowerTriangularSubgroup 1 K) → E := fun z =>
    Ψ (z.2.1, rankOneExtensionLowerCell z.1.1 z.2.2 * rankOneExtensionUpperCell t z.1.2)
    with hG
  have hGm : StronglyMeasurable G :=
    hΨm.comp_measurable (measurable_lowerCell_mul_upperCell H)
  have hne : ∀ᵐ z ∂M, 1 + z.1.1 0 ⬝ᵥ z.1.2 ≠ 0 := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using
      prod_cellScalar_eq_zero ν (fun x : Matrix (Fin 1) (Fin (t + 1)) K => x 0) hxrow dx
        (μQ.prod ρ)
  have hae : (fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
      (LeftQuotient H × lowerTriangularSubgroup 1 K) =>
      Ψ (z.2.1, rankOneExtensionUpperCell t z.1.2 * rankOneExtensionLowerCell z.1.1 z.2.2))
      =ᵐ[M] G ∘ T := by
    filter_upwards [hne] with z hs
    change Ψ (z.2.1, rankOneExtensionUpperCell t z.1.2 * rankOneExtensionLowerCell z.1.1 z.2.2) =
      Ψ (rightTranslate H (rankOneExtensionCellShear (z.1.1 0) z.1.2) z.2.1,
        rankOneExtensionLowerCell z.1.1 (z.2.2 * rankOneExtensionCellScalarInv (z.1.1 0) z.1.2) *
          rankOneExtensionUpperCell t
            (lowerScalarEntry (z.2.2 * rankOneExtensionCellScalarInv (z.1.1 0) z.1.2) • z.1.2))
    rw [rankOneExtensionUpperCell_mul_lowerCell _ _ _ hs, hΨ]
  have hwz : Measurable fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
      (LeftQuotient H × lowerTriangularSubgroup 1 K) => wN (lowerScalarEntry z.2.2) :=
    hwNm.comp (continuous_lowerScalarEntry.measurable.comp (measurable_snd.comp measurable_snd))
  constructor
  · rw [integrable_congr hae, ← integrable_map_measure hGm.aestronglyMeasurable
      hTm.aemeasurable, hmap, integrable_withDensity_iff_integrable_smul hwz]
  · rw [integral_congr_ae hae]
    change ∫ z, G (T z) ∂M = _
    rw [← integral_map hTm.aemeasurable hGm.aestronglyMeasurable, hmap,
      integral_withDensity_eq_integral_smul hwz]

/-- Integral form of the open-cell exchange, in the order `((q, (x, h)), y)` of the lower-block
disintegration followed by the upper-cell variable. -/
theorem integral_cellExchange_reorder (dx : Measure (Matrix (Fin 1) (Fin (t + 1)) K))
    [SFinite dx] (ν : Measure K) [SigmaFinite ν] [NullSingletonClass ν]
    (μQ : Measure (LeftQuotient H)) [SFinite μQ]
    (hμQ : ∀ g, MeasurePreserving (rightTranslate H g) μQ μQ)
    (ρ : Measure (lowerTriangularSubgroup 1 K)) [SFinite ρ] [ρ.IsMulRightInvariant]
    (χ : K →*₀ ℝ≥0) (hχm : Measurable χ)
    (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)
    (Ψ : LeftQuotient H × Langlands.GeneralLinear (1 + (t + 1)) K → E)
    (hΨm : StronglyMeasurable Ψ)
    (hΨ : ∀ q r z, Ψ (q, rankOneExtensionLowerBlock t r 0 1 * z) =
      Ψ (rightTranslate H r q, z)) :
    (Integrable (fun z : (LeftQuotient H × (Matrix (Fin 1) (Fin (t + 1)) K ×
        lowerTriangularSubgroup 1 K)) × (Fin (t + 1) → K) =>
        Ψ (z.1.1, rankOneExtensionUpperCell t z.2 * rankOneExtensionLowerCell z.1.2.1 z.1.2.2))
        ((μQ.prod (dx.prod ρ)).prod (Measure.pi fun _ : Fin (t + 1) => ν)) ↔
      Integrable (fun z : (LeftQuotient H × (Matrix (Fin 1) (Fin (t + 1)) K ×
        lowerTriangularSubgroup 1 K)) × (Fin (t + 1) → K) =>
        (χ (lowerScalarEntry z.1.2.2))⁻¹ ^ (t + 1) •
          Ψ (z.1.1, rankOneExtensionLowerCell z.1.2.1 z.1.2.2 * rankOneExtensionUpperCell t z.2))
        ((μQ.prod (dx.prod ρ)).prod (Measure.pi fun _ : Fin (t + 1) => ν))) ∧
    ∫ z, Ψ (z.1.1, rankOneExtensionUpperCell t z.2 * rankOneExtensionLowerCell z.1.2.1 z.1.2.2)
        ∂((μQ.prod (dx.prod ρ)).prod (Measure.pi fun _ : Fin (t + 1) => ν)) =
      ∫ z, (χ (lowerScalarEntry z.1.2.2))⁻¹ ^ (t + 1) •
          Ψ (z.1.1, rankOneExtensionLowerCell z.1.2.1 z.1.2.2 * rankOneExtensionUpperCell t z.2)
        ∂((μQ.prod (dx.prod ρ)).prod (Measure.pi fun _ : Fin (t + 1) => ν)) := by
  obtain ⟨hint, hintegral⟩ := integral_cellExchange H dx ν μQ hμQ ρ χ hχm hχ Ψ hΨm hΨ
  have hmp := measurePreserving_cellReorder μQ dx ρ (Measure.pi fun _ : Fin (t + 1) => ν)
  have he := (cellReorder : (LeftQuotient H × (Matrix (Fin 1) (Fin (t + 1)) K ×
    lowerTriangularSubgroup 1 K)) × (Fin (t + 1) → K) ≃ᵐ _).measurableEmbedding
  refine ⟨?_, ?_⟩
  · rw [← hmp.integrable_comp_emb he, ← hmp.integrable_comp_emb he] at hint
    exact hint
  · have h1 := hmp.integral_comp' (fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
        (LeftQuotient H × lowerTriangularSubgroup 1 K) =>
      Ψ (z.2.1, rankOneExtensionUpperCell t z.1.2 * rankOneExtensionLowerCell z.1.1 z.2.2))
    have h2 := hmp.integral_comp' (fun z : (Matrix (Fin 1) (Fin (t + 1)) K × (Fin (t + 1) → K)) ×
        (LeftQuotient H × lowerTriangularSubgroup 1 K) =>
      (χ (lowerScalarEntry z.2.2))⁻¹ ^ (t + 1) •
        Ψ (z.2.1, rankOneExtensionLowerCell z.1.1 z.2.2 * rankOneExtensionUpperCell t z.1.2))
    exact h1.trans (hintegral.trans h2.symm)

end Integral

end Langlands.RankinSelberg
