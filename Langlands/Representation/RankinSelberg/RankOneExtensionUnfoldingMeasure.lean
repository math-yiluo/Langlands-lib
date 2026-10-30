import Langlands.Representation.RankinSelberg.RankOneExtensionCellAlgebra
import Langlands.Group.GL.LowerBlockQuotientCoordinates
import Langlands.Analysis.Local.QuotientTopology
import Langlands.Representation.RankinSelberg.Measures
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Measure identity for the open-cell exchange

An abstract skew-product identity: a family of measure-preserving maps of one factor,
followed by a scaling of a second factor, pushes a product measure to the same product
measure with a density. It is then specialized to the change of variables of JPSS (1983),
Lemma 5.5.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Matrix GeneralLinear QuotientIntegration
open scoped ENNReal NNReal

section Abstract

variable {A Y B : Type*} [MeasurableSpace A] [MeasurableSpace Y] [MeasurableSpace B]
  (μA : Measure A) (dy : Measure Y) (μB : Measure B)
  [SFinite dy] [SFinite μB]

/-- The skew map `((a, y), b) ↦ ((a, c(φ_(a,y) b) y), φ_(a,y) b)`. -/
def skewScalingMap (φ : A × Y → B → B) (c : B → Y → Y) : (A × Y) × B → (A × Y) × B :=
  fun z => ((z.1.1, c (φ z.1 z.2) z.1.2), φ z.1 z.2)

variable {μA dy μB}

theorem measurable_skewScalingMap {φ : A × Y → B → B} {c : B → Y → Y}
    (hφm : Measurable (Function.uncurry φ)) (hcm : Measurable (Function.uncurry c)) :
    Measurable (skewScalingMap φ c) :=
  ((measurable_fst.comp measurable_fst).prodMk
    (hcm.comp (hφm.prodMk (measurable_snd.comp measurable_fst)))).prodMk hφm

/-- If every `φ_(a,y)` preserves `μB` and every `c b` scales `dy` by `w b`, the skew map
sends `(μA × dy) × μB` to the same measure with density `w` in the last factor. -/
theorem map_skewScalingMap (φ : A × Y → B → B) (c : B → Y → Y) (w : B → ℝ≥0∞)
    (hφm : Measurable (Function.uncurry φ)) (hφ : ∀ z, MeasurePreserving (φ z) μB μB)
    (hcm : Measurable (Function.uncurry c)) (hc : ∀ b, dy.map (c b) = w b • dy)
    (hw : Measurable w) :
    ((μA.prod dy).prod μB).map (skewScalingMap φ c) =
      ((μA.prod dy).prod μB).withDensity (fun z => w z.2) := by
  have hTm : Measurable (skewScalingMap φ c) := measurable_skewScalingMap hφm hcm
  have hwm : Measurable (fun z : (A × Y) × B => w z.2) := hw.comp measurable_snd
  ext E hE
  rw [Measure.map_apply hTm hE, withDensity_apply _ hE]
  set f : (A × Y) × B → ℝ≥0∞ := E.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hE
  have hlhs : ((μA.prod dy).prod μB) (skewScalingMap φ c ⁻¹' E) =
      ∫⁻ z, f (skewScalingMap φ c z) ∂((μA.prod dy).prod μB) := by
    rw [← lintegral_indicator_one (hTm hE)]
    rfl
  have hrhs : ∫⁻ z in E, w z.2 ∂((μA.prod dy).prod μB) =
      ∫⁻ z, w z.2 * f z ∂((μA.prod dy).prod μB) := by
    rw [← lintegral_indicator hE]
    congr 1
    funext z
    by_cases hz : z ∈ E <;> simp [hf, hz]
  rw [hlhs, hrhs]
  -- measurability of the auxiliary integrands
  have hF : Measurable fun p : (A × Y) × B => f ((p.1.1, c p.2 p.1.2), p.2) :=
    hfm.comp (((measurable_fst.comp measurable_fst).prodMk
      (hcm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).prodMk
      measurable_snd)
  have hG : Measurable fun p : (A × Y) × B => w p.2 * f p := hwm.mul hfm
  calc ∫⁻ z, f (skewScalingMap φ c z) ∂((μA.prod dy).prod μB)
      = ∫⁻ ay, ∫⁻ b, f ((ay.1, c (φ ay b) ay.2), φ ay b) ∂μB ∂(μA.prod dy) :=
        lintegral_prod _ (hfm.comp hTm).aemeasurable
    _ = ∫⁻ ay, ∫⁻ b, f ((ay.1, c b ay.2), b) ∂μB ∂(μA.prod dy) := by
        refine lintegral_congr fun ay => ?_
        exact (hφ ay).lintegral_comp (f := fun b => f ((ay.1, c b ay.2), b))
          (hF.comp (measurable_prodMk_left (x := ay)) :)
    _ = ∫⁻ a, ∫⁻ y, ∫⁻ b, f ((a, c b y), b) ∂μB ∂dy ∂μA :=
        lintegral_prod _ (hF.lintegral_prod_right'.aemeasurable)
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ y, f ((a, c b y), b) ∂dy ∂μB ∂μA := by
        refine lintegral_congr fun a => ?_
        refine lintegral_lintegral_swap ?_
        exact (hF.comp ((measurable_const.prodMk measurable_fst).prodMk
          measurable_snd)).aemeasurable
    _ = ∫⁻ a, ∫⁻ b, w b * ∫⁻ y, f ((a, y), b) ∂dy ∂μB ∂μA := by
        refine lintegral_congr fun a => lintegral_congr fun b => ?_
        have hcb : Measurable (c b) := hcm.comp (measurable_const.prodMk measurable_id)
        have hfy : Measurable fun y => f ((a, y), b) :=
          hfm.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const)
        rw [← lintegral_map hfy hcb, hc b, lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ a, ∫⁻ y, ∫⁻ b, w b * f ((a, y), b) ∂μB ∂dy ∂μA := by
        refine lintegral_congr fun a => ?_
        have hswap := lintegral_lintegral_swap (μ := dy) (ν := μB)
          (f := fun y b => w b * f ((a, y), b))
          ((hG.comp ((measurable_const.prodMk measurable_fst).prodMk
            measurable_snd)).aemeasurable)
        rw [hswap]
        refine lintegral_congr fun b => ?_
        rw [lintegral_const_mul]
        exact hfm.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const)
    _ = ∫⁻ ay, ∫⁻ b, w b * f (ay, b) ∂μB ∂(μA.prod dy) :=
        (lintegral_prod _ (hG.lintegral_prod_right'.aemeasurable)).symm
    _ = ∫⁻ z, w z.2 * f z ∂((μA.prod dy).prod μB) :=
        (lintegral_prod _ hG.aemeasurable).symm

end Abstract

section CellShear

variable {K : Type*} [Field K] {t : ℕ}

private theorem vecMulVec_mul_self (x y : Fin (t + 1) → K) :
    vecMulVec y x * vecMulVec y x = (x ⬝ᵥ y) • vecMulVec y x := by
  rw [vecMulVec_mul_vecMulVec]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

private theorem cellShear_mul_inv {x y : Fin (t + 1) → K} (hs : 1 + x ⬝ᵥ y ≠ 0) :
    (1 + vecMulVec y x) * (1 - (1 + x ⬝ᵥ y)⁻¹ • vecMulVec y x) = 1 := by
  have hA := vecMulVec_mul_self x y
  have hc : (1 + x ⬝ᵥ y)⁻¹ * (1 + x ⬝ᵥ y) = 1 := inv_mul_cancel₀ hs
  calc (1 + vecMulVec y x) * (1 - (1 + x ⬝ᵥ y)⁻¹ • vecMulVec y x)
      = 1 + vecMulVec y x - (1 + x ⬝ᵥ y)⁻¹ • vecMulVec y x -
          (1 + x ⬝ᵥ y)⁻¹ • (vecMulVec y x * vecMulVec y x) := by
        simp only [add_mul, mul_sub, one_mul, mul_one, Matrix.mul_smul]
        abel
    _ = 1 + (1 - (1 + x ⬝ᵥ y)⁻¹ * (1 + x ⬝ᵥ y)) • vecMulVec y x := by
        rw [hA]
        module
    _ = 1 := by rw [hc, sub_self, zero_smul, add_zero]

private theorem cellShear_inv_mul {x y : Fin (t + 1) → K} (hs : 1 + x ⬝ᵥ y ≠ 0) :
    (1 - (1 + x ⬝ᵥ y)⁻¹ • vecMulVec y x) * (1 + vecMulVec y x) = 1 := by
  have hA := vecMulVec_mul_self x y
  have hc : (1 + x ⬝ᵥ y)⁻¹ * (1 + x ⬝ᵥ y) = 1 := inv_mul_cancel₀ hs
  calc (1 - (1 + x ⬝ᵥ y)⁻¹ • vecMulVec y x) * (1 + vecMulVec y x)
      = 1 + vecMulVec y x - (1 + x ⬝ᵥ y)⁻¹ • vecMulVec y x -
          (1 + x ⬝ᵥ y)⁻¹ • (vecMulVec y x * vecMulVec y x) := by
        simp only [sub_mul, mul_add, one_mul, mul_one, Matrix.smul_mul]
        abel
    _ = 1 + (1 - (1 + x ⬝ᵥ y)⁻¹ * (1 + x ⬝ᵥ y)) • vecMulVec y x := by
        rw [hA]
        module
    _ = 1 := by rw [hc, sub_self, zero_smul, add_zero]

open Classical in
/-- The shear `r = I + y x` of the open-cell exchange, with Sherman–Morrison inverse
`I - s⁻¹ y x` for `s = 1 + x · y`. On the null set `s = 0` it is set to `1`. -/
noncomputable def rankOneExtensionCellShear (x y : Fin (t + 1) → K) : Langlands.GeneralLinear (t + 1) K :=
  if hs : 1 + x ⬝ᵥ y = 0 then 1 else
    ⟨1 + vecMulVec y x, 1 - (1 + x ⬝ᵥ y)⁻¹ • vecMulVec y x,
      cellShear_mul_inv hs, cellShear_inv_mul hs⟩

theorem rankOneExtensionCellShear_val {x y : Fin (t + 1) → K} (hs : 1 + x ⬝ᵥ y ≠ 0) :
    (rankOneExtensionCellShear x y).val = 1 + vecMulVec y x := by
  simp [rankOneExtensionCellShear, hs]

theorem rankOneExtensionCellShear_inv_val {x y : Fin (t + 1) → K} (hs : 1 + x ⬝ᵥ y ≠ 0) :
    (rankOneExtensionCellShear x y)⁻¹.val = 1 - (1 + x ⬝ᵥ y)⁻¹ • vecMulVec y x := by
  simp [rankOneExtensionCellShear, hs]

/-- A unit as an element of the `1 × 1` lower-triangular group. -/
def rankOneExtensionScalarLower (a : Kˣ) : lowerTriangularSubgroup 1 K :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) a, by
    intro i j hij
    exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl _)⟩

@[simp] theorem rankOneExtensionScalarLower_apply (a : Kˣ) (i j : Fin 1) :
    (rankOneExtensionScalarLower a).val.val i j = a := by
  rw [Subsingleton.elim i j]
  simp [rankOneExtensionScalarLower]

/-- The entry of an element of the `1 × 1` lower-triangular group. -/
def lowerScalarEntry (h : lowerTriangularSubgroup 1 K) : K := h.val.val 0 0

theorem lowerScalarEntry_ne_zero (h : lowerTriangularSubgroup 1 K) : lowerScalarEntry h ≠ 0 := by
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero h.val
  rwa [Matrix.det_unique] at hdet

@[simp] theorem lowerScalarEntry_mul (h h' : lowerTriangularSubgroup 1 K) :
    lowerScalarEntry (h * h') = lowerScalarEntry h * lowerScalarEntry h' := by
  simp [lowerScalarEntry, Matrix.mul_apply]

@[simp] theorem lowerScalarEntry_scalarLower (a : Kˣ) :
    lowerScalarEntry (rankOneExtensionScalarLower a) = a :=
  rankOneExtensionScalarLower_apply a 0 0

open Classical in
/-- The inverse scalar `s⁻¹`, `s = 1 + x · y`, in the `1 × 1` lower-triangular group;
it is set to `1` on the null set `s = 0`. -/
def rankOneExtensionCellScalarInv (x y : Fin (t + 1) → K) : lowerTriangularSubgroup 1 K :=
  if hs : 1 + x ⬝ᵥ y = 0 then 1 else rankOneExtensionScalarLower (Units.mk0 _ hs)⁻¹

theorem lowerScalarEntry_cellScalarInv {x y : Fin (t + 1) → K} (hs : 1 + x ⬝ᵥ y ≠ 0) :
    lowerScalarEntry (rankOneExtensionCellScalarInv x y) = (1 + x ⬝ᵥ y)⁻¹ := by
  simp [rankOneExtensionCellScalarInv, hs]

end CellShear

section QuotientAction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)

/-- Right translation is jointly continuous on `(H \ G) × G`. -/
theorem continuous_rightTranslate_prod :
    Continuous fun p : LeftQuotient H × G => rightTranslate H p.2 p.1 := by
  have hq : IsOpenQuotientMap (Prod.map (leftQuotientMap H) (id : G → G)) :=
    (leftQuotient_isOpenQuotientMap H).prodMap IsOpenQuotientMap.id
  refine hq.continuous_comp_iff.mp ?_
  exact (leftQuotient_isOpenQuotientMap H).continuous.comp (continuous_fst.mul continuous_snd)

end QuotientAction

section CellExchange

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] {t : ℕ}

omit [T1Space K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] in
private theorem continuous_cellScalar :
    Continuous fun z : (Fin (t + 1) → K) × (Fin (t + 1) → K) => 1 + z.1 ⬝ᵥ z.2 :=
  continuous_const.add (continuous_fst.dotProduct continuous_snd)

omit [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] in
private theorem isOpen_cellScalar_ne_zero :
    IsOpen {z : (Fin (t + 1) → K) × (Fin (t + 1) → K) | 1 + z.1 ⬝ᵥ z.2 ≠ 0} :=
  continuous_cellScalar.isOpen_preimage _ isOpen_compl_singleton

omit [IsTopologicalDivisionRing K] [T1Space K] [MeasurableSpace K] [BorelSpace K] in
theorem secondCountable_generalLinear (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n K) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → K))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

omit [IsTopologicalDivisionRing K] [T1Space K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] in
theorem continuous_lowerScalarEntry :
    Continuous (lowerScalarEntry : lowerTriangularSubgroup 1 K → K) :=
  (show Continuous fun h : lowerTriangularSubgroup 1 K =>
    ((h : Langlands.GeneralLinear 1 K) : Matrix (Fin 1) (Fin 1) K) from
    Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 0

/-- The shear of the open-cell exchange is Borel measurable in `(x, y)`. -/
theorem measurable_cellShear [MeasurableSpace (Langlands.GeneralLinear (t + 1) K)]
    [BorelSpace (Langlands.GeneralLinear (t + 1) K)] :
    Measurable fun z : (Fin (t + 1) → K) × (Fin (t + 1) → K) =>
      rankOneExtensionCellShear z.1 z.2 := by
  classical
  set S := {z : (Fin (t + 1) → K) × (Fin (t + 1) → K) | 1 + z.1 ⬝ᵥ z.2 ≠ 0} with hSdef
  have heq : (fun z : (Fin (t + 1) → K) × (Fin (t + 1) → K) =>
      rankOneExtensionCellShear z.1 z.2) =
      S.piecewise (fun z => rankOneExtensionCellShear z.1 z.2) (fun _ => 1) := by
    funext z
    by_cases hz : z ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz]
      have hz' : 1 + z.1 ⬝ᵥ z.2 = 0 := not_not.mp hz
      simp [rankOneExtensionCellShear, hz']
  rw [heq]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const
    isOpen_cellScalar_ne_zero.measurableSet
  rw [Units.isEmbedding_embedProduct.continuousOn_iff]
  have hv : Continuous fun z : (Fin (t + 1) → K) × (Fin (t + 1) → K) => vecMulVec z.2 z.1 :=
    continuous_snd.matrix_vecMulVec continuous_fst
  have hcont : ContinuousOn (fun z : (Fin (t + 1) → K) × (Fin (t + 1) → K) =>
      ((1 + vecMulVec z.2 z.1 : Matrix (Fin (t + 1)) (Fin (t + 1)) K),
        MulOpposite.op (1 - (1 + z.1 ⬝ᵥ z.2)⁻¹ • vecMulVec z.2 z.1))) S := by
    refine (continuous_const.add hv).continuousOn.prodMk ?_
    refine MulOpposite.continuous_op.comp_continuousOn ?_
    exact continuousOn_const.sub
      ((continuous_cellScalar.continuousOn.inv₀ fun z hz => hz).smul hv.continuousOn)
  refine hcont.congr fun z hz => ?_
  simp only [Function.comp_apply, Units.embedProduct_apply,
    rankOneExtensionCellShear_val hz, rankOneExtensionCellShear_inv_val hz]

/-- The inverse scalar of the open-cell exchange is Borel measurable in `(x, y)`. -/
theorem measurable_cellScalarInv [MeasurableSpace (lowerTriangularSubgroup 1 K)]
    [BorelSpace (lowerTriangularSubgroup 1 K)] :
    Measurable fun z : (Fin (t + 1) → K) × (Fin (t + 1) → K) =>
      rankOneExtensionCellScalarInv z.1 z.2 := by
  classical
  set S := {z : (Fin (t + 1) → K) × (Fin (t + 1) → K) | 1 + z.1 ⬝ᵥ z.2 ≠ 0} with hSdef
  have heq : (fun z : (Fin (t + 1) → K) × (Fin (t + 1) → K) =>
      rankOneExtensionCellScalarInv z.1 z.2) =
      S.piecewise (fun z => rankOneExtensionCellScalarInv z.1 z.2) (fun _ => 1) := by
    funext z
    by_cases hz : z ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz]
      have hz' : 1 + z.1 ⬝ᵥ z.2 = 0 := not_not.mp hz
      simp [rankOneExtensionCellScalarInv, hz']
  rw [heq]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const
    isOpen_cellScalar_ne_zero.measurableSet
  rw [Topology.IsEmbedding.subtypeVal.continuousOn_iff,
    Units.isEmbedding_embedProduct.continuousOn_iff]
  have hcont : ContinuousOn (fun z : (Fin (t + 1) → K) × (Fin (t + 1) → K) =>
      ((1 + z.1 ⬝ᵥ z.2)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) K),
        MulOpposite.op ((1 + z.1 ⬝ᵥ z.2) • (1 : Matrix (Fin 1) (Fin 1) K)))) S := by
    refine ((continuous_cellScalar.continuousOn.inv₀ fun z hz => hz).smul
      continuousOn_const).prodMk ?_
    exact MulOpposite.continuous_op.comp_continuousOn
      (continuous_cellScalar.continuousOn.smul continuousOn_const)
  refine hcont.congr fun z hz => ?_
  have hz' : 1 + z.1 ⬝ᵥ z.2 ≠ 0 := hz
  simp only [Function.comp_apply, Units.embedProduct_apply, rankOneExtensionCellScalarInv,
    hz', ↓reduceDIte, rankOneExtensionScalarLower, map_inv]
  refine Prod.ext ?_ ?_
  · ext i j
    rw [Subsingleton.elim i j]
    simp
  · refine MulOpposite.unop_injective ?_
    ext i j
    rw [Subsingleton.elim i j]
    simp

end CellExchange

section CellExchangeMap

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] {t : ℕ}
  {X : Type*} (H : Subgroup (Langlands.GeneralLinear (t + 1) K)) (xrow : X → Fin (t + 1) → K)

/-- The fibre action of the open-cell exchange on `(H \ GL_(t+1)) × B⁻_1`: right translation
by the shear `r = I + y x` and right multiplication by `s⁻¹`, `s = 1 + x · y`, where `x` is
the row `xrow` of the first parameter. -/
def rankOneExtensionCellExchangeAction (z : X × (Fin (t + 1) → K))
    (b : LeftQuotient H × lowerTriangularSubgroup 1 K) :
    LeftQuotient H × lowerTriangularSubgroup 1 K :=
  (rightTranslate H (rankOneExtensionCellShear (xrow z.1) z.2) b.1,
    b.2 * rankOneExtensionCellScalarInv (xrow z.1) z.2)

/-- The open-cell exchange `((x, y), (q, h)) ↦ ((x, h' y), (q r, h'))`, `h' = h s⁻¹`. -/
def rankOneExtensionCellExchange :
    (X × (Fin (t + 1) → K)) × (LeftQuotient H × lowerTriangularSubgroup 1 K) →
      (X × (Fin (t + 1) → K)) × (LeftQuotient H × lowerTriangularSubgroup 1 K) :=
  skewScalingMap (rankOneExtensionCellExchangeAction H xrow)
    (fun b y => lowerScalarEntry b.2 • y)

@[simp] theorem rankOneExtensionCellExchange_apply
    (z : (X × (Fin (t + 1) → K)) × (LeftQuotient H × lowerTriangularSubgroup 1 K)) :
    rankOneExtensionCellExchange H xrow z =
      ((z.1.1, lowerScalarEntry (z.2.2 * rankOneExtensionCellScalarInv (xrow z.1.1) z.1.2) •
          z.1.2),
        (rightTranslate H (rankOneExtensionCellShear (xrow z.1.1) z.1.2) z.2.1,
          z.2.2 * rankOneExtensionCellScalarInv (xrow z.1.1) z.1.2)) := rfl

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] [T1Space K]

omit [IsTopologicalDivisionRing K] [T1Space K] [MeasurableSpace K] [BorelSpace K] in
theorem secondCountable_lowerTriangular :
    SecondCountableTopology (lowerTriangularSubgroup 1 K) := by
  have := secondCountable_generalLinear (K := K) 1
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

/-- The fibre action of the open-cell exchange is jointly measurable. -/
theorem measurable_rankOneExtensionCellExchangeAction [MeasurableSpace X]
    (hxrow : Measurable xrow)
    [MeasurableSpace (Langlands.GeneralLinear (t + 1) K)]
    [BorelSpace (Langlands.GeneralLinear (t + 1) K)]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    [MeasurableSpace (lowerTriangularSubgroup 1 K)] [BorelSpace (lowerTriangularSubgroup 1 K)] :
    Measurable (Function.uncurry (rankOneExtensionCellExchangeAction H xrow)) := by
  have := secondCountable_generalLinear (K := K) (t + 1)
  have := secondCountable_lowerTriangular (K := K)
  have : MeasurableMul₂ (lowerTriangularSubgroup 1 K) := ContinuousMul.measurableMul₂
  have hshear : Measurable fun z : X × (Fin (t + 1) → K) =>
      rankOneExtensionCellShear (xrow z.1) z.2 :=
    measurable_cellShear.comp ((hxrow.comp measurable_fst).prodMk measurable_snd)
  have hsinv : Measurable fun z : X × (Fin (t + 1) → K) =>
      rankOneExtensionCellScalarInv (xrow z.1) z.2 :=
    measurable_cellScalarInv.comp ((hxrow.comp measurable_fst).prodMk measurable_snd)
  have hrt : Measurable fun p : LeftQuotient H × Langlands.GeneralLinear (t + 1) K =>
      rightTranslate H p.2 p.1 :=
    (continuous_rightTranslate_prod H).measurable
  exact (hrt.comp ((measurable_fst.comp measurable_snd).prodMk
    (hshear.comp measurable_fst))).prodMk
    ((measurable_snd.comp measurable_snd).mul (hsinv.comp measurable_fst))

omit [IsTopologicalDivisionRing K] [T1Space K] in
/-- The scaling `(b, y) ↦ h y` of the open-cell exchange is jointly measurable. -/
theorem measurable_rankOneExtensionCellScaling [IsTopologicalRing K]
    [MeasurableSpace (LeftQuotient H)]
    [MeasurableSpace (lowerTriangularSubgroup 1 K)] [BorelSpace (lowerTriangularSubgroup 1 K)] :
    Measurable (Function.uncurry fun (b : LeftQuotient H × lowerTriangularSubgroup 1 K)
      (y : Fin (t + 1) → K) => lowerScalarEntry b.2 • y) := by
  have hentry : Measurable (lowerScalarEntry : lowerTriangularSubgroup 1 K → K) :=
    continuous_lowerScalarEntry.measurable
  refine Measurable.of_eval fun i => ?_
  exact (hentry.comp (measurable_snd.comp measurable_fst)).mul
    ((measurable_pi_apply i).comp measurable_snd)

/-- The open-cell exchange is measurable. -/
theorem measurable_rankOneExtensionCellExchange [MeasurableSpace X] (hxrow : Measurable xrow)
    [MeasurableSpace (Langlands.GeneralLinear (t + 1) K)]
    [BorelSpace (Langlands.GeneralLinear (t + 1) K)]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    [MeasurableSpace (lowerTriangularSubgroup 1 K)] [BorelSpace (lowerTriangularSubgroup 1 K)] :
    Measurable (rankOneExtensionCellExchange H xrow) :=
  measurable_skewScalingMap (measurable_rankOneExtensionCellExchangeAction H xrow hxrow)
    (measurable_rankOneExtensionCellScaling H)

/-- The open-cell exchange sends `(dx × dy) × (μQ × ρ)` to the same measure with density
`w(h)`, when `dy`, `μQ` and `ρ` are s-finite, `μQ` and `ρ` are right-invariant, and `a • ·`
scales `dy` by `w a`. -/
theorem map_cellExchange [MeasurableSpace X] (hxrow : Measurable xrow)
    [MeasurableSpace (Langlands.GeneralLinear (t + 1) K)]
    [BorelSpace (Langlands.GeneralLinear (t + 1) K)]
    [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    [MeasurableSpace (lowerTriangularSubgroup 1 K)] [BorelSpace (lowerTriangularSubgroup 1 K)]
    (dx : Measure X) (dy : Measure (Fin (t + 1) → K)) [SFinite dy]
    (μQ : Measure (LeftQuotient H)) [SFinite μQ]
    (hμQ : ∀ g, MeasurePreserving (rightTranslate H g) μQ μQ)
    (ρ : Measure (lowerTriangularSubgroup 1 K)) [SFinite ρ] [ρ.IsMulRightInvariant]
    (w : K → ℝ≥0∞) (hw : Measurable w)
    (hdy : ∀ a : K, a ≠ 0 → dy.map (fun y => a • y) = w a • dy) :
    ((dx.prod dy).prod (μQ.prod ρ)).map (rankOneExtensionCellExchange H xrow) =
      ((dx.prod dy).prod (μQ.prod ρ)).withDensity (fun z => w (lowerScalarEntry z.2.2)) := by
  have := secondCountable_lowerTriangular (K := K)
  have : MeasurableMul₂ (lowerTriangularSubgroup 1 K) := ContinuousMul.measurableMul₂
  have hentry : Measurable (lowerScalarEntry : lowerTriangularSubgroup 1 K → K) :=
    continuous_lowerScalarEntry.measurable
  refine map_skewScalingMap (rankOneExtensionCellExchangeAction H xrow)
    (fun b y => lowerScalarEntry b.2 • y) (fun b => w (lowerScalarEntry b.2))
    (measurable_rankOneExtensionCellExchangeAction H xrow hxrow) ?_
    (measurable_rankOneExtensionCellScaling H) ?_ ?_
  · intro z
    exact (hμQ _).prod (measurePreserving_mul_right ρ _)
  · intro b
    exact hdy _ (lowerScalarEntry_ne_zero b.2)
  · exact hw.comp (hentry.comp measurable_snd)

end CellExchangeMap

section ProductScaling

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T1Space K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] (ν : Measure K) [SigmaFinite ν]

omit [T1Space K] in
/-- Multiplication by `a ≠ 0` scales a finite power of a scalar measure by `χ(a)^(-|ι|)`,
when `x ↦ a x` scales `ν` by `χ(a)⁻¹`. -/
theorem productMeasure_map_const_smul {ι : Type*} [Fintype ι] (χ : K →*₀ ℝ≥0)
    (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν) {a : K} (ha : a ≠ 0) :
    (Measure.pi fun _ : ι => ν).map (fun y => a • y) =
      (((χ a)⁻¹ ^ Fintype.card ι : ℝ≥0) : ℝ≥0∞) • Measure.pi fun _ : ι => ν := by
  classical
  have hdet : det (diagonal fun _ : ι => a) = a ^ Fintype.card ι := by
    rw [det_diagonal, Finset.prod_const, Finset.card_univ]
  have hD : det (diagonal fun _ : ι => a) ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ ha
  have hlin : (fun y : ι → K => a • y) = toLin' (diagonal fun _ : ι => a) := by
    funext y
    ext i
    simp [Matrix.toLin'_apply, mulVec_diagonal]
  rw [hlin, HarmonicAnalysis.productMeasure_map_diagonal ν χ hχ hD, hdet, map_pow, inv_pow,
    Measure.coe_nnreal_smul]

omit [T1Space K] [SigmaFinite ν] in
private theorem measurable_cellScalar' {t : ℕ} {X : Type*} [MeasurableSpace X]
    {xrow : X → Fin (t + 1) → K} (hxrow : Measurable xrow) :
    Measurable fun z : X × (Fin (t + 1) → K) => 1 + xrow z.1 ⬝ᵥ z.2 :=
  (continuous_const.add (continuous_fst.dotProduct continuous_snd)).measurable.comp
    ((hxrow.comp measurable_fst).prodMk measurable_snd)

/-- The exchange hyperplane `{y | 1 + x · y = 0}` is null for a finite power of a σ-finite
atomless measure. -/
theorem productMeasure_cellScalar_eq_zero [NullSingletonClass ν] {t : ℕ} (x : Fin (t + 1) → K) :
    (Measure.pi fun _ : Fin (t + 1) => ν) {y | 1 + x ⬝ᵥ y = 0} = 0 := by
  classical
  by_cases hx : x = 0
  · have he : {y : Fin (t + 1) → K | 1 + x ⬝ᵥ y = 0} = ∅ := by
      ext y
      simp [hx]
    rw [he, measure_empty]
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    exact hx (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  have hpres := measurePreserving_piFinSuccAbove (fun _ : Fin (t + 1) => ν) j
  have hS : MeasurableSet {y : Fin (t + 1) → K | 1 + x ⬝ᵥ y = 0} :=
    (continuous_const.add (continuous_const.dotProduct continuous_id)).measurable
      (measurableSet_singleton 0)
  rw [← (hpres.symm _).measure_preimage_equiv,
    Measure.prod_apply_symm ((MeasurableEquiv.measurable _) hS)]
  have hsec : ∀ z : Fin t → K, ν ((fun a => (a, z)) ⁻¹'
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) => K) j).symm ⁻¹'
        {y | 1 + x ⬝ᵥ y = 0})) = 0 := by
    intro z
    refine Set.Subsingleton.measure_zero ?_ ν
    have hdot : ∀ a : K, x ⬝ᵥ Fin.insertNth j a z =
        x j * a + ∑ i, x (j.succAbove i) * z i := by
      intro a
      simp only [dotProduct, Fin.sum_univ_succAbove _ j, Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove]
    intro a ha a' ha'
    change 1 + x ⬝ᵥ Fin.insertNth j a z = 0 at ha
    change 1 + x ⬝ᵥ Fin.insertNth j a' z = 0 at ha'
    rw [hdot] at ha ha'
    have hmul : x j * a = x j * a' := by linear_combination ha - ha'
    exact mul_left_cancel₀ hj hmul
  exact (lintegral_congr fun z => hsec z).trans lintegral_zero

/-- The exchange hyperplane `{1 + x · y = 0}` is null for `(dx × dy) × μ'`, `dy` a finite
power of a σ-finite atomless measure and `dx`, `μ'` s-finite. -/
theorem prod_cellScalar_eq_zero [NullSingletonClass ν] {t : ℕ} {X B : Type*} [MeasurableSpace X]
    [MeasurableSpace B] (xrow : X → Fin (t + 1) → K) (hxrow : Measurable xrow)
    (dx : Measure X) [SFinite dx] (μ' : Measure B) [SFinite μ'] :
    ((dx.prod (Measure.pi fun _ : Fin (t + 1) => ν)).prod μ')
      {z | 1 + xrow z.1.1 ⬝ᵥ z.1.2 = 0} = 0 := by
  have hS : MeasurableSet {p : X × (Fin (t + 1) → K) | 1 + xrow p.1 ⬝ᵥ p.2 = 0} :=
    measurable_cellScalar' hxrow (measurableSet_singleton 0)
  have he : {z : (X × (Fin (t + 1) → K)) × B | 1 + xrow z.1.1 ⬝ᵥ z.1.2 = 0} =
      {p : X × (Fin (t + 1) → K) | 1 + xrow p.1 ⬝ᵥ p.2 = 0} ×ˢ Set.univ := by
    ext z
    simp
  rw [he, Measure.prod_prod, Measure.prod_apply hS]
  have h0 : ∀ x : X, (Measure.pi fun _ : Fin (t + 1) => ν)
      (Prod.mk x ⁻¹' {p : X × (Fin (t + 1) → K) | 1 + xrow p.1 ⬝ᵥ p.2 = 0}) = 0 :=
    fun x => productMeasure_cellScalar_eq_zero ν (xrow x)
  rw [(lintegral_congr h0).trans lintegral_zero, zero_mul]

end ProductScaling

end Langlands.RankinSelberg
