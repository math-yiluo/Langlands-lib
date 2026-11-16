import Langlands.Global.RankinSelberg.FourierStandardOutsideProof
import Langlands.Global.RankinSelberg.RectangleModulusStatement
import Langlands.Global.RankinSelberg.EqualAnalyticModulus

/-! # Proof: the modulus of right multiplication on adelic rectangular matrices

For `g ∈ GL_m(𝔸)`, the pushforward of `rectangleMeasure F k m` under `x ↦ x g` is
`|det g|_𝔸^{-k} • rectangleMeasure F k m`. The `k` rows of `x` are moved independently, so the
statement follows from the Library's one-row theorem
`EqualAnalytic.map_rightMul_rectangleMeasure` and uniqueness of Haar measure.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace RectangleModulus

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]

local instance rectModMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance rectModBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance rectModAdelesT2 : T2Space (Adeles F) := EqualAnalytic.t2Space_adeles F

local instance rectModAdelesLocallyCompact : LocallyCompactSpace (Adeles F) :=
  adeles_locallyCompactSpace F

local instance rectModAdelesSecondCountable : SecondCountableTopology (Adeles F) :=
  adeles_secondCountableTopology F

local instance rectModLocallyCompact (k m : ℕ) :
    LocallyCompactSpace (Matrix (Fin k) (Fin m) (Adeles F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin k → Fin m → Adeles F))

local instance rectModSecondCountable (k m : ℕ) :
    SecondCountableTopology (Matrix (Fin k) (Fin m) (Adeles F)) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin m → Adeles F))

local instance rectModGeneralLinearAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance rectModGeneralLinearSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-! ### `rectangleMeasure F k m` is invariant and finite on compact sets -/

/-- The actual adelic two-block unipotent subgroup whose coordinates are `k × m` matrices. -/
abbrev BlockGroup (k m : ℕ) :=
  AdelicSubgroupPoints.adelicPoints F
    (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
    (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl))

local instance rectModBlockClosed (k m : ℕ) :
    IsClosed (BlockGroup F k m : Set (AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F)))) :=
  GeneralLinearBlockUnipotent.isClosed_adelicPoints F (show k + m = k + m from rfl)

local instance rectModBlockLocallyCompact (k m : ℕ) : LocallyCompactSpace (BlockGroup F k m) :=
  (GeneralLinearBlockUnipotent.isClosed_adelicPoints F
    (show k + m = k + m from rfl)).locallyCompactSpace

theorem blockHomeomorph_apply (k m : ℕ) (x : BlockGroup F k m) :
    rectangleCoordinateHomeomorph F k m x =
      (GeneralLinearBlockUnipotent.adelicCoordinates F (show k + m = k + m from rfl) x).toAdd :=
  rfl

theorem blockHomeomorph_mul (k m : ℕ) (x y : BlockGroup F k m) :
    rectangleCoordinateHomeomorph F k m (x * y) = rectangleCoordinateHomeomorph F k m x + rectangleCoordinateHomeomorph F k m y := by
  simp only [blockHomeomorph_apply, map_mul, toAdd_mul]

/-- `rectangleMeasure` is the image of the normalized block Haar measure. -/
theorem rectangleMeasure_eq_map_blockHomeomorph (k m : ℕ) :
    rectangleMeasure F k m = Measure.map (rectangleCoordinateHomeomorph F k m)
      (GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure F
        (show k + m = k + m from rfl)) :=
  rfl

theorem normalizedBlockHaarMeasure_isMulLeftInvariant (k m : ℕ) :
    (GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure F
      (show k + m = k + m from rfl)).IsMulLeftInvariant := by
  unfold GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure
    AdelicSubgroupPoints.normalizedHaarMeasure
  infer_instance

theorem normalizedBlockHaarMeasure_isFiniteMeasureOnCompacts (k m : ℕ) :
    IsFiniteMeasureOnCompacts (GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure F
      (show k + m = k + m from rfl)) := by
  unfold GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure
    AdelicSubgroupPoints.normalizedHaarMeasure
  exact IsFiniteMeasureOnCompacts.smul _
    (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F _ _)

instance rectangleMeasure_isAddLeftInvariant (k m : ℕ) :
    (rectangleMeasure F k m).IsAddLeftInvariant := by
  have := normalizedBlockHaarMeasure_isMulLeftInvariant F k m
  constructor
  intro v
  rw [rectangleMeasure_eq_map_blockHomeomorph,
    Measure.map_map (by fun_prop) (rectangleCoordinateHomeomorph F k m).measurable]
  have heq : (fun w : Matrix (Fin k) (Fin m) (Adeles F) => v + w) ∘ rectangleCoordinateHomeomorph F k m =
      rectangleCoordinateHomeomorph F k m ∘ fun x => (rectangleCoordinateHomeomorph F k m).symm v * x := by
    funext x
    simp only [Function.comp_apply, blockHomeomorph_mul, Homeomorph.apply_symm_apply]
  rw [heq, ← Measure.map_map (rectangleCoordinateHomeomorph F k m).measurable (by fun_prop),
    map_mul_left_eq_self]

instance rectangleMeasure_isFiniteMeasureOnCompacts (k m : ℕ) :
    IsFiniteMeasureOnCompacts (rectangleMeasure F k m) := by
  have := normalizedBlockHaarMeasure_isFiniteMeasureOnCompacts F k m
  constructor
  intro K hK
  rw [rectangleMeasure_eq_map_blockHomeomorph,
    Measure.map_apply (rectangleCoordinateHomeomorph F k m).measurable hK.measurableSet]
  exact ((rectangleCoordinateHomeomorph F k m).isCompact_preimage.mpr hK).measure_lt_top

/-! ### Rows -/

/-- A `k × m` matrix as the family of its `k` rows, each a `1 × m` matrix. -/
def rowsEquiv (k m : ℕ) :
    Matrix (Fin k) (Fin m) (Adeles F) ≃ₜ+ (Fin k → Matrix (Fin 1) (Fin m) (Adeles F)) where
  toFun x i := Matrix.of fun _ j => x i j
  invFun y := Matrix.of fun i j => y i 0 j
  left_inv x := by
    ext i j
    rfl
  right_inv y := by
    funext i
    ext a j
    rw [Subsingleton.elim a 0]
    rfl
  map_add' x y := by
    funext i
    ext a j
    rfl
  continuous_toFun := continuous_pi fun i => continuous_matrix fun _ j =>
    continuous_id.matrix_elem i j
  continuous_invFun := continuous_matrix fun i j => (continuous_apply i).matrix_elem 0 j

theorem rowsEquiv_symm_apply (k m : ℕ) (y : Fin k → Matrix (Fin 1) (Fin m) (Adeles F))
    (i : Fin k) (j : Fin m) :
    (rowsEquiv F k m).symm y i j = y i 0 j :=
  rfl

/-- The product of `k` copies of the one-row measure, on families of rows. -/
def rowsMeasure (k m : ℕ) : Measure (Fin k → Matrix (Fin 1) (Fin m) (Adeles F)) :=
  Measure.pi fun _ : Fin k => rectangleMeasure F 1 m

/-- The product measure, transported to `M_{k×m}(𝔸)`. -/
def productRectangleMeasure (k m : ℕ) : Measure (Matrix (Fin k) (Fin m) (Adeles F)) :=
  Measure.map (rowsEquiv F k m).symm (rowsMeasure F k m)

/-- A product of `k` copies of `r • ν` is `r ^ k` times the product of copies of `ν`. -/
theorem pi_const_smul {X : Type*} [MeasurableSpace X] (k : ℕ) (ν : Measure X) [SigmaFinite ν]
    (r : ℝ≥0∞) [SigmaFinite (r • ν)] :
    Measure.pi (fun _ : Fin k => r • ν) = r ^ k • Measure.pi (fun _ : Fin k => ν) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

variable [CompactSpace (AdeleQuotient F)]

/-- The transported product of the one-row Haar measures is an additive Haar measure. -/
instance productRectangleMeasure_isAddHaarMeasure (k m : ℕ) :
    (productRectangleMeasure F k m).IsAddHaarMeasure := by
  unfold productRectangleMeasure rowsMeasure
  have : (Measure.pi fun _ : Fin k => rectangleMeasure F 1 m).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  exact ContinuousAddEquiv.isAddHaarMeasure_map _ (rowsEquiv F k m).symm

/-- Right multiplication by `g` on each row scales the product measure by `|det g|^{-k}`. -/
theorem map_rowwise_rowsMeasure (k m : ℕ) (g : AdelicGL F m) :
    Measure.map (fun y i => EqualAnalytic.rightMul F m g (y i)) (rowsMeasure F k m) =
      ENNReal.ofReal (absDet F m g)⁻¹ ^ k • rowsMeasure F k m := by
  have hrow := EqualAnalytic.map_rightMul_rectangleMeasure F m g
  have : SigmaFinite (ENNReal.ofReal (absDet F m g)⁻¹ • rectangleMeasure F 1 m) := by
    rw [← hrow]
    infer_instance
  have hφ : Measurable ⇑(EqualAnalytic.rightMul F m g) :=
    (EqualAnalytic.rightMul F m g).continuous.measurable
  unfold rowsMeasure
  rw [Measure.pi_map_pi fun _ => hφ.aemeasurable]
  simp_rw [hrow]
  exact pi_const_smul _ _ _

/-- **Change of variables** `x ↦ x g` on `M_{k×m}(𝔸)`, for `g ∈ GL_m(𝔸)` as a matrix unit. -/
theorem map_mul_rectangleMeasure (k m : ℕ) (g : AdelicGL F m) :
    Measure.map (fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
        x * (g : Matrix (Fin m) (Fin m) (Adeles F)))
      (rectangleMeasure F k m) =
      ENNReal.ofReal ((absDet F m g ^ k)⁻¹) • rectangleMeasure F k m := by
  have hmul : Measurable (fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
      x * (g : Matrix (Fin m) (Fin m) (Adeles F))) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have he : Measurable (rowsEquiv F k m).symm := (rowsEquiv F k m).symm.continuous.measurable
  have hrows : Measurable (fun (y : Fin k → Matrix (Fin 1) (Fin m) (Adeles F)) i =>
      EqualAnalytic.rightMul F m g (y i)) :=
    measurable_pi_iff.mpr fun i =>
      (EqualAnalytic.rightMul F m g).continuous.measurable.comp (measurable_pi_apply i)
  have hcomm : (fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
      x * (g : Matrix (Fin m) (Fin m) (Adeles F))) ∘ (rowsEquiv F k m).symm =
      (rowsEquiv F k m).symm ∘ fun y i => EqualAnalytic.rightMul F m g (y i) := by
    funext y
    ext i j
    simp only [Function.comp_apply, Matrix.mul_apply, rowsEquiv_symm_apply,
      EqualAnalytic.rightMul_apply]
  have hr : ENNReal.ofReal (absDet F m g)⁻¹ ^ k = ENNReal.ofReal ((absDet F m g ^ k)⁻¹) := by
    rw [← ENNReal.ofReal_pow (inv_nonneg.mpr (absDet_pos F m g).le), inv_pow]
  have hprod : Measure.map (fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
      x * (g : Matrix (Fin m) (Fin m) (Adeles F))) (productRectangleMeasure F k m) =
      ENNReal.ofReal ((absDet F m g ^ k)⁻¹) • productRectangleMeasure F k m := by
    unfold productRectangleMeasure
    rw [Measure.map_map hmul he, hcomm, ← Measure.map_map he hrows,
      map_rowwise_rowsMeasure, Measure.map_smul _ he.aemeasurable, hr]
  have huniq := Measure.isAddLeftInvariant_eq_smul (rectangleMeasure F k m)
    (productRectangleMeasure F k m)
  rw [huniq, Measure.map_smul _ hmul.aemeasurable, hprod, smul_comm]

end RectangleModulus

/-- **The modulus of right multiplication on `M_{k×m}(𝔸)`**: the pushforward of
`rectangleMeasure F k m` under `x ↦ x g` is `|det g|_𝔸^{-k} • rectangleMeasure F k m`. -/
theorem rectangleMeasureModulus : RectangleMeasureModulusStatement.{u} := by
  intro F _ _ _ k m g
  exact RectangleModulus.map_mul_rectangleMeasure F k m
    (GeneralLinearGroupPoints.adelicEquiv F m g)

end Langlands.Global.RankinSelbergGlobal
