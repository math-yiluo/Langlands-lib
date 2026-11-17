import Langlands.Global.CompactTorusQuotientIntegral
import Langlands.Global.RankinSelberg.AdelicDiagonalUnipotentModulus
import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge
import Langlands.Global.RankinSelberg.AdelicSchwartzMellinHaar
import Langlands.Global.RankinSelberg.UnfoldingSteps
import Langlands.Global.AdelicGLIwasawa
import Langlands.Global.AdelicGLSiegelShape

/-! # A compact torus criterion on the actual adelic Whittaker quotient -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Measure Set Topology
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.WhittakerCompactTorusIntegral

open UnipotentConjugationModulus AdelicDiagonalUnipotentModulus
open Langlands.HarishChandraSchwartz

local instance torusSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance torusSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance : LocallyCompactSpace (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance : SecondCountableTopology (Ideles F) :=
  (AdelicSchwartzMellin.ideleContinuousEquiv F).symm.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace (Ideles F) := borel _
local instance : BorelSpace (Ideles F) := ⟨rfl⟩

/-- The actual diagonal embedding of the full idele torus. -/
def diagonalHom : (Fin n → Ideles F) →* Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm.toMonoidHom.comp
    (GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F))

@[simp] theorem diagonalHom_apply (d : Fin n → Ideles F) :
    diagonalHom F n d = gaugeDiagonalPoint F n d := rfl

@[simp] theorem matrixOf_diagonal (d : Fin n → Ideles F) :
    matrixOf (gaugeDiagonalPoint F n d) = Matrix.diagonal (fun i => (d i : Adeles F)) := by
  simp only [matrixOf, gaugeDiagonalPoint, MulEquiv.apply_symm_apply,
    GroupScheme.GeneralLinear.diagonalMatrixUnits_val]

theorem diagonalHom_injective : Function.Injective (diagonalHom F n) := by
  intro d e h
  funext i
  apply Units.ext
  have hi := congrArg (fun g : Points F n => matrixOf g i i) h
  simpa only [diagonalHom_apply, matrixOf_diagonal, Matrix.diagonal_apply_eq] using hi

theorem continuous_diagonalHom : Continuous (diagonalHom F n) := by
  apply (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous fun d : Fin n → Ideles F => Matrix.diagonal fun i => (d i : Adeles F)
    exact (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  · change Continuous fun d : Fin n → Ideles F =>
      Matrix.diagonal fun i => (((d i)⁻¹ : Ideles F) : Adeles F)
    exact (continuous_pi fun i => Units.continuous_coe_inv.comp (continuous_apply i)).matrix_diagonal

/-- The actual diagonal subgroup in the adelic point carrier. -/
def diagonalTorus : Subgroup (Points F n) := (diagonalHom F n).range

/-- Algebraic diagonal coordinates. -/
def diagonalEquiv : (Fin n → Ideles F) ≃* diagonalTorus F n :=
  MonoidHom.ofInjective (diagonalHom_injective F n)

@[simp] theorem diagonalEquiv_coe (d : Fin n → Ideles F) :
    (diagonalEquiv F n d : Points F n) = gaugeDiagonalPoint F n d := rfl

theorem diagonalParameters_val (a : diagonalTorus F n) (i : Fin n) :
    ((diagonalEquiv F n).symm a i : Adeles F) = matrixOf (a : Points F n) i i := by
  obtain ⟨d, rfl⟩ := (diagonalEquiv F n).surjective a
  simp only [MulEquiv.symm_apply_apply, diagonalEquiv_coe, matrixOf_diagonal,
    Matrix.diagonal_apply_eq]

theorem diagonalParameters_inv_val (a : diagonalTorus F n) (i : Fin n) :
    ((((diagonalEquiv F n).symm a i)⁻¹ : Ideles F) : Adeles F) =
      matrixOf (a : Points F n)⁻¹ i i := by
  have h := congrArg (fun g : Points F n => matrixOf g⁻¹ i i)
    (MonoidHom.apply_ofInjective_symm (diagonalHom_injective F n) a)
  rw [diagonalHom_apply, matrixOf_inv_of_diagonal (matrixOf_diagonal F n _),
    Matrix.diagonal_apply_eq] at h
  exact h

/-- The actual diagonal subgroup is continuously isomorphic to the idele torus. -/
def diagonalContinuousEquiv : (Fin n → Ideles F) ≃ₜ* diagonalTorus F n where
  toMulEquiv := diagonalEquiv F n
  continuous_toFun := (continuous_diagonalHom F n).subtype_mk _
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous fun a : diagonalTorus F n =>
        ((diagonalEquiv F n).symm a i : Adeles F)
      simp_rw [diagonalParameters_val]
      exact ((continuous_matrixOf (F := F) (m := n)).comp
        continuous_subtype_val).matrix_elem i i
    · change Continuous fun a : diagonalTorus F n =>
        ((((diagonalEquiv F n).symm a i)⁻¹ : Ideles F) : Adeles F)
      simp_rw [diagonalParameters_inv_val]
      exact ((continuous_matrixOf (F := F) (m := n)).comp
        continuous_subtype_val.inv).matrix_elem i i

@[simp] theorem diagonalContinuousEquiv_coe (d : Fin n → Ideles F) :
    (diagonalContinuousEquiv F n d : Points F n) = gaugeDiagonalPoint F n d := rfl

/-- Diagonal points normalize the actual upper unitriangular subgroup. -/
theorem diagonalTorus_normalizes :
    diagonalTorus F n ≤ Subgroup.normalizer (unipotentAdelic F n : Set (Points F n)) := by
  rintro a ⟨d, rfl⟩ x
  exact (conj_mem_iff_of_diagonal (matrixOf_diagonal F n d) x).symm

/-- The positive-root modulus in actual diagonal-subgroup coordinates. -/
def torusModulus : diagonalTorus F n →* ℝ≥0ˣ :=
  (diagonalModulus F n).comp (diagonalEquiv F n).symm.toMonoidHom

@[simp] theorem torusModulus_diagonal (d : Fin n → Ideles F) :
    torusModulus F n (diagonalContinuousEquiv F n d) = diagonalModulus F n d := by
  change diagonalModulus F n ((diagonalEquiv F n).symm (diagonalEquiv F n d)) = _
  rw [MulEquiv.symm_apply_apply]

local instance : LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

/-- The standard compact subgroup transported to the actual point carrier. -/
def standardCompactPoints : Subgroup (Points F n) :=
  (PrimitiveAdelicHeight.standardCompact F n).map
    (GeneralLinearGroupPoints.adelicEquiv F n).symm.toMonoidHom

theorem isCompact_standardCompactPoints :
    IsCompact (standardCompactPoints F n : Set (Points F n)) := by
  exact (PrimitiveAdelicHeight.isCompact_standardCompact F n).image
    (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous

/-- Every actual adelic point has diagonal-unipotent-compact coordinates. -/
theorem exists_diagonal_unipotent_compact (g : Points F n) :
    ∃ a : diagonalTorus F n, ∃ v : unipotentAdelic F n,
      ∃ k ∈ standardCompactPoints F n, g = (a : Points F n) * v * k := by
  classical
  let e := GeneralLinearGroupPoints.adelicEquiv F n
  obtain ⟨b, k, hg, hb, hk⟩ :=
    PrimitiveAdelicHeight.exists_isStandardIwasawaFactorization F n (e g)
  have hb' := (GeneralLinear.mem_upperTriangularSubgroup_iff _).mp hb
  let d : Fin n → Ideles F := PrimitiveAdelicHeight.diagonalUnit b hb'
  let D := GroupScheme.GeneralLinear.diagonalMatrixUnits (Adeles F) d
  let a : diagonalTorus F n := diagonalEquiv F n d
  have hD : (D⁻¹ : AdelicGL F n).val =
      Matrix.diagonal (fun i => (((d i)⁻¹ : Ideles F) : Adeles F)) := rfl
  have hv : e.symm (b * D⁻¹) ∈ unipotentAdelic F n := by
    rw [Unfolding.mem_unipotentAdelic_iff, MulEquiv.apply_symm_apply]
    change PrimitiveAdelicHeight.IsUnitriangular (b.val * (D⁻¹).val)
    rw [hD]
    exact PrimitiveAdelicHeight.isUnitriangular_mul_diagonal hb' d (fun _ => rfl)
  let v : unipotentAdelic F n := ⟨e.symm (b * D⁻¹), hv⟩
  refine ⟨a, conjUnipotent (diagonalTorus_normalizes F n) a⁻¹ v,
    e.symm k, ⟨k, hk, rfl⟩, ?_⟩
  change g = (a : Points F n) *
    ((a : Points F n)⁻¹ * e.symm (b * D⁻¹) * (a : Points F n)⁻¹⁻¹) * e.symm k
  have ha : (a : Points F n) = e.symm D := rfl
  rw [inv_inv, ha]
  calc
    g = e.symm (b * k) := by rw [← hg, MulEquiv.symm_apply_apply]
    _ = _ := by rw [map_mul, map_mul, map_inv]; group

local instance : LocallyCompactSpace (diagonalTorus F n) :=
  (diagonalContinuousEquiv F n).symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
local instance : SecondCountableTopology (diagonalTorus F n) :=
  (diagonalContinuousEquiv F n).symm.toHomeomorph.secondCountableTopology

/-- Transport any idele-torus Haar normalization to the actual diagonal subgroup. -/
def torusMeasure (mu : Measure (Fin n → Ideles F)) : Measure (diagonalTorus F n) :=
  mu.map (diagonalContinuousEquiv F n)

instance torusMeasure_isHaar (mu : Measure (Fin n → Ideles F)) [mu.IsHaarMeasure] :
    (torusMeasure F n mu).IsHaarMeasure :=
  (diagonalContinuousEquiv F n).isHaarMeasure_map mu

variable [CompactSpace (AdeleQuotient F)]

/-- The actual unipotent Haar measure has the expected diagonal conjugation modulus. -/
theorem isConjModulus_torus (nu : Measure (unipotentAdelic F n))
    [nu.IsHaarMeasure] :
    IsConjModulus (diagonalTorus_normalizes F n) nu (torusModulus F n) := by
  intro a
  let d := (diagonalEquiv F n).symm a
  have ha : matrixOf (a : Points F n) = Matrix.diagonal fun i => (d i : Adeles F) := by
    rw [← MonoidHom.apply_ofInjective_symm (diagonalHom_injective F n) a]
    exact matrixOf_diagonal F n d
  let alpha := QuotientIntegration.subgroupAutomorphism (unipotentAdelic F n)
    (conjugation (a : Points F n)) (conj_mem_iff_of_diagonal ha)
  have hc := mulEquivHaarChar_conj_eq_diagonalModulus F ha
    (conj_mem_iff_of_diagonal ha)
  have hh := mulEquivHaarChar_smul_map nu alpha
  have he : (conjUnipotent (diagonalTorus_normalizes F n) a :
      unipotentAdelic F n → unipotentAdelic F n) = alpha := rfl
  rw [he]
  rw [hc] at hh
  change (diagonalModulus F n d : ℝ≥0) • nu.map alpha = nu at hh
  conv_rhs => rw [← hh]
  rw [smul_smul]
  simp only [torusModulus, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    d, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

omit [CompactSpace (AdeleQuotient F)] in
theorem unipotentRationalImage_le_unipotent :
    unipotentRationalImage F n ≤ unipotentAdelic F n := by
  intro x hx
  obtain ⟨l, rfl⟩ := (Unfolding.mem_unipotentRationalImage_iff F n x).mp hx
  exact l.val.property

omit [CompactSpace (AdeleQuotient F)] in
theorem unipotentRationalImage_comap :
    (unipotentRationalImage F n).comap (unipotentAdelic F n).subtype =
      AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n) := by
  ext x
  change (x : Points F n) ∈ unipotentRationalImage F n ↔
    x ∈ AdelicSubgroupPoints.rationalSubgroup F (Scheme F n) (upperUnipotent F n)
  rw [Unfolding.mem_unipotentRationalImage_iff]
  constructor
  · rintro ⟨l, hl⟩
    have he : (l : unipotentAdelic F n) = x := Subtype.ext hl
    rw [← he]
    exact l.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

omit [CompactSpace (AdeleQuotient F)] in
/-- The lower integral for the defined Whittaker measure is the ambient Haar
integral over the chosen rational-unipotent fundamental domain. -/
theorem lintegral_whittakerQuotient_eq (f : Points F n → ℝ≥0∞)
    (hfm : Measurable f)
    (hf : ∀ (v : unipotentAdelic F n) (g : Points F n), f ((v : Points F n) * g) = f g) :
    ∫⁻ q : WhittakerQuotient F n, f q.out ∂whittakerQuotientMeasure F n =
      ∫⁻ g in LeftCosetSpace.fundamentalDomain (unipotentRationalImage F n)
        (isDiscrete_unipotentRationalImage F n), f g ∂Measure.haar := by
  let fQ := LeftCosetSpace.lift (unipotentAdelic F n) f hf
  have hQ : Measurable fQ := measurable_from_quotient.mpr hfm
  rw [Unfolding.out_eq_lift (unipotentAdelic F n) f hf]
  change ∫⁻ q, fQ q ∂whittakerQuotientMeasure F n = _
  rw [whittakerQuotientMeasure, lintegral_map hQ (measurable_toWhittakerQuotient F n)]
  simp only [LeftCosetSpace.haarQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
    LeftCosetSpace.quotientMeasure]
  rw [lintegral_map (show Measurable (fun q => fQ (toWhittakerQuotient F n q)) from
    hQ.comp (measurable_toWhittakerQuotient F n))
    (LeftCosetSpace.measurable_mk (unipotentRationalImage F n))]
  rfl

/-- Compact-uniform inverse-modulus torus bounds imply finiteness on the
actual adelic Whittaker quotient, for any torus Haar normalization. -/
theorem lintegral_whittakerQuotient_lt_top_of_compactTorusBound
    (mu : Measure (Fin n → Ideles F)) [mu.IsHaarMeasure]
    (f : Points F n → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ (v : unipotentAdelic F n) (g : Points F n), f ((v : Points F n) * g) = f g)
    (hbound : ∀ C : Set (Points F n), IsCompact C →
      ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ c ∈ C,
        ∫⁻ d, (((diagonalModulus F n d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
          f (gaugeDiagonalPoint F n d * c) ∂mu ≤ B) :
    ∫⁻ q : WhittakerQuotient F n, f q.out ∂whittakerQuotientMeasure F n < ⊤ := by
  have hbd : LeftCosetSpace.HasCompactTorusBound
      (torusMeasure F n mu) (torusModulus F n) f := by
    intro C hC
    obtain ⟨B, hB, hb⟩ := hbound C hC
    refine ⟨B, hB, fun c hc => ?_⟩
    change (∫⁻ a, (((torusModulus F n a : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
      f ((a : Points F n) * c) ∂mu.map (diagonalContinuousEquiv F n)) ≤ B
    erw [lintegral_map_equiv _
      (diagonalContinuousEquiv F n).toHomeomorph.toMeasurableEquiv]
    change (∫⁻ d, (((torusModulus F n (diagonalContinuousEquiv F n d) : ℝ≥0)⁻¹ :
      ℝ≥0) : ℝ≥0∞) * f ((diagonalContinuousEquiv F n d : Points F n) * c) ∂mu) ≤ B
    simpa only [torusModulus_diagonal, diagonalContinuousEquiv_coe] using hb c hc
  let : Countable ((unipotentRationalImage F n).comap (unipotentAdelic F n).subtype) := by
    rw [unipotentRationalImage_comap]
    exact LeftCosetSpace.countable_of_isDiscrete _
      (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n))
  have ht : IsFundamentalDomain
      ((unipotentRationalImage F n).comap (unipotentAdelic F n).subtype)
      (Unfolding.unipotentFundamentalDomain F n)
      (Measure.haar : Measure (unipotentAdelic F n)) := by
    rw [unipotentRationalImage_comap]
    exact LeftCosetSpace.isFundamentalDomain _
      (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F n) (upperUnipotent F n)) _
  have := Unfolding.compactSpace_unipotentRationalQuotient F n
  have htfinite : (Measure.haar : Measure (unipotentAdelic F n))
      (Unfolding.unipotentFundamentalDomain F n) < ⊤ := by
    rw [Unfolding.haar_unipotentFundamentalDomain]
    exact (ENNReal.inv_ne_top.mpr
      (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero F (Scheme F n)
        (upperUnipotent F n))).lt_top
  rw [lintegral_whittakerQuotient_eq F n f hfm hf]
  exact LeftCosetSpace.lintegral_fundamentalDomain_lt_top_of_compactTorusBound
    Measure.haar (torusMeasure F n mu) Measure.haar
    (diagonalTorus_normalizes F n) (standardCompactPoints F n) (unipotentRationalImage F n)
    (isCompact_standardCompactPoints F n) (unipotentRationalImage_le_unipotent F n)
    (exists_diagonal_unipotent_compact F n)
    (LeftCosetSpace.measurableSet_fundamentalDomain _ (isDiscrete_unipotentRationalImage F n))
    (LeftCosetSpace.fundamentalDomain_unique _ (isDiscrete_unipotentRationalImage F n))
    ht htfinite (torusModulus F n) (isConjModulus_torus F n Measure.haar) f hfm hf hbd

end Langlands.Global.RankinSelbergGlobal.WhittakerCompactTorusIntegral
