import Langlands.Representation.RankinSelberg.AdjacentRankDualModelZetaCoefficient
import Langlands.Representation.RankinSelberg.ModelMinusOneScalar
import Langlands.Representation.GodementJacquet.CoefficientTwistAndDual

/-! The actual reflected square-test scalar in the dual adjacent-rank formula. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uG

private theorem biSmoothCoefficient_scalarAction
    {G : Type uG} [Group G] [TopologicalSpace G]
    {X : Type uV} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (z : G) (c : ℂ)
    (hact : ∀ x, ρ z x = c • x)
    (f : GodementJacquet.biSmoothMatrixCoefficients ρ) :
    ∀ g, f.val (z * g) = c * f.val g := by
  have hf := f.property
  generalize hfa : f.val = a at hf ⊢
  clear hfa f
  induction hf using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨L, v, rfl⟩ := ha
    intro g
    change L.val (ρ (z * g) v.val) = c * L.val (ρ g v.val)
    rw [map_mul, Module.End.mul_apply, hact, map_smul]
    rfl
  | zero => intro g; simp
  | add a b ha hb iha ihb => intro g; simp [iha g, ihb g, mul_add]
  | smul a b hb ih => intro g; simp [ih g, mul_left_comm]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance reflectionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance reflectionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance reflectionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance reflectionFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance reflectionFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance reflectionFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance reflectionGroupMeasurable (r : ℕ) : MeasurableSpace
    (GeneralLinear (r + 1) F.Carrier) := borel _
local instance reflectionGroupBorel (r : ℕ) : BorelSpace
    (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

attribute [local irreducible] coefficientModel modelRepresentation
  GodementJacquet.biSmoothMatrixCoefficients

/-- The scalar from reflecting the dual square test for the inverse
determinant twist of an actual model coefficient. -/
def adjacentRankDualMatrixReflectionScalar
    (χ : Quasicharacter F.Carrier) (r : ℕ) (ζ : ℂˣ) : ℂˣ :=
  χ⁻¹ (determinant (-1 : GeneralLinear (r + 1) F.Carrier)) * ζ

/-- Scalar action on the actual coefficient image gives the same scalar
on every actual bi-smooth coefficient of its right-translation action. -/
theorem biSmoothModelCoefficient_minusOne {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r τ) (ζ : ℂˣ)
    (hζ : HasModelMinusOneScalar τ ℓ ζ)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r τ ℓ).toSubmodule)
      (glModelRepresentation ψ r τ ℓ)) :
    ∀ g, f.val ((-1) * g) = (ζ : ℂ) * f.val g := by
  have hact (W : (glCoefficientModel ψ r τ ℓ).toSubmodule) :
      glModelRepresentation ψ r τ ℓ (-1) W = (ζ : ℂ) • W := by
    unfold glModelRepresentation modelRepresentation
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change W.val.val (g * (-1)) = (ζ : ℂ) * W.val.val g
    have hc : g * (-1) = (-1) * g := by apply Units.ext; simp
    rw [hc]
    exact hζ W g
  exact biSmoothCoefficient_scalarAction
    (G := GeneralLinear (r + 1) F.Carrier)
    (X := (glCoefficientModel ψ r τ ℓ).toSubmodule)
    (glModelRepresentation ψ r τ ℓ) (-1) ζ hact f

private theorem inverseTranspose_minusOne {r : ℕ} :
    inverseTranspose (r + 1) F.Carrier (-1) =
      (-1 : GeneralLinear (r + 1) F.Carrier) := by
  apply Units.ext
  simp [inverseTranspose_coe]

/-- The actual inverse-transpose coefficient and inverse determinant
character have the indicated central reflection scalar. -/
theorem adjacentRankDualMatrixCoefficient_minusOne {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r τ) (ζ : ℂˣ)
    (hζ : HasModelMinusOneScalar τ ℓ ζ)
    (χ : Quasicharacter F.Carrier)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r τ ℓ).toSubmodule)
      (glModelRepresentation ψ r τ ℓ))
    (g : GeneralLinear (r + 1) F.Carrier) :
    (χ⁻¹ (determinant ((-1) * g)) : ℂ) *
        GodementJacquet.coefficientIota f.val ((-1) * g) =
      (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ) *
        ((χ⁻¹ (determinant g) : ℂ) * GodementJacquet.coefficientIota f.val g) := by
  have hfi : GodementJacquet.coefficientIota f.val ((-1) * g) =
      (ζ : ℂ) * GodementJacquet.coefficientIota f.val g := by
    dsimp only [GodementJacquet.coefficientIota]
    rw [map_mul, inverseTranspose_minusOne F]
    exact biSmoothModelCoefficient_minusOne F ψ τ ℓ ζ hζ f _
  rw [hfi, map_mul, map_mul, Units.val_mul]
  simp only [adjacentRankDualMatrixReflectionScalar, Units.val_mul]
  ring

private theorem reflected_matrixIntegrand_mul_minusOne {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (v : GeneralLinear (r + 1) F.Carrier → ℂ)
    (η : ℂˣ) (hv : ∀ g, v ((-1) * g) = (η : ℂ) * v g)
    (s : ℂ) (g : GeneralLinear (r + 1) F.Carrier) :
    GodementJacquet.matrixIntegrand abv (adjacentRankReflectedTest Φ) s v ((-1) * g) =
      (η : ℂ) * GodementJacquet.matrixIntegrand abv Φ s v g := by
  have hw : determinantWeight abv (-1 : GeneralLinear (r + 1) F.Carrier) s = 1 := by
    simp [determinantWeight, Units.val_neg, Units.val_one, Matrix.det_neg]
  simp only [GodementJacquet.matrixIntegrand, adjacentRankReflectedTest_apply,
    hv, determinantWeight_mul, hw, one_mul, Units.val_mul, Units.val_neg, Units.val_one,
    Matrix.neg_mul, neg_neg]
  ring

/-- Reflection preserves genuine matrix convergence, and the literal
matrix integral changes by exactly the supplied central scalar. -/
theorem adjacentRankMatrix_reflection {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (v : GeneralLinear (r + 1) F.Carrier → ℂ)
    (η : ℂˣ) (hv : ∀ g, v ((-1) * g) = (η : ℂ) * v g) (s : ℂ) :
    (GodementJacquet.Padic.MatrixConverges F (adjacentRankReflectedTest Φ) s v ↔
      GodementJacquet.Padic.MatrixConverges F Φ s v) ∧
    GodementJacquet.Padic.matrixIntegral F (adjacentRankReflectedTest Φ) s v =
      (η : ℂ) * GodementJacquet.Padic.matrixIntegral F Φ s v := by
  let μ := generalLinearHaar F.Carrier r
  have hp := reflected_matrixIntegrand_mul_minusOne F Φ v η hv s
  have hfun : GodementJacquet.matrixIntegrand abv (adjacentRankReflectedTest Φ) s v ∘
      (fun g : GeneralLinear (r + 1) F.Carrier => (-1) * g) =
      fun g => (η : ℂ) * GodementJacquet.matrixIntegrand abv Φ s v g := funext hp
  constructor
  · change Integrable _ μ ↔ Integrable _ μ
    rw [← (measurePreserving_mul_left μ (-1)).integrable_comp_emb
      (Homeomorph.mulLeft (-1 : GeneralLinear (r + 1) F.Carrier)).measurableEmbedding,
      hfun]
    exact integrable_const_mul_iff η.isUnit _
  · change (∫ g, GodementJacquet.matrixIntegrand abv (adjacentRankReflectedTest Φ) s v g
      ∂μ) = (η : ℂ) * ∫ g, GodementJacquet.matrixIntegrand abv Φ s v g ∂μ
    rw [← integral_mul_left_eq_self
      (GodementJacquet.matrixIntegrand abv (adjacentRankReflectedTest Φ) s v) (-1)]
    simp_rw [hp]
    exact integral_const_mul _ _

/-- The actual shifted rational value of the reflected square test is the
constant scalar multiple of the original shifted rational value. -/
theorem adjacentRankMatrix_reflectedRationalValue {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (v : GeneralLinear (r + 1) F.Carrier → ℂ)
    (η : ℂˣ) (hv : ∀ g, v ((-1) * g) = (η : ℂ) * v g)
    (M : RationalFunctions)
    (hM : GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F.Carrier r) Φ v M) :
    GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F.Carrier r) (adjacentRankReflectedTest Φ) v
      (RatFunc.C (η : ℂ) * M) := by
  constructor
  · obtain ⟨a, ha⟩ := hM.1
    exact ⟨a, fun s hs => (adjacentRankMatrix_reflection F Φ v η hv _).1.mpr (ha s hs)⟩
  · exact RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul (η : ℂ) hM.2)
      ⟨0, fun s _ => (adjacentRankMatrix_reflection F Φ v η hv _).2⟩

private theorem scalar_minusOne {r : ℕ} :
    scalar (n := r + 1) (-1 : F.Carrierˣ) =
      (-1 : GeneralLinear (r + 1) F.Carrier) := by
  apply Units.ext
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Units.val_neg, Units.val_one, Matrix.neg_apply, hij]

/-- The model-star scalar and the square-test reflection leave precisely
the actual second model's minus-one scalar. -/
theorem adjacentRankModelStar_reflectionScalar_cancel
    (χ : Quasicharacter F.Carrier) (r : ℕ) (ζ : ℂˣ) :
    adjacentRankModelStarScalar F χ r *
      (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ) = (ζ : ℂ) := by
  have hs : χ⁻¹ (determinant (-1 : GeneralLinear (r + 1) F.Carrier)) *
      χ⁻¹ (determinant (-1 : GeneralLinear (r + 1) F.Carrier)) = 1 := by
    rw [← map_mul, ← map_mul]
    simp
  simp only [adjacentRankModelStarScalar, scalar_minusOne F,
    adjacentRankDualMatrixReflectionScalar, Units.val_mul]
  rw [← mul_assoc, ← Units.val_mul, hs, Units.val_one, one_mul]

/-- The same cancellation holds for the actual rational finite sum, so the
reflection scalar changes the equal-rank sign by exactly one power. -/
theorem adjacentRankModelStar_reflectedProduct_cancel
    (χ : Quasicharacter F.Carrier) (r N : ℕ) (ζ : ℂˣ)
    (A M : Fin N → RationalFunctions) :
    RatFunc.C (adjacentRankModelStarScalar F χ r) *
        (∑ i, A i * (RatFunc.C
          (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ) * M i)) =
      RatFunc.C (ζ : ℂ) * ∑ i, A i * M i := by
  have hc : RatFunc.C (adjacentRankModelStarScalar F χ r) *
      RatFunc.C (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ) =
      RatFunc.C (ζ : ℂ) := by
    rw [← map_mul, adjacentRankModelStar_reflectionScalar_cancel]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (RatFunc.C (adjacentRankModelStarScalar F χ r) *
        RatFunc.C (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ)) *
        (A i * M i) := by ring
    _ = _ := by rw [hc]

end Langlands.RankinSelberg.Padic
