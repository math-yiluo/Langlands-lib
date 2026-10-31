import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCompactApproximation
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Group.GL.Nonarchimedean
import Langlands.Group.GL.CountabilityProof

/-! # Compact approximation for actual smooth coefficient-model vectors -/

noncomputable section

namespace Langlands.RankinSelberg.CompactWhittakerApproximation

open MeasureTheory Whittaker Induction GeneralLinear

universe uG uR uV uA uB uF

section ModelInclusion

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]
    {H : Subgroup G} {θ : H →* Rˣ}
    (π : Representation R G V) (hπ : IsSmooth π) (ℓ : functionals H θ π)

/-- A smooth coefficient-model vector, with its unchanged values, in scalar
character smooth induction. -/
def modelSmoothFunction (w : (coefficientModel π ℓ).toSubmodule) :
    SmoothFunctions H (characterRepresentation θ) :=
  let K := Classical.choose (model_isSmooth π hπ ℓ w)
  let hK := Classical.choose_spec (model_isSmooth π hπ ℓ w)
  smoothFunctionOf H (characterRepresentation θ) w.val.val
    (fun h x => w.val.property h x) K
    (fun k x => congrArg
      (fun z : (coefficientModel π ℓ).toSubmodule => z.val.val x) (hK k))

omit [IsTopologicalGroup G] in
@[simp] theorem eval_modelSmoothFunction
    (w : (coefficientModel π ℓ).toSubmodule) (g : G) :
    eval H (characterRepresentation θ) (modelSmoothFunction π hπ ℓ w) g =
      w.val.val g := rfl

/-- The actual equivariant inclusion of a smooth coefficient model into scalar
character smooth induction. -/
def modelSmoothInclusion :
    (modelRepresentation π ℓ).IntertwiningMap
      (smoothInduced H (characterRepresentation θ)) where
  toLinearMap :=
    { toFun := modelSmoothFunction π hπ ℓ
      map_add' w z := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      map_smul' a w := by
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The inclusion loses no coefficient-model vectors. -/
theorem modelSmoothInclusion_injective :
    Function.Injective (modelSmoothInclusion π hπ ℓ) := by
  intro w z h
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact congrArg (fun f => eval H (characterRepresentation θ) f g) h

end ModelInclusion

section ModelComparison

variable {G : Type uG} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {A : Type uA} {B : Type uB} [MeasurableSpace A] [MeasurableSpace B]

/-- A compact character-function identity extends to every actual smooth
coefficient-model vector with integrable weighted restrictions. -/
theorem weighted_model_integral_eq_of_compact
    (μ : Measure A) (ν : Measure B)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (θ : H →* ℂˣ)
    (π : Representation ℂ G V) (hπ : IsSmooth π) (ℓ : functionals H θ π)
    (ρ : A → G) (τ : B → G) (w : A → ℂ) (v : B → ℂ)
    (hρ : Measurable ρ) (hτ : Measurable τ)
    (hcompact : ∀ f : CompactFunctions H (characterRepresentation θ),
      (∫ a, w a * eval H (characterRepresentation θ) f.val (ρ a) ∂μ) =
      ∫ b, v b * eval H (characterRepresentation θ) f.val (τ b) ∂ν)
    (f : (coefficientModel π ℓ).toSubmodule)
    (hi : Integrable (fun a => w a * f.val.val (ρ a)) μ)
    (hj : Integrable (fun b => v b * f.val.val (τ b)) ν) :
    (∫ a, w a * f.val.val (ρ a) ∂μ) =
      ∫ b, v b * f.val.val (τ b) ∂ν :=
  weighted_integral_eq_of_compact μ ν H hH (characterRepresentation θ)
    ρ τ w v hρ hτ hcompact (modelSmoothFunction π hπ ℓ f) hi hj

end ModelComparison

section CanonicalPadic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelApproximationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance modelApproximationValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance modelApproximationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance modelApproximationT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance modelApproximationGLNonarchimedean (n : ℕ) :
    NonarchimedeanGroup (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  valuativeGeneralLinearNonarchimedean F.Carrier (n + 1)
local instance modelApproximationGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance modelApproximationGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)
local instance modelApproximationGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance modelApproximationGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {A : Type uA} {B : Type uB} [MeasurableSpace A] [MeasurableSpace B]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Canonical p-adic GL specialization for an actual Whittaker model, using
only smoothness of the original representation and the two weighted bounds. -/
theorem weighted_glModel_integral_eq_of_compact
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ n π)
    (μ : Measure A) (ν : Measure B)
    (ρ : A → Langlands.GeneralLinear (n + 1) F.Carrier)
    (τ : B → Langlands.GeneralLinear (n + 1) F.Carrier)
    (w : A → ℂ) (v : B → ℂ) (hρ : Measurable ρ) (hτ : Measurable τ)
    (hcompact : ∀ f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
        (characterRepresentation (standardCharacter ψ n)),
      (∫ a, w a * eval _ _ f.val (ρ a) ∂μ) =
      ∫ b, v b * eval _ _ f.val (τ b) ∂ν)
    (f : (glCoefficientModel ψ n π ℓ).toSubmodule)
    (hi : Integrable (fun a => w a * glModelFunction ψ n π ℓ f (ρ a)) μ)
    (hj : Integrable (fun b => v b * glModelFunction ψ n π ℓ f (τ b)) ν) :
    (∫ a, w a * glModelFunction ψ n π ℓ f (ρ a) ∂μ) =
      ∫ b, v b * glModelFunction ψ n π ℓ f (τ b) ∂ν :=
  weighted_model_integral_eq_of_compact μ ν (upperUnipotent (n + 1) F.Carrier)
    UpperUnipotent.isClosed (standardCharacter ψ n) π hπ ℓ
    ρ τ w v hρ hτ hcompact f hi hj

end CanonicalPadic

end Langlands.RankinSelberg.CompactWhittakerApproximation
