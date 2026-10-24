import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Analysis.Local.QuotientMeasure
import Langlands.HarmonicAnalysis.AlgebraicIntegrand
import Langlands.HarmonicAnalysis.AlgebraicIntegral
import Mathlib.RepresentationTheory.Coinvariants

/-! The actual quotient integral from compact induction to inducing coinvariants. -/

noncomputable section

namespace Langlands.Induction

open MeasureTheory
open Langlands.HarmonicAnalysis

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (H : Subgroup G) (σ : Representation ℂ H V)

/-- Projection to inducing coinvariants removes the left covariance. -/
theorem coinvariant_eval_left_mul (f : CompactFunctions H σ) (h : H) (x : G) :
    Representation.Coinvariants.mk σ (eval H σ f.val ((h : G) * x)) =
      Representation.Coinvariants.mk σ (eval H σ f.val x) := by
  rw [eval_covariant, Representation.Coinvariants.mk_self_apply]

/-- The actual function on `H * g` with value the class of `f(g)`. -/
def quotientCoinvariantFunction (f : CompactFunctions H σ) :
    QuotientIntegration.LeftQuotient H → Representation.Coinvariants σ :=
  QuotientIntegration.descend H
    (fun x => Representation.Coinvariants.mk σ (eval H σ f.val x))
    (coinvariant_eval_left_mul H σ f)

@[simp]
theorem quotientCoinvariantFunction_mk (f : CompactFunctions H σ) (x : G) :
    quotientCoinvariantFunction H σ f (quotientMap H x) =
      Representation.Coinvariants.mk σ (eval H σ f.val x) := rfl

/-- Local constancy descends through the quotient topology. -/
theorem quotientCoinvariantFunction_isLocallyConstant (f : CompactFunctions H σ) :
    IsLocallyConstant (quotientCoinvariantFunction H σ f) := by
  intro s
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel H)).isCoinducing.isOpen_preimage.mp
  exact (eval_isLocallyConstant H σ f.val).comp (Representation.Coinvariants.mk σ) s

/-- Projection of values can only shrink the original quotient support. -/
theorem support_quotientCoinvariantFunction_subset (f : CompactFunctions H σ) :
    Function.support (quotientCoinvariantFunction H σ f) ⊆
      quotientSupport H (eval H σ f.val) := by
  intro q hq
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  refine ⟨x, ?_, rfl⟩
  intro hx
  apply hq
  change Representation.Coinvariants.mk σ (eval H σ f.val x) = 0
  rw [hx, map_zero]

/-- Compact support follows from the compact, closed original quotient support. -/
theorem quotientCoinvariantFunction_hasCompactSupport (f : CompactFunctions H σ) :
    HasCompactSupport (quotientCoinvariantFunction H σ f) := by
  apply f.property.of_isClosed_subset isClosed_closure
  exact closure_minimal (support_quotientCoinvariantFunction_subset H σ f)
    (isClosed_quotientSupport H σ f.val)

/-- Right translation agrees with the actual right action on the left quotient. -/
theorem quotientCoinvariantFunction_translate (g : G) (f : CompactFunctions H σ)
    (q : QuotientIntegration.LeftQuotient H) :
    quotientCoinvariantFunction H σ (compactInduced H σ g f) q =
      quotientCoinvariantFunction H σ f (QuotientIntegration.rightTranslate H g q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- The descended function commutes with every algebraic inducing intertwiner. -/
theorem quotientCoinvariantFunction_natural {τ : Representation ℂ H W}
    (T : σ.IntertwiningMap τ) (f : CompactFunctions H σ)
    (q : QuotientIntegration.LeftQuotient H) :
    quotientCoinvariantFunction H τ (compactInducedMap H T f) q =
      Representation.Coinvariants.map σ τ T (quotientCoinvariantFunction H σ f q) := by
  induction q using Quotient.inductionOn with
  | h x => rfl

variable [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
variable [BorelSpace (QuotientIntegration.LeftQuotient H)]

/-- The descended function as an actual finite-image simple function. -/
def quotientCoinvariantSimple (f : CompactFunctions H σ) :
    SimpleFunc (QuotientIntegration.LeftQuotient H) (Representation.Coinvariants σ) :=
  compactlySupportedSimpleFunc (quotientCoinvariantFunction H σ f)
    (quotientCoinvariantFunction_isLocallyConstant H σ f)
    (quotientCoinvariantFunction_hasCompactSupport H σ f)

@[simp]
theorem quotientCoinvariantSimple_apply (f : CompactFunctions H σ)
    (q : QuotientIntegration.LeftQuotient H) :
    quotientCoinvariantSimple H σ f q = quotientCoinvariantFunction H σ f q := rfl

/-- Passing to the actual simple functions is linear. -/
def quotientCoinvariantSimpleLinear : CompactFunctions H σ →ₗ[ℂ]
    SimpleFunc (QuotientIntegration.LeftQuotient H) (Representation.Coinvariants σ) where
  toFun := quotientCoinvariantSimple H σ
  map_add' f k := by
    ext q
    induction q using Quotient.inductionOn with
    | h x =>
      change Representation.Coinvariants.mk σ (eval H σ f.val x + eval H σ k.val x) = _
      exact map_add (Representation.Coinvariants.mk σ) _ _
  map_smul' c f := by
    ext q
    induction q using Quotient.inductionOn with
    | h x =>
      change Representation.Coinvariants.mk σ (c • eval H σ f.val x) = _
      exact map_smul (Representation.Coinvariants.mk σ) c _

variable (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]

/-- Finiteness on compact sets suffices for every nonzero fiber. -/
theorem quotientCoinvariantSimple_finMeasSupp (f : CompactFunctions H σ) :
    (quotientCoinvariantSimple H σ f).FinMeasSupp ν :=
  compactlySupportedSimpleFunc_finMeasSupp ν _
    (quotientCoinvariantFunction_isLocallyConstant H σ f)
    (quotientCoinvariantFunction_hasCompactSupport H σ f)

/-- Quotient integration by the finite fiber sum, with no topology on the values. -/
def compactCoinvariantIntegral :
    CompactFunctions H σ →ₗ[ℂ] Representation.Coinvariants σ where
  toFun f := AlgebraicIntegral.integral ν (quotientCoinvariantSimple H σ f)
  map_add' f k := by
    change AlgebraicIntegral.integral ν (quotientCoinvariantSimpleLinear H σ (f + k)) = _
    rw [map_add]
    exact AlgebraicIntegral.integral_add _ _
      (quotientCoinvariantSimple_finMeasSupp H σ ν f)
      (quotientCoinvariantSimple_finMeasSupp H σ ν k)
  map_smul' c f := by
    change AlgebraicIntegral.integral ν (quotientCoinvariantSimpleLinear H σ (c • f)) = _
    rw [map_smul]
    exact AlgebraicIntegral.integral_smul c _
      (quotientCoinvariantSimple_finMeasSupp H σ ν f)

/-- The defining formula is the actual finite-fiber algebraic integral. -/
theorem compactCoinvariantIntegral_apply (f : CompactFunctions H σ) :
    compactCoinvariantIntegral H σ ν f =
      AlgebraicIntegral.integral ν (quotientCoinvariantSimple H σ f) := rfl

/-- Naturality before descent, for every algebraic inducing intertwiner. -/
theorem compactCoinvariantIntegral_natural {τ : Representation ℂ H W}
    (T : σ.IntertwiningMap τ) (f : CompactFunctions H σ) :
    compactCoinvariantIntegral H τ ν (compactInducedMap H T f) =
      Representation.Coinvariants.map σ τ T (compactCoinvariantIntegral H σ ν f) := by
  have he : quotientCoinvariantSimple H τ (compactInducedMap H T f) =
      (quotientCoinvariantSimple H σ f).map (Representation.Coinvariants.map σ τ T) := by
    ext q
    exact quotientCoinvariantFunction_natural H σ T f q
  rw [compactCoinvariantIntegral_apply, he]
  exact AlgebraicIntegral.integral_linearMap _
    (quotientCoinvariantSimple_finMeasSupp H σ ν f) _

variable (hν : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)

include hν in
/-- Right invariance is proved from measure-preserving change of variables. -/
theorem compactCoinvariantIntegral_translate (g : G) (f : CompactFunctions H σ) :
    compactCoinvariantIntegral H σ ν (compactInduced H σ g f) =
      compactCoinvariantIntegral H σ ν f := by
  have he : quotientCoinvariantSimple H σ (compactInduced H σ g f) =
      (quotientCoinvariantSimple H σ f).comp (QuotientIntegration.rightTranslate H g)
        (hν g).measurable := by
    ext q
    exact quotientCoinvariantFunction_translate H σ g f q
  rw [compactCoinvariantIntegral_apply, he]
  exact AlgebraicIntegral.integral_comp_measurePreserving _ _ (hν g)

/-- The induced map on ambient coinvariants, with independent carrier universes. -/
def compactCoinvariantDesc :
    Representation.Coinvariants (compactInduced H σ) →ₗ[ℂ]
      Representation.Coinvariants σ :=
  Representation.Coinvariants.lift (compactInduced H σ) (compactCoinvariantIntegral H σ ν)
    (fun g => LinearMap.ext (compactCoinvariantIntegral_translate H σ ν hν g))

@[simp]
theorem compactCoinvariantDesc_mk (f : CompactFunctions H σ) :
    compactCoinvariantDesc H σ ν hν (Representation.Coinvariants.mk (compactInduced H σ) f) =
      compactCoinvariantIntegral H σ ν f := rfl

/-- The representative formula, expressed directly as quotient integration. -/
theorem compactCoinvariantDesc_mk_integral (f : CompactFunctions H σ) :
    compactCoinvariantDesc H σ ν hν (Representation.Coinvariants.mk (compactInduced H σ) f) =
      AlgebraicIntegral.integral ν (quotientCoinvariantSimple H σ f) := rfl

/-- Naturality on actual coinvariants, with `Coinvariants.map` on both sides. -/
theorem compactCoinvariantDesc_natural {τ : Representation ℂ H W}
    (T : σ.IntertwiningMap τ) :
    (compactCoinvariantDesc H τ ν hν).comp
        (Representation.Coinvariants.map (compactInduced H σ) (compactInduced H τ)
          (compactInducedMap H T)) =
      (Representation.Coinvariants.map σ τ T).comp (compactCoinvariantDesc H σ ν hν) := by
  apply Representation.Coinvariants.hom_ext
  ext f
  exact compactCoinvariantIntegral_natural H σ ν T f

/-- Pointwise form of naturality on the ambient coinvariant carrier. -/
theorem compactCoinvariantDesc_natural_apply {τ : Representation ℂ H W}
    (T : σ.IntertwiningMap τ) (z : Representation.Coinvariants (compactInduced H σ)) :
    compactCoinvariantDesc H τ ν hν
        (Representation.Coinvariants.map (compactInduced H σ) (compactInduced H τ)
          (compactInducedMap H T) z) =
      Representation.Coinvariants.map σ τ T (compactCoinvariantDesc H σ ν hν z) :=
  LinearMap.congr_fun (compactCoinvariantDesc_natural H σ ν hν T) z

end Langlands.Induction
