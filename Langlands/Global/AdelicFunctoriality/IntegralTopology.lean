import Langlands.Global.AdelicFunctoriality.IntegralTensorEquiv
import Langlands.Global.CurvePlaceIntegralTopology
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Original module topology of number-field completed integers -/

noncomputable section

universe u v

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
  Langlands.Global.AdelicFunctoriality.IntegralTensor

namespace Langlands.Global.AdelicFunctoriality.IntegralTopology

/-- The actual completed integer ring retains its inherited topological ring structure. -/
scoped instance completedIntegerTopologicalRing {F : Type u} [Field F]
    [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IsTopologicalRing (v.adicCompletionIntegers F) :=
  inferInstanceAs (IsTopologicalRing (v.adicCompletionIntegers F).toSubring)

/-- Units in the actual completed integer ring are open. -/
scoped instance completedIntegerOpenUnits {F : Type u} [Field F]
    [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IsOpenUnits (v.adicCompletionIntegers F) :=
  isOpenUnits_openSubring (v.adicCompletionIntegers F).toSubring
    (Valued.isOpen_valuationSubring (v.adicCompletion F))

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p)

/-- The original upper ring of integers is projective over the lower one. -/
scoped instance integersProjective : Module.Projective (𝓞 K) (𝓞 L) := by
  let : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite (𝓞 K) (𝓞 L)
  exact Module.Flat.projective_of_finitePresentation

/-- Every original upper completed integer ring is finite over the lower one. -/
scoped instance localFinite :
    Module.Finite (p.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) := by
  let : Module.Finite (p.adicCompletionIntegers K)
      (∀ q : FinitePlacesAbove L p, q.1.adicCompletionIntegers L) :=
    Module.Finite.equiv (IntegralTensor.tensorEquiv p).toLinearEquiv
  let f : (∀ q : FinitePlacesAbove L p, q.1.adicCompletionIntegers L) →ₗ[
      p.adicCompletionIntegers K] q.1.adicCompletionIntegers L := LinearMap.proj q
  exact Module.Finite.of_surjective f (Function.surjective_eval q)

/-- The canonical completion embedding restricted to the original integer rings is continuous. -/
theorem continuous_completionIntegersMap :
    Continuous (FiniteExtension.completionIntegersMap p q.1) := by
  apply continuous_induced_rng.mpr
  exact (FiniteExtension.continuous_completionMap p q.1).comp continuous_subtype_val

/-- The actual upper completed integer ring has continuous lower scalar multiplication. -/
scoped instance continuousSMul :
    ContinuousSMul (p.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) where
  continuous_smul :=
    ((continuous_completionIntegersMap p q).comp continuous_fst).mul continuous_snd

/-- The original upper completed-integer topology is the canonical finite-module topology. -/
scoped instance moduleTopology :
    IsModuleTopology (p.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) := by
  let : CompactSpace (p.adicCompletionIntegers K) :=
    isCompact_iff_compactSpace.mp (Langlands.Global.isCompact_adicCompletionIntegers K p)
  exact compactFiniteModuleIsModuleTopology (p.adicCompletionIntegers K)
    (q.1.adicCompletionIntegers L)

/-- The finite original extension of completed integer rings is projective. -/
scoped instance localProjective :
    Module.Projective (p.adicCompletionIntegers K) (q.1.adicCompletionIntegers L) := by
  infer_instance

end Langlands.Global.AdelicFunctoriality.IntegralTopology
