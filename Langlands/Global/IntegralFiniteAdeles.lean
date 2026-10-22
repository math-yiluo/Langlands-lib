import Langlands.Global.Adelic
import Langlands.Global.CompletionPadic

noncomputable section

universe u

namespace Langlands.Global

namespace FiniteAdelicGL

open NumberField IsDedekindDomain

variable (K : Type u) [Field K] [NumberField K]

/-- Finite adeles integral at every finite place. -/
def integralAdeles : Subring (FiniteAdeleRing (𝓞 K) K) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 K), a v ∈ v.adicCompletionIntegers K}
  zero_mem' v := (v.adicCompletionIntegers K).zero_mem
  one_mem' v := (v.adicCompletionIntegers K).one_mem
  add_mem' ha hb v := (v.adicCompletionIntegers K).toSubring.add_mem (ha v) (hb v)
  mul_mem' ha hb v := (v.adicCompletionIntegers K).toSubring.mul_mem (ha v) (hb v)
  neg_mem' ha v := (v.adicCompletionIntegers K).toSubring.neg_mem (ha v)

@[simp]
theorem mem_integralAdeles (a : FiniteAdeleRing (𝓞 K) K) :
    a ∈ integralAdeles K ↔
      ∀ v : HeightOneSpectrum (𝓞 K), a v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

/-- Openness is in the actual restricted-product topology. -/
theorem isOpen_integralAdeles :
    IsOpen (integralAdeles K : Set (FiniteAdeleRing (𝓞 K) K)) :=
  RestrictedProduct.isOpen_forall_mem
    (fun v : HeightOneSpectrum (𝓞 K) => Valued.isOpen_valuationSubring (v.adicCompletion K))

end FiniteAdelicGL

variable (K : Type u) [Field K] [NumberField K]

/-- Finite adeles integral at every finite place, using the shared subring. -/
def integralFiniteAdeles : Subring (FiniteAdeles K) :=
  FiniteAdelicGL.integralAdeles K

@[simp]
theorem mem_integralFiniteAdeles (a : FiniteAdeles K) :
    a ∈ integralFiniteAdeles K ↔ ∀ v, a v ∈ v.adicCompletionIntegers K :=
  FiniteAdelicGL.mem_integralAdeles K a

/-- The actual completed integer ring is compact in the completion topology. -/
theorem isCompact_adicCompletionIntegers (v : FinitePlace K) :
    IsCompact (v.adicCompletionIntegers K : Set (FiniteCompletion K v)) := by
  let : ValuativeRel (FiniteCompletion K v) :=
    (CompletionPadic.topologicalData v).valuativeRel
  let : IsNonarchimedeanLocalField (FiniteCompletion K v) :=
    (CompletionPadic.topologicalData v).localField
  have hc := IsNonarchimedeanLocalField.isCompact_closedBall (FiniteCompletion K v) 1
  convert hc using 1
  ext x
  change Valued.v x ≤ 1 ↔ ValuativeRel.valuation (FiniteCompletion K v) x ≤ 1
  rw [← (ValuativeRel.valuation _).vle_one_iff]
  rw [CompletionPadic.topologicalData_vle]
  simp

theorem isOpen_integralFiniteAdeles :
    IsOpen (integralFiniteAdeles K : Set (FiniteAdeles K)) :=
  FiniteAdelicGL.isOpen_integralAdeles K

theorem isCompact_integralFiniteAdeles :
    IsCompact (integralFiniteAdeles K : Set (FiniteAdeles K)) := by
  have : ∀ v : FinitePlace K, CompactSpace (v.adicCompletionIntegers K) :=
    fun v => isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers K v)
  have h := isCompact_range
    (RestrictedProduct.isEmbedding_structureMap (R := FiniteCompletion K)
      (A := fun v : FinitePlace K => (v.adicCompletionIntegers K : Set (FiniteCompletion K v)))
      (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end Langlands.Global
