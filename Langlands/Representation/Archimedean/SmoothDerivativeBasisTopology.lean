import Langlands.Representation.Archimedean.SmoothDerivativeTopology
import Mathlib.Topology.MetricSpace.PiNat

/-! # Basis words generate the genuine smooth-vector topology -/

noncomputable section

open scoped Manifold ContDiff Topology
open TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

universe u𝔤 uM uG uE uι uX

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {M : Type uM} [TopologicalSpace M] (I : ModelWithCorners ℝ 𝔤 M)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace M G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →* (E →L[ℂ] E)) [LieGroup I ∞ G]

/-- Genuine differentiation on smooth vectors, real linear in the Lie direction. -/
def smoothLieDerivativeDirection : 𝔤 →ₗ[ℝ] Module.End ℂ (smoothVectors I π) where
  toFun X := smoothLieDerivative I π X
  map_add' X Y := by
    ext v
    change lieDerivative I π (X + Y) v = lieDerivative I π X v + lieDerivative I π Y v
    exact map_add (mfderiv I 𝓘(ℝ, E) (orbitMap π v) 1) X Y
  map_smul' c X := by
    ext v
    change lieDerivative I π (c • X) v = c • lieDerivative I π X v
    exact map_smul (mfderiv I 𝓘(ℝ, E) (orbitMap π v) 1) c X

/-- The derivative of a word with one variable direction, real linear in that slot. -/
def wordDirectionLinear (pre post : List 𝔤) (v : smoothVectors I π) : 𝔤 →ₗ[ℝ] E :=
  (((smoothVectors I π).subtype.comp
      (smoothIteratedLieDerivative I π pre)).restrictScalars ℝ).comp
    (((LinearMap.applyₗ (smoothIteratedLieDerivative I π post v)).restrictScalars ℝ).comp
      (smoothLieDerivativeDirection I π))

lemma wordDirectionLinear_apply (pre post : List 𝔤) (v : smoothVectors I π) (X : 𝔤) :
    wordDirectionLinear I π pre post v X =
      iteratedLieDerivative I π (pre ++ X :: post) v := by
  change ((smoothIteratedLieDerivative I π pre)
      (smoothLieDerivative I π X (smoothIteratedLieDerivative I π post v)) : E) = _
  rw [← smoothIteratedLieDerivative_apply, smoothIteratedLieDerivative_append]
  rfl

variable {ι : Type uι} (b : Module.Basis ι ℝ 𝔤)

/-- Expanding one real direction in a basis expands that word slot by a finite sum. -/
lemma iteratedLieDerivative_basis_expansion (pre post : List 𝔤)
    (v : smoothVectors I π) (X : 𝔤) :
    iteratedLieDerivative I π (pre ++ X :: post) v =
      ∑ i ∈ (b.repr X).support, (b.repr X i) •
        iteratedLieDerivative I π (pre ++ b i :: post) v := by
  have h := congrArg (wordDirectionLinear I π pre post v) (b.linearCombination_repr X)
  simp only [Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, wordDirectionLinear_apply] at h
  exact h.symm

/-- Continuity of basis-word derivatives implies continuity for all genuine words.
The source can carry any topology. -/
theorem continuous_iteratedLieDerivative_of_basis {X : Type uX} [TopologicalSpace X]
    (f : X → smoothVectors I π)
    (hf : ∀ W : List ι, Continuous fun x => iteratedLieDerivative I π (W.map b) (f x))
    (W : List 𝔤) : Continuous fun x => iteratedLieDerivative I π W (f x) := by
  classical
  suffices h : ∀ post : List 𝔤, ∀ pre : List ι,
      Continuous fun x => iteratedLieDerivative I π (pre.map b ++ post) (f x) by
    simpa using h W []
  intro post
  induction post with
  | nil =>
    intro pre
    simpa using hf pre
  | cons Y post ih =>
    intro pre
    have he : (fun x => iteratedLieDerivative I π (pre.map b ++ Y :: post) (f x)) =
        fun x => ∑ i ∈ (b.repr Y).support, (b.repr Y i) •
          iteratedLieDerivative I π (pre.map b ++ b i :: post) (f x) := by
      funext x
      exact iteratedLieDerivative_basis_expansion I π b (pre.map b) post (f x) Y
    rw [he]
    apply continuous_finsetSum
    intro i _
    apply Continuous.const_smul
    simpa [List.map_append, List.append_assoc] using ih (pre ++ [i])

namespace DerivativeSmoothVectors

/-- The genuine word coordinates using only words in a chosen real basis. -/
def basisDerivativeCoordinates : DerivativeSmoothVectors I π →ₗ[ℂ] (List ι → E) :=
  LinearMap.pi fun W => (LinearMap.proj (W.map b)).comp (derivativeCoordinates I π)

@[simp]
lemma basisDerivativeCoordinates_apply (v : DerivativeSmoothVectors I π) (W : List ι) :
    basisDerivativeCoordinates I π b v W = iteratedLieDerivative I π (W.map b) (toSmooth I π v) :=
  derivativeCoordinates_apply I π v (W.map b)

lemma basisDerivativeCoordinates_injective :
    Function.Injective (basisDerivativeCoordinates I π b) := by
  intro v w h
  apply (toSmooth I π).injective
  apply Subtype.ext
  simpa only [basisDerivativeCoordinates_apply, List.map_nil,
    iteratedLieDerivative_nil] using congrFun h []

lemma continuous_basisDerivativeCoordinates : Continuous (basisDerivativeCoordinates I π b) := by
  apply continuous_pi
  intro W
  exact (derivativeCLM I π (W.map b)).continuous

/-- Restricting from all real-direction words to basis words leaves the topology unchanged. -/
theorem topology_eq_induced_basisDerivativeCoordinates :
    (inferInstance : TopologicalSpace (DerivativeSmoothVectors I π)) =
      TopologicalSpace.induced (basisDerivativeCoordinates I π b) inferInstance := by
  apply le_antisymm
  · exact continuous_iff_le_induced.mp (continuous_basisDerivativeCoordinates I π b)
  · let t := TopologicalSpace.induced (basisDerivativeCoordinates I π b) inferInstance
    have h : @Continuous (DerivativeSmoothVectors I π) (List 𝔤 → E) t inferInstance
        (derivativeCoordinates I π) := by
      let _ : TopologicalSpace (DerivativeSmoothVectors I π) := t
      have hbas : ∀ B : List ι, Continuous fun v : DerivativeSmoothVectors I π =>
          iteratedLieDerivative I π (B.map b) (toSmooth I π v) := by
        intro B
        have hc : @Continuous (DerivativeSmoothVectors I π) (List ι → E) t inferInstance
            (basisDerivativeCoordinates I π b) := continuous_induced_dom
        have hcB := (continuous_apply B).comp hc
        change @Continuous (DerivativeSmoothVectors I π) E t inferInstance
          (fun v => basisDerivativeCoordinates I π b v B) at hcB
        simp only [basisDerivativeCoordinates_apply] at hcB
        exact hcB
      apply continuous_pi
      intro W
      simp only [derivativeCoordinates_apply]
      exact continuous_iteratedLieDerivative_of_basis I π b (toSmooth I π) hbas W
    exact continuous_iff_le_induced.mp h

/-- The smooth carrier embeds into the product of the basis-word coordinates. -/
theorem isEmbedding_basisDerivativeCoordinates :
    Topology.IsEmbedding (basisDerivativeCoordinates I π b) :=
  ⟨⟨topology_eq_induced_basisDerivativeCoordinates I π b⟩,
    basisDerivativeCoordinates_injective I π b⟩

include b in
/-- A countable real basis makes the genuine smooth-vector topology metrizable. -/
theorem metrizableSpace_of_countable_basis [Countable ι] :
    MetrizableSpace (DerivativeSmoothVectors I π) := by
  let _ : Encodable (List ι) := Encodable.ofCountable _
  let _ : MetricSpace (List ι → E) := PiCountable.metricSpace
  exact (isEmbedding_basisDerivativeCoordinates I π b).metrizableSpace

/-- In particular, a finite-dimensional real Lie algebra gives a metrizable
word-derivative topology. Completeness is a separate assertion. -/
theorem metrizableSpace_of_finiteDimensional [FiniteDimensional ℝ 𝔤] :
    MetrizableSpace (DerivativeSmoothVectors I π) :=
  metrizableSpace_of_countable_basis I π (Module.finBasis ℝ 𝔤)

end DerivativeSmoothVectors

end Langlands.Archimedean
