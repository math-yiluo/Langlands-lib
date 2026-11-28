import Langlands.Representation.Archimedean.SmoothActionIrreducibility
import Langlands.Representation.Archimedean.SmoothProjectiveProduct

/-! # Density of pure smooth tensors in the genuine product topology -/

noncomputable section

open MeasureTheory Set UniformSpace Topology
open scoped ContDiff Manifold TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Archimedean.CompletedProjectiveRepresentation

open DerivativeSmoothVectors

universe uι uA uE

variable {ι : Type uι} [Fintype ι]
  (A : ι → Type uA) [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra ℝ (A i)]
  [∀ i, CompleteSpace (A i)]
  {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, (A i)ˣ →* (E i →L[ℂ] E i))

local notation "U" => (∀ i, A i)ˣ
local notation "I" => 𝓘(ℝ, (∀ i, A i))
local notation "D" => DerivativeSmoothVectors I (productAction A R)

/-- The actual product-group action on pure smooth tensors. -/
theorem representation_pureSmooth (g : U) (v : ∀ i, DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)) :
    representation I (productAction A R) g (pureSmooth A R v) =
      pureSmooth A R (fun i => representation 𝓘(ℝ, A i) (R i) (unitProjection A i g) (v i)) := by
  apply (toSmooth I (productAction A R)).injective
  apply Subtype.ext
  simp only [toSmooth_representation, smoothRepresentation_apply, toSmooth_pureSmooth,
    productAction_pure]

/-- The complex span of pure smooth tensors in the genuine product smooth carrier. -/
def pureSmoothSpan : Submodule ℂ D := Submodule.span ℂ (range (pureSmooth A R))

private theorem mapsTo_pureSmoothSpan (g : U) :
    MapsTo (representation I (productAction A R) g) (pureSmoothSpan A R) (pureSmoothSpan A R) := by
  intro v hv
  let T := representation I (productAction A R) g
  change T v ∈ pureSmoothSpan A R
  apply (LinearMap.map_span_le T _ _).mpr ?_ (Submodule.mem_map_of_mem hv)
  rintro _ ⟨w, rfl⟩
  exact Submodule.subset_span ⟨_, (representation_pureSmooth A R g w).symm⟩

variable [∀ i, FiniteDimensional ℝ (A i)] [∀ i, CompleteSpace (E i)]

private theorem dense_normImage_pureSmoothSpan (hR : ∀ i, IsContinuousRepresentation (R i)) :
    Dense ((pureSmoothSpan A R).map (derivativeCLM I (productAction A R) []).toLinearMap :
      Set (Carrier E)) := by
  let P := derivativeCLM I (productAction A R) []
  let W := (pureSmoothSpan A R).map P.toLinearMap
  let M := W.topologicalClosure
  let j (i : ι) (v : DerivativeSmoothVectors 𝓘(ℝ, A i) (R i)) := (toSmooth 𝓘(ℝ, A i) (R i) v).val
  have hj (i : ι) : DenseRange (j i) := by
    let : MeasurableSpace (A i)ˣ := borel _
    let : BorelSpace (A i)ˣ := ⟨rfl⟩
    let : LocallyCompactSpace (A i)ˣ := Units.isOpenEmbedding_val.locallyCompactSpace
    have he : range (j i) = (smoothVectors 𝓘(ℝ, A i) (R i) : Set (E i)) := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        exact (toSmooth 𝓘(ℝ, A i) (R i) v).property
      · intro hx
        exact ⟨(toSmooth 𝓘(ℝ, A i) (R i)).symm ⟨x, hx⟩, by simp [j]⟩
    rw [DenseRange, he]
    exact dense_smoothVectors_units (R i) (Measure.haar : Measure (A i)ˣ) (hR i)
  have hPi : DenseRange (Pi.map j) := DenseRange.piMap hj
  have hMap : MapsTo (pure E) (range (Pi.map j)) M := by
    rintro _ ⟨v, rfl⟩
    apply W.le_topologicalClosure
    exact ⟨pureSmooth A R v, Submodule.subset_span (mem_range_self v), rfl⟩
  have hPure (v : ∀ i, E i) : pure E v ∈ M :=
    hMap.closure_left (pure E).cont W.isClosed_topologicalClosure (hPi v)
  have hAlg (x : ⨂[ℂ] i, E i) : (x : Carrier E) ∈ M := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      rw [Completion.coe_smul, ← pure_apply]
      exact M.smul_mem c (hPure v)
    | add v w hv hw =>
      rw [Completion.coe_add]
      exact M.add_mem hv hw
  intro x
  exact closure_minimal (range_subset_iff.mpr hAlg) W.isClosed_topologicalClosure
    (Completion.denseRange_coe x)

/-- Smooth pure tensors span densely for the genuine product word-derivative topology. -/
def SmoothProjectiveProductDensityStatement : Prop :=
  ∀ {ι : Type uι} [Fintype ι] (A : ι → Type uA) [∀ i, NormedRing (A i)]
    [∀ i, NormedAlgebra ℝ (A i)] [∀ i, CompleteSpace (A i)] [∀ i, FiniteDimensional ℝ (A i)]
    (E : ι → Type uE) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] (R : ∀ i, (A i)ˣ →* (E i →L[ℂ] E i)),
    (∀ i, IsContinuousRepresentation (R i)) → Dense (pureSmoothSpan A R : Set
      (DerivativeSmoothVectors 𝓘(ℝ, (∀ i, A i)) (productAction A R)))

set_option maxHeartbeats 450000 in
theorem smoothProjectiveProductDensity : SmoothProjectiveProductDensityStatement := by
  intro ι _ A _ _ _ _ E _ _ _ R hR
  let : MeasurableSpace (∀ i, A i)ˣ := borel _
  let : BorelSpace (∀ i, A i)ˣ := ⟨rfl⟩
  let : LocallyCompactSpace (∀ i, A i)ˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  exact dense_of_invariant_of_normDense (productAction A R) (Measure.haar : Measure (∀ i, A i)ˣ)
    (isContinuous_productAction A R hR) (pureSmoothSpan A R) (mapsTo_pureSmoothSpan A R)
    (dense_normImage_pureSmoothSpan A R hR)

end Langlands.Archimedean.CompletedProjectiveRepresentation
