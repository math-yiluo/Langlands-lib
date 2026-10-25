import Langlands.Global.AdelicFunctoriality.Norm

/-! # Neighborhoods of one in actual local norm images -/

namespace Langlands.Global.AdelicFunctoriality

open Filter Topology NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField NumberField.LiesOver FiniteExtension InfiniteExtension

universe u v

/-- For an arbitrary extension of number fields, the images of the actual local norms
on multiplicative units contain neighborhoods of one at all finite and infinite places.
This defines the proposition, with independent field universes. -/
def LocalNormNeighborhoodStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L],
    (∀ (p : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
      (h : q.asIdeal.LiesOver p.asIdeal),
      letI := h
      Set.range (Units.map (FiniteExtension.localNorm p q)) ∈
        𝓝 (1 : (p.adicCompletion K)ˣ)) ∧
    (∀ (p : InfinitePlace K) (q : InfinitePlace L) (h : q.LiesOver p),
      letI := h
      Set.range (Units.map (InfiniteExtension.localNorm p q)) ∈
        𝓝 (1 : p.Completionˣ))

end Langlands.Global.AdelicFunctoriality
