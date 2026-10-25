import Langlands.ClassField.Global.IdeleArchimedean

/-! # Mixed weak approximation by principal ideles -/

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open Langlands.ClassField.Global
open scoped NumberField

universe u

/-- Multiplicative weak approximation at any finite set of finite places and at
every infinite place, using a single nonzero principal multiplier. -/
def MixedPrincipalIdeleApproximation : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : IdeleGroup (𝓞 K) K)
    (U : ∀ p : HeightOneSpectrum (𝓞 K), Set (p.adicCompletion K)ˣ),
    (∀ p ∈ S, U p ∈ 𝓝 1) →
    ∀ (V : ∀ w : InfinitePlace K, Set w.Completionˣ),
    (∀ w, V w ∈ 𝓝 1) →
    ∃ α : Kˣ,
      (∀ p ∈ S,
        ideleCoordinate p ((IdeleGroup.unitEmbedding (𝓞 K) K α)⁻¹ * a) ∈ U p) ∧
      ∀ w,
        ideleInfiniteCoordinate w ((IdeleGroup.unitEmbedding (𝓞 K) K α)⁻¹ * a) ∈ V w

end Langlands.Global.AdelicFunctoriality
