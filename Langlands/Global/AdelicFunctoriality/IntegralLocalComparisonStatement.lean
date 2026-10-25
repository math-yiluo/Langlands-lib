/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper

Modified by Worker 382 (2026): restate, as proposition definitions, the conclusions of
Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/Completion/BaseChange.lean:533-547, :810-821 and :854-870, and of
FLT/DedekindDomain/IntegralClosure.lean:256-297, for number fields in independent universes.
Use the Library's integralTensorInclusion, integralTensorComparison and
integralTensorTransport and its FinitePlacesAbove index in place of Imperial's equivalences
and Extension index. No proof is ported. The upstream license is retained at
licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Global.AdelicFunctoriality.IntegralTensorMaps

/-! # Integral local tensor comparison: statement targets -/

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct

universe u v

/-- At every finite place `p`, the canonical comparison
`T_p : 𝓞 L ⊗[𝓞 K] K_p → Π (q above p), L_q` is bijective, and it maps the image of the
canonical map `i_p : 𝓞 L ⊗[𝓞 K] O_p → 𝓞 L ⊗[𝓞 K] K_p` exactly onto `Π (q above p), O_q`. -/
def IntegralLocalTensorComparison : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)),
    Function.Bijective (integralTensorComparison L p) ∧
    Set.range (integralTensorComparison L p ∘ integralTensorInclusion L p) =
      Set.pi Set.univ (fun q : FinitePlacesAbove L p =>
        (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))) ∧
    Set.BijOn (integralTensorComparison L p) (Set.range (integralTensorInclusion L p))
      (Set.pi Set.univ (fun q : FinitePlacesAbove L p =>
        (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))))

/-- At every finite place `p`, the coefficient and tensor-order transport
`𝓞 L ⊗[𝓞 K] K_p → K_p ⊗[K] L`, `b ⊗ x ↦ x ⊗ b`, is bijective. -/
def IntegralTensorTransportBijective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)),
    Function.Bijective (integralTensorTransport L p)

end Langlands.Global.AdelicFunctoriality
