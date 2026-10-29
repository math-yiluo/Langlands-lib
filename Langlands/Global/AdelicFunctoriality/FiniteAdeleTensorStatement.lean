/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Matthew Jasper

Modified by Worker 300 (2026): restate, as a proposition definition, the conclusion of
`baseChange_bijective` in Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean:229-252, for number fields in
independent universes. It concerns the Library's canonical map `finiteAdeleTensorMap` in
the tensor order `A_K ⊗[K] L`, in place of Imperial's semialgebra base change in the order
`L ⊗[K] A_K`. No proof is ported. The upstream license is retained at
licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Global.AdelicFunctoriality.FiniteAdeleTensorMap

/-! # Bijectivity of the canonical map `A_K ⊗[K] L → A_L`: statement target -/

namespace Langlands.Global.AdelicFunctoriality

universe u v

/-- For all number fields `K` and `L` with `[Algebra K L]`, the canonical finite-adele map
`finiteAdeleTensorMap K L : A_K ⊗[K] L →ₐ[A_K] A_L`, which sends `x ⊗ l` to
`finiteAdeleInclusion x * algebraMap L A_L l`, is bijective. -/
def FiniteAdeleTensorMapBijective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L], Function.Bijective (finiteAdeleTensorMap K L)

end Langlands.Global.AdelicFunctoriality
