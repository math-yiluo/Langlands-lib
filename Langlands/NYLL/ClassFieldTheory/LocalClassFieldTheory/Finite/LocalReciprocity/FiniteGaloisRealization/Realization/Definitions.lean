/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.SeparableClosure
import Langlands.NYLL.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding.U002.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions

/-!
# Finite Galois field ranges and fixing subgroups

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory
noncomputable section
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
/-- The embedded copy of `L` determined by an explicit embedding into the
fixed separable closure.  Keeping the embedding visible is what makes the
canonicity argument in the finite local reciprocity theorem meaningful. -/
def finiteGaloisFieldRangeOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    IntermediateField K (SeparableClosure K) :=
  AlgHom.fieldRange i

/-- An explicit embedding identifies `L` with its field range. -/
def finiteGaloisFieldRangeEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    L ≃ₐ[K] finiteGaloisFieldRangeOfEmbedding K L i :=
  AlgEquiv.ofInjectiveField i

/-- The image of an embedded finite Galois extension is again Galois over the base field. -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_isGalois
    (i : L →ₐ[K] SeparableClosure K) :
    IsGalois K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  IsGalois.of_algEquiv (finiteGaloisFieldRangeEquivOfEmbedding K L i)

/-- The image of an embedded finite extension is finite-dimensional over the base field. -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_finiteDimensional
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteDimensional K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  (finiteGaloisFieldRangeEquivOfEmbedding K L i).toLinearEquiv.finiteDimensional

/-- The closed fixing subgroup attached to an explicit realization of
`L/K` in the separable closure. -/
def finiteGaloisClosedFixingSubgroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ClosedSubgroup (Gal(SeparableClosure K / K)) :=
  closedFixingSubgroup K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)

/-- The embedded copy of `L` inside the fixed separable closure. -/
def finiteGaloisFieldRange : IntermediateField K (SeparableClosure K) :=
  finiteGaloisFieldRangeOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The canonical realization of a finite Galois extension is Galois over the base field. -/
instance finiteGaloisFieldRange_isGalois :
    IsGalois K (finiteGaloisFieldRange K L) :=
  finiteGaloisFieldRangeOfEmbedding_isGalois K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The canonical realization of a finite extension is finite-dimensional over the base field. -/
instance finiteGaloisFieldRange_finiteDimensional :
    FiniteDimensional K (finiteGaloisFieldRange K L) :=
  finiteGaloisFieldRangeOfEmbedding_finiteDimensional K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

/-- The concrete closed subgroup of the absolute separable Galois group
attached to `L/K`. -/
def finiteGaloisClosedFixingSubgroup :
    ClosedSubgroup (Gal(SeparableClosure K / K)) :=
  finiteGaloisClosedFixingSubgroupOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)
end
end Langlands.NYLL.LocalClassFieldTheory
