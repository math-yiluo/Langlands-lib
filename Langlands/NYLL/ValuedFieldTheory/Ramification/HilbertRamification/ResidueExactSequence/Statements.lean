/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 121, 2026-11-13: extract the types of the Prop-valued
instances M243.007 `decompositionFixedSubring.instIsLocalRing` (line 97),
M243.013 `decompositionFixedSubring.instSMulCommClass` (line 166), M243.014
`decompositionFixedSubring.instIsInvariant` (line 173), M243.016
`decompositionFixedMaximalIdeal.instIsMaximal` (line 203), M243.019
`selectedMaximalIdeal.instLiesOver` (line 229) and of the theorem M243.022
`decompositionGroup_maximalIdeal_stabilizer_eq_top` (line 253) of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace with Langlands.NYLL and package each complete elaborated source
telescope (the section variables the source declaration retains, then its
own binders) as a closed Prop-valued definition named with the suffix
`Statement`. The five instance targets are `abbrev`s, so that a proof can be
registered as an instance. Proofs, instance attributes, the private helpers
and all other declarations are omitted; the import is the published M243
data module.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.Definitions

/-!
# The residue-action exact sequence: statement targets on the fixed subring

Closed statement targets for NYLL M243.007, .013, .014, .016, .019 and .022:
the fixed subring `A^{G_w}` is local; the decomposition group action on `A`
commutes with multiplication by `A^{G_w}`; `A^{G_w}` is the invariant ring of
that action; for Galois `L / K` the contracted maximal ideal is maximal; the
maximal ideal of `A` lies over it; and every element of the decomposition
group stabilizes the maximal ideal of `A`.
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

open scoped Pointwise

/-- Statement target for the NYLL M243.007 instance
`decompositionFixedSubring.instIsLocalRing`: the fixed subring of the
decomposition group is a local ring. -/
abbrev decompositionFixedSubring.instIsLocalRingStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    IsLocalRing (decompositionFixedSubring K A)

/-- Statement target for the NYLL M243.013 instance
`decompositionFixedSubring.instSMulCommClass`: the action of the
decomposition group on `A` commutes with multiplication by the fixed
subring. -/
abbrev decompositionFixedSubring.instSMulCommClassStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A

/-- Statement target for the NYLL M243.014 instance
`decompositionFixedSubring.instIsInvariant`: every element of `A` fixed by
the decomposition group lies in the fixed subring. -/
abbrev decompositionFixedSubring.instIsInvariantStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A)

/-- Statement target for the NYLL M243.016 instance
`decompositionFixedMaximalIdeal.instIsMaximal`: for a Galois extension, the
contraction of the maximal ideal of `A` to the fixed subring is maximal. -/
abbrev decompositionFixedMaximalIdeal.instIsMaximalStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (A : _root_.ValuationSubring L),
    (decompositionFixedMaximalIdeal K A).IsMaximal

/-- Statement target for the NYLL M243.019 instance
`selectedMaximalIdeal.instLiesOver`: the maximal ideal of `A` lies over the
contracted ideal of the fixed subring. -/
abbrev selectedMaximalIdeal.instLiesOverStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    (IsLocalRing.maximalIdeal A).LiesOver
      (decompositionFixedMaximalIdeal K A)

/-- Statement target for NYLL M243.022
`decompositionGroup_maximalIdeal_stabilizer_eq_top`: every
decomposition-group automorphism stabilizes the maximal ideal of `A`. -/
def decompositionGroup_maximalIdeal_stabilizer_eq_topStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) = ⊤

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
