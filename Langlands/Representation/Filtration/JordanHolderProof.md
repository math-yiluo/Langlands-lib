# Actual Jordan–Hölder comparison, transport and transitivity

Assembly author: Worker 185. The imported comparison and transitivity proofs
are by Workers 185 and 242; the imported transport proof is by Worker 244.
The component implementations remain in their published modules.

`Langlands.jordanHolderSeries` proves exactly
`Langlands.JordanHolderSeriesStatement.{uK,uG,uA,uB,uC}` from
`Langlands.Representation.Filtration.JordanHolderStatement`. The proof is the
nested conjunction of the three published theorems
`jordanHolderSeriesComparison`, `jordanHolderSeriesTransport`, and
`haveSameJordanHolderFactors_trans`. Its explicit universe applications retain
independent universes for the field, monoid, and three representation carriers.
It adds no hypotheses and assumes no general existence of composition series.

The imported [comparison proof](JordanHolderComparisonProof.md) and
[transport proof](JordanHolderTransportProof.md) give the detailed constructions.
The following explains how those constructions establish the aggregate.

For comparison, the supplied filtrations give exactly their sequences of
invariant subspaces. `LengthCriterionProof.hasSimpleFactors_iff_covBy` converts
simple graded factors to covering relations between consecutive steps. These
sequences become Mathlib composition series in the modular lattice of invariant
subspaces. Their initial steps are bottom and their final steps are top.
`CompositionSeries.jordan_holder` therefore supplies a bijection
`Fin n ≃ Fin m` and matching lattice interval equivalences.

The comparison module interprets every such interval equivalence as an actual
`Representation.Equiv` of quotients. For invariant subspaces `S` and `T`,
`LengthCriterionProof.quotientRep S T` acts on
`T.toSubmodule ⧸ (S.toSubmodule.comap T.toSubmodule.subtype)`.
For consecutive filtration steps this is definitionally the graded action.
`JordanHolderProof.quotientSecondIso` realizes the generating interval relation
by the second isomorphism theorem from `y / (y ∩ x)` to `(y + x) / x`.
It sends a vector's quotient class to the class of the same vector in the sum.
Equivariance follows on representatives because both composites apply the
ambient action and then take the quotient class.
`JordanHolderProof.quotientEquiv_of_intervalIso` extends this interpretation
through reflexivity, symmetry, and transitivity using the corresponding
operations on representation equivalences. Applying it at every matched index
gives the required actual graded equivalences. The index bijection matches
individual occurrences, so repeated isomorphic factors retain their
multiplicities.

For transport along `φ : A.ρ.Equiv B.ρ`, the target filtration's steps are
the images of the supplied source steps. `JordanHolderTransportProof.subrepOrderIso`
shows that taking these images is an order isomorphism, preserving bottom, top,
monotonicity, and covering relations. Thus the image filtration has the same
length and simple factors. The helper `upperEquiv` restricts `φ` to an upper
step, and `map_lower` identifies the image of the pulled-back lower step.
`quotientEquiv` descends this restriction with `Submodule.Quotient.equiv`.
On representatives its equivariance is exactly
`φ (A.ρ g v) = B.ρ g (φ v)`. It matches the graded quotient at each source index
to the target quotient at that same index, across the independent carrier
universes.

For transitivity, the two hypotheses may supply different series of the middle
representation `B`, with lengths `n` and `m`. The imported transitivity theorem
instantiates the polymorphic comparison theorem at the middle universe `uB`,
giving a matching `g : Fin n ≃ Fin m`. Equality of finite cardinalities gives
`n = m`. After substituting it, the matching from `A` to `C` is
`e.trans (g.trans f)`, where `e` and `f` are the matchings supplied by the two
hypotheses. The three actual factor equivalences compose as
`(p.trans q).trans r`. The aggregate imports this independently proved
transitivity theorem; it does not attempt to specialize the first conjunct,
which concerns carriers at `uA`, to carriers at `uB`.

All three constructions include length zero: the endpoint conditions still
apply, and the factor conditions quantify over an empty index type. Zero
representations are allowed. No positivity, ambient nontriviality, or
finite-dimensionality hypothesis is introduced.

This aggregate is an internal deduction in general module theory for monoid
representations over a field. Its provenance is the two imported proof modules
and their unchanged published statement. The BZ77 motivation and original-source
locators are recorded in [the statement companion](JordanHolderStatement.md):
they concern Jordan–Hölder factors with multiplicities for smooth complex
representations. The broader field-and-monoid formulation is a derived
algebraic result. This aggregate establishes no p-adic induction, graded
refinement, or adjacent-block combinatorics.
