# Rank-one root reducedness descends from an algebraic closure

Worker 847.

This is an internal field-descent interface and conditional reduction for the
published `RankOneRootReducednessStatement`. Its provenance is the existing
actual-root and lattice base-change results in `RootSupportBaseChange`,
`RankOnePositiveRootBaseChange`, `SplitLatticeBaseChange` and
`MaximalBaseChangeProof`. It adds no classification result or unconditional
reducedness proof.

## Statement and scope

`Langlands.GroupScheme.RankOneAlgClosedRootReducednessStatement.{u}` is the
published rank-one reducedness proposition restricted to algebraically closed
fields. For every field `k : Type u` with `IsAlgClosed k`, connected reductive
group `G`, split commutative torus `T` and prescribed maximal-torus map
`i : T.toGrp ⟶ G`, suppose all pairs of actual roots are linearly dependent
over the integers. Then any two actual roots `α`, `β` satisfy `α = β` or
`α = -β`.

The roots are the nonzero characters with nonzero weight spaces in the actual
adjoint Lie representation. Affineness in that definition comes from `hG`.
The statement allows the root set to be empty. There is no assertion of root
existence, root-space dimension, an `SL₂` cover, a Borel model or a root datum.
The universe and characteristic are unrestricted. This module does not prove
the newly stated algebraically closed proposition.

## Implemented reduction

`rankOneAlgClosedRootReducedness_of_statement` restricts the all-field
proposition to algebraically closed fields.

`rankOneRootReducedness_of_algClosed` proves the converse implication.
Given an arbitrary field and two roots `α`, `β`, it passes to
`AlgebraicClosure k` with its canonical field algebra. The existing reductive
base-change result makes the changed group connected reductive. The existing
maximal-torus base-change theorem makes the changed torus maximal, and the
torus remains split. The pure lattice result
`roots_pairwise_dependent_baseChange_iff` transports the pairwise dependence
hypothesis. The actual-root comparison `mem_roots_baseChange_iff` transports
both roots.

The algebraically closed hypothesis then equates their pullback characters
up to sign. Character pullback for a split torus is bijective, and in
particular injective. Injectivity reflects equality back to the original
character lattice. In the negative case, additivity of pullback identifies
the negative of the changed character with the change of the original
negative character. This proves the required equality up to sign over the
original field.

`rankOneRootReducedness_iff_algClosed` combines these two implications into
a logical equivalence. This equivalence concerns the two universal
propositions; it is not an unconditional proof of either one.

## Dependency boundary

The reduction uses pure root support, character lattices and maximal-torus
base change. In particular, the positive-root uniqueness theorem and its
geometric proof are not inputs. The module containing the pure pairwise
dependence transport lemma also states a positive-root proposition; importing
that module does not apply the proposition or its proof. Independent review
must check the new declaration dependencies as well as these semantics.
