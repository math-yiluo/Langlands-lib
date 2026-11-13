# Proof of reduced-norm-one presentations of simply connected groups of inner type A

This module proves the published statement
`Langlands.GroupScheme.InnerTypeANormOneStatement` at every universe parameter `u`. The
theorem is `Langlands.GroupScheme.innerTypeANormOne`. Let `K` be an arbitrary field, of
any characteristic. Let `G` be a simply connected, absolutely almost simple group scheme
over `Spec K`, affine and locally of finite type. Suppose its Tits-index data has inner
type `A_n`: the Cartan pairings of its simple vertices are the type-`A_n` Cartan matrix,
and the full absolute Galois star action is trivial. Then there is a finite-dimensional
central simple `K`-algebra `A` of reduced degree `n + 1` with an isomorphism of group
schemes `G ≅ CentralSimpleUnits.normOne K A`. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The proof is one application of the helper theorem
`InnerTypeANormOneReduction.innerTypeANormOne_of_inputs`, in
`InnerTypeANormOneReduction.lean`. That theorem derives the target from four input
propositions. Each input is supplied by its published Library proof:

1. `specialLinearSimplyConnectedPinning`
   (`Langlands/GroupScheme/Reductive/SpecialLinearPinningProof.lean`) proves
   `SpecialLinearSimplyConnectedPinningStatement`: `SL_{n+1}` over any field has a split
   pinning with spanning coroots and type-`A_n` Cartan matrix.
2. `Langlands.LinearAlgebra.corootSpanCartanEquiv`
   (`Langlands/LinearAlgebra/CorootSpanCartanEquivProof.lean`) proves
   `CorootSpanCartanEquivStatement`: a pairing-preserving bijection of simple roots
   extends to an isomorphism of root data with spanning coroots.
3. `specialLinearInnerFormNormOne`
   (`Langlands/GroupScheme/SimplyConnected/SpecialLinearInnerFormNormOneProof.lean`)
   proves `SpecialLinearInnerFormNormOneStatement`: a quasi-split inner-form
   presentation with model `SL_{n+1}` comes from a central simple algebra of reduced
   degree `n + 1`, as its reduced-norm-one group.
4. `starActionFiniteStage`
   (`Langlands/GroupScheme/Reductive/StarActionFiniteStageProof.lean`) proves
   `StarActionFiniteStageStatement`: Galois pinning data over the separable closure is
   realized over a finite Galois extension, compatibly with root data, bases and star
   actions.

## Shape of the reduction

`InnerTypeANormOneReduction.md` explains the reduction in full. In outline: input 4 gives
Galois pinning data of `G` over a finite Galois `L/K` with trivial star action. Input 1
gives a pinning of `SL_{n+1}`, and input 2 gives a pinned isomorphism
`SL_{n+1,L} ≅ G_L`. `TrivialStarInnerTwist.hasInnerDiscrepancy` (in
`TrivialStarInnerTwist.lean`) shows that its Galois discrepancy is inner. That yields a
quasi-split inner-form presentation of `G` with model `SL_{n+1}`, and input 3 turns it
into the required central simple algebra.

## Literature

This is the classical identification of simply connected groups of inner type `A_n`
with the groups `SL_1(A)`. Tits 1966, §2.3 (printed p.39) gives the
inner-form classification. Milne 2017, §24.c (printed p.517) identifies the
split special-linear model; Corollary 23.53 (printed p.500) treats quasi-split
inner forms, and §24.f, Theorem 24.43 (printed p.524) gives the norm-one
classification.
Knus–Merkurjev–Rost–Tignol 1998, Theorem 26.9 (printed p.366) and Platonov–Rapinchuk
1994, Proposition 2.17 (printed p.87) identify the inner forms of `SL_{n+1}`. The Lean
proof follows this route through the four inputs listed above.
