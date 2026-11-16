# The unlinked induction-character swap

`realInducedCharacterSwap` has exactly the Library proposition
`Langlands.Archimedean.RealInducedCharacterSwapStatement` as its type. It retains
every original quantifier and hypothesis, including arbitrary ambient rank and
surrounding block lists.

The rank-three input is
`RealMixedSwapTwist.inducedCharacterSwap_unlinked`. For a complex character datum
`d` and real character datum `b`, write `q = |d.weight| + 1`. Signed reversal of
functions, `f(g) ↦ sgn(det g)^q f(w(gᵀ)⁻¹)` with
`w = [[0,0,1],[0,-1,0],[1,0,0]]`, identifies the standard module of
`[induced d, character b]` with that of
`[character (reverseCharacter d b), induced (reverseInduced d)]`. The output
standard module of `[character b, induced d]` has the corresponding reversed
identification with
`[induced (reverseInduced d), character (reverseCharacter d b)]`.

The reversed induction datum keeps its nonzero weight and negates its exponent.
The reversed real character negates its exponent and adds `q` to its sign parity
modulo two. Thus the original exponent order and mixed unlinkedness imply exactly
the hypotheses of `RealCharacterInducedUnlinked.injective_unlinked` for these
reversed parameters. That theorem provides an unconditional injective
character-induction intertwiner, using its proved generic, interlaced, and
endpoint constructions.

Conjugating that map by the two signed-reversal equivalences gives the required
rank-three map in the original direction. The common determinant-sign scalar
under compact translation cancels across the complex-linear middle map. For the
Lie action, both equivalences carry the direction `X` to `-Xᵀ`, so exact
equivariance of the middle map proves exact equivariance of the conjugate.
The two equivalences and injectivity of the middle map prove injectivity.

The implemented proof then applies
`RealInjectiveIntertwinerExists.in_stages` to this rank-three map. Both exchanged
middle lists have rank three. The original ambient rank equation supplies the
rank equation after adjoining `pre` and `post`, and simplification identifies
the concatenated lists with the lists in the target proposition. Induction in
stages preserves complex linearity, injectivity, and the original compact and
Lie intertwining predicate.

This is internal derived content built from the proved signed-reversal,
character-induction, and induction-in-stages results. It retains no
irreducibility, landing, classification, or intertwining-existence premise.
