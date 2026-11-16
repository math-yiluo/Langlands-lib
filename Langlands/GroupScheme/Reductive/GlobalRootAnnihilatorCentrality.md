# Full centrality from simple-root character equations over arbitrary bases

This internal consequence removes the local-base restriction from
`RelativeRootAnnihilatorCentrality`. It concerns a reductive group over any
commutative ring, with its supplied fibrewise maximal coordinate torus,
full coordinate root datum and base.

`SimpleRootCharactersOne` requires value one for the actual simple-root
characters on a relative torus point. Evaluation of exponent characters is
a homomorphism from the integer exponent lattice to units. Its additive
integer-linear kernel contains the simple roots, hence their integral span
and every root. This gives `RootCharactersOne`.

For a local coefficient test ring with separably closed residue field,
extend the original group, coordinate torus and root datum to that ring.
The actual point equivalences and canonical torus base-change isomorphism
preserve the character equations and torus inclusion. The local-base
commutation theorem therefore gives commutation on the original test.
Every morphism from the spectrum of a coefficient ring supplies its own
algebra structure, so this applies to all such tests.

Detection of morphism equality into an affine scheme by these local test
rings, after each relative refinement, then proves membership in the full
scheme-theoretic centre. It retains nilpotents and imposes no affineness,
connectedness or nonemptiness on the relative test scheme. Pinning has not
yet been used to establish the simple-root character equations, and this
module does not prove the pinned-comparison existence statement.
