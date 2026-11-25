# The exact marking of every local rank-one D4 index

This internal derived module proves `localRankOneD4_central_marking`.
For any nonarchimedean local field `K : Type u`, it assumes an affine
locally finite type group scheme, actual `TitsIndexData G`, simple
connectedness, absolute almost simplicity, split rank one, and an
equivalence `e` identifying the actual Cartan matrix with
`CartanMatrix.D 4`. Its conclusion is the exact
`IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) e` predicate.
Thus precisely the central vertex is distinguished, in the originally
supplied numbering. All field and residue characteristics, including
characteristic two, are retained.

The proof splits on existence of a leaf fixed by the full absolute Galois
star action. When such a leaf exists,
`localRankOneD4_presentation_and_marking_of_fixed_leaf` gives the central
marking in the numbering that swaps that leaf with vertex `0`.
This transposition fixes the center, so injectivity of the transposition
transports the marking back to `e`. When there is no globally fixed leaf,
`D4_central_marking_of_no_fixed_leaf` supplies the same conclusion over
an arbitrary field.

The theorem places no additional restriction on the full star image.
It does not prove that the action is nontrivial or has a globally fixed
leaf. In particular, it does not exclude inner D4 or trialitarian local
indices, and does not itself prove `HasRankOneOuterD4Index` or the full
`LocalRankOneTitsIndexStatement`. Those arithmetic and full-image
steps are not taken here; `localRankOneTitsIndex` in
`LocalRankOneTitsIndexProof` proves the full statement.
