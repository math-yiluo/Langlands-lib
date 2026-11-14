# Chamber simple roots under root-datum isogenies

This derived support module compares bases adapted to a coweight and its actual
coweight pullback. The two lattices of each datum share a universe; the two
data and their index sets may use independent universes. It retains finite
reduced root data, injective transpose lattice maps and every positive
characteristic-power root factor from `RootDatumIsogeny`.

The proof uses an intrinsic reflection criterion for a simple root. In a base's
positive system, reflection in a simple root preserves all other positive roots,
by the published `RootPairing.Base.IsPos.reflectionPerm`. Conversely, a positive
root that is a sum of two positive roots cannot have this property: reflection
sends their sum to the negative of the original root, so a functional cannot be
positive on both reflected summands. The published positive-indecomposability
characterization of a base's support completes this criterion.

The transpose pairing and coroot equations show that the actual weight map
commutes with reflections in corresponding roots. The positive root factor of
each evaluated root then gives equivalence of signs, both before and after a
reflection. Applying the criterion on the two bases proves
`mem_support_iff_of_coweight_signs`. Its positivity hypotheses remain explicit;
this module does not prove the full arbitrary-base transport statement.

The content is an internal deduction from the imported root-datum and base
interfaces. It is designed for chambers of actual split maximal tori in the
general split-isogeny construction.
