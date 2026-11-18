# The local geometric Artinian exhaustion theorem

Worker 801 proves `LocalArtinianExhaustion.Statement` in every scheme and index
universe. The internal `affineSeparationIndex` chooses a positive separating
power on each affine open for a morphism already full on the punctured base.

The proof first takes a common stage full both over the punctured base and on
the residue fibre; it is a surjective closed immersion. Its affine defining
ideals have support over the closed point, and support/Artin–Rees gives a
separating power on each affine open. A finite affine cover permits one common
power. A later stage, dominating the earlier stage and a stage full on that
thickening, is also a surjective closed immersion.

The canonical thickening's projection factors through that later stage.
Consequently the later defining ideal is contained in the extended
maximal-ideal power, by the actual affine base-change kernel calculation. It is
also contained in the earlier ideal. Their separating intersection is zero, so
all its affine ideals vanish. The ideal-sheaf affine-cover criterion makes the
whole defining ideal zero, and the closed immersion is an isomorphism.

This implements the local argument of SGA 3, Exposé IX, Lemma 6.2 (registered
source `sga3-expose-ix-gille-polo-2009`, printed pp.53–54), replacing the source's
finite-length separation appeal with Artin–Rees. The outer induction and
localization-to-open spreading remain separate parts of the global exhaustion
proof.
