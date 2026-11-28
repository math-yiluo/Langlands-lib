# The root datum of the trialitarian leaf centralizer

`d4LeafParabolicCoweights_coroot_eq_a2_of_zero` calculates the
coroots of `D₄` roots whose evaluation on the first difference of
the leaf triple is zero. In the coroot coordinates of a simply
connected datum, the difference leaves the subsystem on the
adjacent simple vertices `1` and `3`. The proof enumerates the signed
two-coordinate roots and uses injectivity of the coordinate map to
put each coroot on the six-element list spanned by those two
simple coroots.

`IsRootDatumOf.exists_a2_of_leafCentralizer` transfers this calculation
to an actual centralizer of the first difference over a field with
the split torus. The centralizer root embedding identifies its roots
with the ambient roots vanishing on that difference and preserves
coroots. The two simple roots in the list lift along the embedding.
The transported Cartan pairings are both `-1`, and every coroot of
the centralizer belongs to the resulting `A₂` list. This gives the
root datum input for a second descent inside the common Levi.
