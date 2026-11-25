# Parabolic Lie containment spreads to a Zariski neighbourhood

`relativeParabolicLieContainment` proves the unchanged Library proposition
`Langlands.GroupScheme.RelativeParabolicLieContainmentStatement` in every
universe. The base scheme is arbitrary, the ambient group is reductive, and
the two relative parabolics contain the supplied relative maximal torus.
There are no additional hypotheses.

The proof first pulls back the two global torus range inclusions to the
residue field of the distinguished point. Reductivity gives a connected
reductive group on that residue fibre. Relative parabolicity supplies the
two field parabolics, and fibrewise maximality supplies maximality of the
same torus on that fibre. The hypothesis is exactly containment of the
actual tangent submodules of their ranges.

`RelativeLevi.parabolic_range_le_of_lie_le` therefore gives containment of
the smaller residue-fibre range in the larger one. This field criterion
uses fixed-torus dynamic presentations and the published dynamic Lie
criterion; it permits a nonsplit torus over an arbitrary field.

`RelativeLevi.exists_open_range_le_of_torus_residueFiber` spreads that
range containment to an open containing the original point. Its
implementation splits the specified relative torus on an etale cover,
uses the split-torus neighbourhood construction, and descends containment
to the open image in the original base. The conclusion is containment of
the actual subgroup functors on every test scheme over that open.

The affine instances needed to form the tangent submodules are consequences
of reductivity and pullback. The target's global closedness hypothesis for
the torus is not needed by this proof: its fibrewise maximality and the
relative-torus splitting cover suffice for the two composed lemmas. The
target statement and its imported definitions are unchanged.
