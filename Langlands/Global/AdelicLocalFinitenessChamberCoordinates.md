# Minimal-parabolic coordinates for local finiteness

`exists_siegelAlgebraicSetup_of_generic` constructs a Siegel setup using the
maximal split torus and generic cocharacter of the given local-finiteness
system. It chooses the derived split factor inside that torus, obtains the
split central factor and uses their product isogeny. The standard minimal
parabolic and Levi come from the prescribed cocharacter.

`exists_minimalParabolicTorusDualEquiv` identifies the real character dual of
that minimal parabolic with the dual of the maximal split torus. Levi
restriction is bijective on characters. In the minimal Levi the torus is
central and maximal split, so restriction from the Levi is injective with
finite index. The resulting map of real duals is the actual map induced by
the torus inclusion.

`AdelicLocalFinitenessChamberCoordinatesStatement` supplies a continuous
linear equivalence from the real parabolic dual to the product of the
simple-root and central coordinate spaces. Its proof transports
`localFinitenessTorusCoordinates` along the dual equivalence. Each root
coordinate is the corresponding torus character logarithm divided by its
positive translation step. The simultaneous vanishing of the central
coordinates is equivalent to vanishing of the ambient logarithmic
functional. Evaluating the actual parabolic logarithms of the specified
positive translations gives one unit coordinate in each case.

The construction implements the height coordinates used in Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series*, §§7.1–7.2 and §7.7.
It uses the positive split points and all the group data of the published
number-field local-finiteness system.
