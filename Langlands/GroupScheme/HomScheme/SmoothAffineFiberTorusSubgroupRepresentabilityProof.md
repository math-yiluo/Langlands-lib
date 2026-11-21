# Smooth torus-subgroup representability with affine residue fibres

`smoothAffineFiberTorusSubgroupRepresentability` proves
`SmoothAffineFiberTorusSubgroupRepresentabilityStatement.{u}`. For a smooth,
separated, quasi-compact group scheme with affine actual residue fibres over any
`S : Scheme.{u}`, it gives a smooth parameter over `S` with a universal family
of closed relative tori. On every test, the classifying map is unique and the
evaluation of the family equals the test subgroup functor.

The proof supplies the three inputs to
`smoothAffineFiberTorusSubgroupRepresentability_of_moduliInputs` over a
Noetherian affine base with geometrically connected ambient fibres. Affineness
of the closed fibre extends to each local Artinian pullback because the maximal
ideal is nilpotent. The adic limit theorem algebraizes compatible actual closed
tori over the maximal-ideal thickenings of a complete Noetherian local test.

For the centralizer parameter, the proof invokes
`noetherianAffineFibrewiseTorusCentralizersRepresentable`. Its charts classify
actual identity jets of smooth closed geometrically connected subgroup families
with torus-centralizer residue fibres. Each chart fixes a first-jet rank and a
finite jet order. Its lifting locus is the intersection of the rank locus and
the locus where the family is open in its jet stabilizer. Over a residue field
some finite jet stabilizer equals the normalizer, in which the centralizer is
open. This yields local chart coverage. Zariski descent and gluing give the
locally finite-type parameter and its universal closed subgroup.

An actual closed torus on any test has a smooth closed geometrically connected
centralizer with the required residue fibres. The proof uses its subgroup-functor
equality to specialize the universal property of the glued parameter to the
centralizers of actual tori. The Artinian lifting criterion then proves
smoothness of this parameter. On an elementary Artinian extension one recognizes
the given subgroup as a torus centralizer, lifts the torus, and classifies the
new centralizer. Base change and uniqueness recover the original point.

The assembly theorem represents tori with the specified centralizer by an
étale scheme over the smooth centralizer parameter. A test torus determines its
point of the centralizer parameter first and then its unique point of the étale
scheme. The ambient pullback comparisons preserve literal subgroup-functor
equality. The reductions in the assembly pass through the relative identity
component and Noetherian affine models to give the result on arbitrary bases.

The proof uses Raynaud's finite-jet method and centralizer lifting argument in
SGA 3, Exposé XV, §§5.2–5.5 and Proposition 7.1(i), and the adic and étale steps
leading to Theorem 8.9(a) and Corollary 8.11. See the Gille–Polo recomposition of
1 December 2008, recomposed pp. 264–269, 282–283, and 288–295 (PDF pp. 32–37,
50–51, and 56–63), registered as `sga3-expose-xv-raynaud-2008`.
