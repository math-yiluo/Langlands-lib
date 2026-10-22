# Differential action on simultaneous center-finite functions

This internal construction connects the actual action in `EnvelopingAction`
to the common-family condition in `CenterFinite`. The field `K` is any number
field in universe `u`, and the rank is any natural number, including zero.
Coefficients are complex. The carrier remains actual continuous,
rational-invariant adelic functions with smooth infinite slices and a common
open finite stabilizer.

`finiteSmoothCenterRepresentation` is the multiplicative representation
underlying the published center algebra action. `finiteSmoothCenterSlices`
is the complex-linear intertwiner taking a function to all its infinite
slices. It is injective, and agrees with the published smooth slice-family
map after the inclusion into the slice-wise smooth ambient space.
Consequently `isCenterFinite_iff_finiteSmoothCenterVector` identifies a finite
center orbit of the actual function with the existing simultaneous condition:
one finite-dimensional orbit of the entire family. This is the same condition
already identified with a single finite-codimensional common annihilator
ideal in `CenterFinite`, not separate bounds for individual slices.

An element of the actual enveloping-algebra center commutes with every element
of that algebra. Applying the genuine algebra homomorphism proves
`finiteSmoothEnvelopingAction_center_commute`. Each enveloping operator is
therefore a center intertwiner, so it takes a finite center orbit into a finite
center orbit. This proves `isCenterFinite_finiteSmoothEnvelopingAction`.
The stronger `centerFamilyAnnihilator_le_differential` shows that every operator
annihilating all the original slices also annihilates all the differentiated
slices. In particular, the same common ideal works after differentiation.

`centerFiniteFiniteSmoothFunctions` is the pullback of the existing
center-finite subspace along the actual finite-smooth inclusion.
`CenterFiniteDifferentialAction` abbreviates the type of complex algebra
homomorphisms from the enveloping algebra to endomorphisms of this subspace.
`centerFiniteEnvelopingAction` restricts the genuine complex algebra action to
this subspace, with its value in the ambient space unchanged. The construction
does not require the ambient function space to be finite-dimensional.

The provenance is internal: faithful equivariant slice extraction and the
published finite-vector image lemma prove the equivalence and preservation;
centrality in the actual enveloping algebra proves the required commutation.
This constructs only the center-finite differential restriction. Growth,
compact-type finiteness, cuspidality, and their simultaneous assembly into
automorphic forms remain separate constructions.
