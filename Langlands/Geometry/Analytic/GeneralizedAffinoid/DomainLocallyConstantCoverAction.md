# Continuous equivariant locally constant descent on finite spectrum covers

Worker 56 constructs the continuous action on all compatible locally
constant families on a finite cover's original representing spectra, and
an equivariant restriction/gluing isomorphism with functions on the actual
target locus. The inputs are a presented affinoid algebra over a complete
ultrametric normed field, a `DomainSpectralAction` of a topological group
`G`, an open subgroup `H`, an `H`-invariant represented domain `d`, a
finite represented-domain cover `c` of `d.obj`, and a coefficient set `A`
in an independent universe. No topology or action on `A` is assumed.

`DiscreteSpectrumCompatibleFamily` is the full subtype of families of
`DiscreteLocallyConstant` functions on the original component spectra.
Its equations are exactly `SpectrumLocallyConstantCompatible`: all values
agree on any pair of component-spectrum points with equal images under
the original component maps, including pairs in a single spectrum.
The topology is inherited from the finite product of discrete function
spaces, so it is discrete. The wrappers retain the complete original
locally constant function sets.

`discreteSpectrumRestrict` is precomposition with the original component
maps. `discreteSpectrumGlue` uses the existing direct spectrum gluing:
assemble the component functions on the original finite disjoint union,
then descend along `c.totalMap` using its proved quotient topology and
the complete equal-image equations. At `c.componentMap i x` the result
is the original value `f i x`. This evaluation law proves restriction
after gluing; the surjectivity of `c.totalMap` proves gluing after
restriction. `discreteSpectrumEquiv` records both inverse laws.

The acting group is the existing `finiteFamilyOpenSubgroup H c.obj`,
with its original subspace topology. It is the largest open subgroup
inside `H` preserving every component locus. The target and component
representations remain unchanged. The existing `finiteCoverComponent_smul`
from `DomainLocallyConstantCoverStabilizer` expresses the component morphism's
pointwise equivariance and supplies the compatibility used below.

`finiteCoverCompatibleLocallyConstantSmul` acts separately on every
component by the original inverse-precomposition operator:
its value at `i, x` is `f i (g⁻¹ • x)`. Component equivariance sends
equal-image pairs to equal-image pairs under inverse translation,
so these operators preserve the complete compatibility equations.
The component action laws give the family action laws.
`finiteCoverCompatibleLocallyConstantAction` proves joint continuity
by using the already proved continuous action on each compact spectrum's
discrete function space, the product continuity criterion, and continuity
into a subtype. The subgroup topology is unchanged.

`finiteCoverLocallyConstantDescentIso` bundles the original restriction
and constructed gluing as an isomorphism in `ContAction TopCat` for this
same common subgroup. Both maps are continuous because their function
spaces are discrete. Equivariance of each original component map at
the inverse group element proves restriction equivariance. `Action.mkIso`
then derives inverse equivariance from the two inverse laws.
The final evaluation lemmas retain the original component maps in both
directions.

This is an internal consequence of the actual compact geometric actions,
the original finite spectrum quotient, and the previously constructed
locally constant descent and discrete function actions. No descended
function or function fixedness is supplied as an input. Positive
polyradii, arbitrary closed ideals, nilpotents, trivial valuations,
empty loci, empty covers and empty coefficient sets are retained.
The construction concerns local constant-coefficient function data;
arbitrary equivariant sheaf descent, analytic etale site comparison
and the Harris tower remain separate obligations.
