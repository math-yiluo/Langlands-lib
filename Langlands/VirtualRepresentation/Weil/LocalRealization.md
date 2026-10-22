# Actual local Weil realization and finite induced-character lattices

Author: Worker 24. This derived construction specializes the published
realization and induction interfaces to the actual local Weil group.

For every actual `PadicField p`, this module realizes the genuine local
irreducible lattice in the split Grothendieck group of representations of
`localWeilGroup F`. Its trace map is the trace of those actual representation
classes, extended by integral linearity. The range restriction has the actual
trace image as codomain. The unitary trace map is the restriction along the
constructed inclusion of the specified local unitary basis. Field, carrier and
finite target-group universes remain independent.

For a finite group `Q` and an explicit homomorphism
`q : Field.absoluteGaloisGroup F.Carrier ->* Q`, `finiteMap F q` is its
composite with the actual `localProjection F`. No group standing in for the
Weil group is supplied. An inducing datum is an actual subgroup of `Q` and a
unit-valued one-dimensional character. `inflatedMonomial` forms its genuine
finite-group induced representation, passes to its split virtual class, and
restricts along that composite.

The induced virtual span is the integral span of these objects. The induced
character lattice is its image under actual trace realization. The generator
and evaluation maps take values in the span using the proved generic
membership constructor. `inflatedMonomial_character` follows the imported
restriction and trace formulas to prove that evaluation at an actual Weil
element is the induced finite-group trace evaluated at its actual image.

The supplied map is not asserted to be continuous or surjective. Consequently
this algebraic construction does not silently assert continuous irreducible
decompositions of every inflated representation. When a particular continuous
finite Galois quotient map is constructed, it can be used here through its
underlying homomorphism. Constructing maps for every actual finite extension
and proving their topological properties remains with the local Weil branch.

The virtual and trace preimages in the actual irreducible lattice are defined
separately. Their unitary versions are inverse images along the actual unitary
inclusion. The implemented inclusion from virtual preimage to trace preimage
uses the same realized virtual element as its image witness. It needs no
character-faithfulness theorem. No converse, equality with finite-factorization
support, irreducible decomposition, Brauer spanning, or local correspondence
is assumed or proved by these definitions.

## Sources and dependencies

This is derived assembly of the free groups and actual induced-character
construction in Henniart (2000), sections 2.5--2.6, printed pp.445--447,
section 3.1, p.448, and section 3.7, p.451. These passages were read in the
retained original, literature ID `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The split completion and trace image remain distinct, as explained in the
generic Realization pair. Worker 20 separately owns exact-sequence
Grothendieck constructions; no split/exact comparison is used here.

The two direct imports are `Langlands.VirtualRepresentation.Weil.Local` and
`Langlands.VirtualRepresentation.Weil.Realization`. The local lattice module
uses the published `Langlands.Weil.Local.Parameters` and actual local assembly.
The generic realization module uses the published finite representation classes,
induction and split virtual representation interfaces. Their exact definitions
and source conventions are documented in the respective paired Markdown.
The only additional assumptions here are the displayed finite group and supplied
absolute Galois homomorphism. Field, representation-carrier and finite target
group universes are independent; coefficients are complex for representations
and integral for lattices.

The weak-association generating families on the Weil and supercuspidal sides,
their compatibility, numerical orbit data and the actual local basis
operations remain separate required constructions. These finite induced spans
do not define those global families.
