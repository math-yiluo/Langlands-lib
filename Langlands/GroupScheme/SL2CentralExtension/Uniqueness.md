# Uniqueness of sections of central extensions of SL₂

This internal helper development supplies the uniqueness step for central
extensions of the actual binary special linear group over an arbitrary scheme.
The reference target is Conrad, *Reductive group schemes* (2014),
Proposition 4.3.1, pp.126–131. The proof here uses the Library's published
relative semisimple fppf perfectness theorem.

`binarySpecialLinear S` is exactly the integral binary special linear model
base changed along the canonical map from `S` to `Spec ℤ`. Reductivity follows
from reductivity over every commutative ring and preservation under arbitrary
base change. Every geometric fibre is identified with the special linear model
over the corresponding algebraically closed residue field. The published simple
connectedness theorem supplies its semisimplicity. Relative perfectness therefore
shows that every point is fppf-locally in the abstract commutator subgroup.

For abstract groups, `centralDifference F G h` is the homomorphism
`a ↦ F(a) G(a)⁻¹` into the center, assuming those values are central.
The centrality hypothesis gives its multiplication law. Since the center is
commutative, this homomorphism kills the commutator subgroup; consequently
`F` and `G` agree there.

`section_unique_of_locallyCommutator` applies this argument to group schemes.
For two sections `s₁` and `s₂` of `q`, the difference of their values on any
point is killed by `q`. Kernel exactness puts that difference in the range of
the central homomorphism `z`, so it is central in the group of points. On an
fppf cover witnessing commutator membership of the original point, the two
sections therefore agree. The effective epimorphism property of fppf covers
descends this equality. Pointwise equality then gives equality of the section
morphisms. This general lemma only assumes kernel inclusion into the range of
`z` and centrality of `z`, together with local commutator membership for the
quotient group scheme.

`binarySpecialLinear_section_unique` specializes this result to the exact
binary special linear model and the kernel and centrality hypotheses of the
published main statement. The remaining main hypotheses—separatedness and
commutativity of the kernel group, monicity of its map, and fppf-local lifting
along `q`—are not needed for this uniqueness argument. The signature includes
a commutative kernel group to match the main statement.

These are derived helpers. The module does not establish existence of a
section of any central extension.
