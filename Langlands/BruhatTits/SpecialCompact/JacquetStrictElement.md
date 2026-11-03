# Strict elements from actual standard cocharacters

This supporting module retains standard-cocharacter existence as an explicit
premise. Given such a cocharacter and the actual compatible split component
from `SimultaneousStandardBasisAt`, it constructs an element of the actual
standard Levi, the intrinsic common-uniformizer section, the weak chamber and
the strict chamber. It does not prove standard-cocharacter existence or the
unconditional adapter statement.

`IsCompatibleStandardSplitComponent.strictElement` chooses such an element
from the proved existential. Its four memberships are recorded together in
`strictElement_spec`. The arguments contain no open subgroup, so this element
is fixed before a Levi or ambient open subgroup is specified.

The published theorem
`IsStandardCocharacter.isCentral_standardLeviTorusFactor` makes the chosen
cocharacter central in the represented standard Levi. Maximality of its split
component factors this central homomorphism through that component, integrally.
Monicity of the ambient maximal split torus identifies the resulting composite
with the original cocharacter. Thus the pairing of each restricted outside
simple root with its lift is positive. The intrinsic uniformizer evaluation
identity turns these positive pairings into strict normalized norm inequalities.
The image of the section point belongs to the actual standard Levi by its
representing inclusion, and to the three specified section/chamber sets by
their definitions. Weak inequalities follow from the strict inequalities.

The provenance is derived use of the published actual standard-Levi torus and
split-component factorization results, together with the intrinsic evaluation
helper. There is no chosen coordinate torus, replacement topology, extra
strict-chamber premise for the final target, or use of real-image surjectivity.
