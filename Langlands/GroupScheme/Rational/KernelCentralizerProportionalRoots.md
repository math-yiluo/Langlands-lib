# Proportional-root centralizers inside full character-kernel centralizers

Author: Worker 1465.

This internal unit constructs an all-test containment used in the classical
maximal-torus argument. It works over any field and in any universe. The ambient
group is connected reductive, its specified maximal torus is split, and a second
split torus maps into that maximal torus. The character of the second torus is
nonzero but need not be primitive.

`map_mem_kernelCentralizer` proves directly from universal commutation that a
group-scheme homomorphism carries a full character-kernel centralizer into the
corresponding ambient centralizer. The kernel remains the actual scheme kernel.

`root_eq_or_neg_of_proportionalCentralizer` uses the published generic
cocharacter attached to an ambient root. Every root of its actual centralizer
is an ambient root annihilating that cocharacter, so is integrally dependent
with the chosen root. Published reducedness for the split maximal torus makes
it equal to that root or its negative.

`range_proportionalCentralizer_le_kernelCentralizer` assumes that the chosen
ambient root restricts to an integer multiple of the supplied character. The
preceding root comparison makes every root of the proportional-root
centralizer restrict to an integer multiple as well. Split-torus weight
decomposition gives full integral tangent support, and the published smooth
kernel-centralizer structure and connected closed-subgroup tangent equality
force its internal full-kernel centralizer to be the entire group. Universal
commutation then maps to the ambient group. The resulting containment includes
all test schemes and keeps any torsion in the character quotient.

`proportionalRootCentralizerData` packages the canonical cocharacter, actual
centralizer group, all-test representing inclusion and annihilation equation
as `RadicalFreeRootCentralizerData`. Its radical witness follows from the
published unconditional reductivity theorem for cocharacter centralizers,
then the implication from connected reductivity to trivial ground-field
unipotent radical. This constructor needs no maximality assumption on the
torus; maximality is used only in the preceding proportional-root containment.

The provenance is internal composition of published root reducedness, the
actual generic cocharacter centralizer, and the integral-weight support unit.
This unit does not yet construct the ambient maximal torus or prove the
arbitrary-field identity-component reductivity statement.
