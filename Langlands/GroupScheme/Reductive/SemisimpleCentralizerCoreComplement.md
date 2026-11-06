# Semisimple centralizer-core complements from almost-simple generation

Worker 1783, with Worker 1616's proposed reduced-centralizer construction and
normal-subgroup semisimplicity interface.

Over an algebraically closed field of arbitrary universe and characteristic,
let `G` be semisimple and `j : H ⟶ G` a smooth connected closed normal subgroup.
This module keeps `SemisimpleAlmostSimpleGenerationStatement` as an explicit
hypothesis. It does not prove that hypothesis or the unconditional
arbitrary-field normal-isogeny-complement proposition.

`flat_surjective_centralizerCoreMultiplication_of_almostSimpleGeneration`
works with any supplied `C : ClosedNormalCentralizer j` whose group has an
affine locally finite-type structure map. Its second subgroup is exactly
`ReducedSubgroup.identityCore C.group`, included in `G` by
`ReducedSubgroup.identityCoreι C.group ≫ C.inclusion`. The actual multiplication
from `H` times this reduced identity component to `G` is flat and surjective.
The affine locally finite-type hypotheses on `C` follow from its closed
inclusion when `G` is semisimple.

The proof restricts the full centralizer's all-test commutation to its core.
The actual multiplication range contains both factor ranges. For each closed
normal almost-simple subgroup of `G`, the published normal-subgroup dichotomy
places it either inside `H` or in the full centralizer. In the second case,
the actual factorization into the centralizer factors further through its
reduced identity component because the almost-simple source is smooth and
connected. Consequently every such almost-simple subgroup lies in the
multiplication range. The existing schematic-image generation theorem applies
the explicit generation premise and proves flatness and scheme-surjectivity.
All range containments and commutation assertions retain every test scheme.

`semisimpleCentralizerCoreComplementOfAlmostSimpleGeneration` constructs the
corresponding actual `CommutingNormalComplement j`, using the canonical chosen
full normal centralizer and exactly its reduced identity component. Its
inclusion is the composite above. The core is smooth, connected and affine.
Its inclusion is closed by composition, and the existing smooth-action theorem
proves normality on every test. Unconditional normal-subgroup semisimplicity
gives semisimplicity of both `H` and the core. Their finite full centres, the
surjective multiplication just proved, and the finite-centre multiplication
construction prove that their actual product is semisimple and that the same
actual multiplication is a central isogeny. The subtype records all these
properties alongside the chosen complement.

The provenance is internal composition of the published full-centralizer,
almost-simple dichotomy, reduced-subgroup, identity-component, schematic-image,
and multiplication interfaces. It refines the older full-centralizer
construction by using the smooth connected reduced identity component and
retains the unproved generation premise explicitly. No smoothness is asserted
for the full centralizer, the full centres, or the multiplication kernel.
