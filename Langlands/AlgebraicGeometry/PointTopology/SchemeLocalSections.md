# Algebraic sections on actual scheme point spaces

This internal construction bridges actual algebraic sections to the canonical
scheme-point topologies. The base `R` is any commutative ring. The value ring
`S` is a local commutative `R`-algebra with a topology, continuous multiplication
and `IsOpenUnits S`. The schemes and their relative morphisms are arbitrary;
no affineness, finite type or separation hypothesis is added.

`HasOpenSectionsAtPoints R S f` means that every actual `S`-valued point of the
target has its whole image inside an open subscheme `U`, on which there is an
actual relative section `s` satisfying `s ≫ f = openOverι R Y U`. This is a
hypothesis about algebraic morphisms near every actual point. It is not a claim
that a surjective, smooth or quotient morphism automatically has such sections.

`schemeOpenPointHomeomorph` equips the existing `openPointEquiv` with the
canonical final scheme-point topology on the open-subscheme points and the
ambient subspace topology on the locus of points whose image lies in `U`.
The published open-embedding theorem `schemeOpenPoint_proof` supplies the
inducing property. Its open-range property shows that this locus is open.

For each target point choose an algebraic section on an open subscheme
containing that point. On the corresponding open point locus, compose the
inverse of `schemeOpenPointHomeomorph` with postcomposition by that section.
The inverse homeomorphism is continuous, and postcomposition is continuous by
`schemePointContinuity_proof`. The algebraic section identity and category
associativity prove the required section identity on actual points. This proves
`hasContinuousLocalSections_schemePointMap` for exactly the existing
`Langlands.Topology.HasContinuousLocalSections` property.

The surjectivity and quotient-map conclusions then use the generic
continuous-local-sections construction. In particular, the target topology is
the actual quotient topology of postcomposition; no replacement topology is
introduced. This bridge can be used with `R = S = F` over any topological field
satisfying the stated value-ring hypotheses. Algebraic quotient existence,
existence of the local sections, the identification of its fibers, compactness
of the target point space, and the unrestricted dynamic-parabolic compactness
statement all remain separate obligations.

Provenance: this is a derived internal construction from the published actual
open-point equivalence, open embedding and functorial continuity results, together
with the generic continuous-local-sections quotient comparison. The proof does
not invoke an additional external source theorem.

Author: Worker 339. Worker 125 supplied the generic topology construction and
the proposed bridge interface.
