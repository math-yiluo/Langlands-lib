# Irreducible quotients of induction from an actual rational Levi

Author: Worker 148, Task 5295 (`717df3ca-7a3c-40fc-a8b3-79617086393e`).
Module `Langlands.Representation.LanglandsClassification.LeviInductionQuotient`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

This internal construction prepares quotient existence in Renard VII.4.2 (i).
Its finite-length input corresponds to VI.6.2; the module does not prove that
input. Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The classification passage, printed p.243 / PDF p.249, was read and checked
in the rendered original.

The setting is an actual represented parabolic `p : P → G`, rational Levi
`l : M → P`, geometric unipotent radical `r : U → P` and multiplication
isomorphism `P = MU`. The field has a Hausdorff topology; the rational points
of `G` have the canonical topology and are assumed locally compact and
nonarchimedean. The smooth representation `σ` of `M(F)` has carrier in an
independent universe `v`, while the field and rational point groups lie in
universe `u`. The output induction and quotient carriers lie in `max u v`.
No characteristic, standardness or chamber condition is imposed.

`nontrivial_leviInduction` proves that the published transported normalized
induction of any nonzero `σ` is nonzero. It pulls `σ` back along the inverse
of the published actual Levi-point equivalence, uses the proved continuity
of the semidirect projection and invokes the published
`nontrivial_normalizedInduction`. That result proves surjectivity of
evaluation at the identity by a compact local section with prescribed
value. This step has no finite-length or admissibility premise.

`exists_irreducibleLeviInductionQuotient` assumes that this particular
induction functor preserves group-algebra finite length and that `σ` is
irreducible. The published `SmoothRep.hasFiniteLength_of_isIrreducible`
supplies finite length of the input, so preservation supplies finite length
of the actual induction. The preceding nonzeroness result and the published
`RegularHeadExistence.exists_irreducibleQuotient_of_finiteLength` then give
a smooth irreducible quotient with an actual surjective intertwiner.
The latter helper chooses a coatom invariant submodule and forms its smooth
quotient.

`irreducibleLeviInductionQuotient` is the actual definition entry: it chooses
one of the resulting smooth quotient representations and returns its full
`Classification.IsIrreducibleQuotient` certificate. No canonical choice or
uniqueness is claimed.

The construction applies to the irreducible unramified twist in a Langlands
triplet after supplying finite-length preservation for its induction
functor. The general preservation target
`LeviInductionFiniteLengthStatement` would supply that premise. This module
does not prove that target, the strong-head assertion, injectivity of
Langlands parameters, or exhaustion of irreducible representations.
