# Identity components and semisimple representations over an algebraically closed field

This module is internal supporting work for the proof of
`Langlands.GroupScheme.CharZeroSemisimpleRepresentationIdentityComponentStatement`. It proves the
two directions of Milne's Corollary 22.43 for the rational-point representations of a smooth
affine group over an algebraically closed field of characteristic zero. The direction "all
representations semisimple ⇒ identity component reductive" takes Milne's Theorem 22.42, in the
form of the published statement `CharZeroReductiveSemisimpleRepresentationStatement`, as an
explicit hypothesis `h22`.

Throughout, `k : Type u` is a field and `J` is a group scheme over `Spec k` with
`[Smooth J.X.hom]` and `[IsAffineHom J.X.hom]`. `rationalIdentitySubgroup J` is the published
normal subgroup of rational points factoring through `identityComponentι J`
(`IdentityComponentRationalQuotient`).

## General lemmas

- `isSemisimpleRepresentation_iff_of_range_eq`: two representations of possibly different
  monoids on the same space with the same image are simultaneously semisimple; their
  subrepresentation lattices are order isomorphic. The shared order isomorphism is imported from `Representation.Category.SubrepresentationRange`.
- `range_rationalRepresentation_comp_rationalIdentitySubgroup`: the restriction of
  `ρ.rationalRepresentation` to `rationalIdentitySubgroup J` has the same image as the
  rational-point representation of `ρ.restrict (identityComponentι J)`. It uses
  `mem_rationalIdentitySubgroup` and `rationalMatrix_restrict`.
- The instance `finiteIndex_rationalIdentitySubgroup`: `rationalIdentitySubgroup J` has finite
  index, from the published `finite_rationalComponentQuotient` (the quotient embeds in the
  finitely many connected components of `J`).
- `isClosedSubgroup_restrict_identityComponentι`: if `ψ : MatrixRepresentation J (Fin N)` is a
  closed subgroup (`IsClosedSubgroup ψ`, a closed immersion), so is
  `ψ.restrict (identityComponentι J)`, because the inclusion of the identity component is a
  closed immersion.

## The two directions

Assume moreover `[IsAlgClosed k]` and `[CharZero k]`.

- `rationalRepresentation_isSemisimple_of_identityComponent`: if
  `IsPseudoReductive (identityComponent J)`, then for every finite index type `n` and every
  `ρ : MatrixRepresentation J n`, `ρ.rationalRepresentation` is semisimple. The restriction to
  `identityComponent J` has semisimple rational-point representation by the published
  `reductiveCharZeroSemisimplicityStatement`; by the range comparison, so does the restriction of
  `ρ.rationalRepresentation` to the normal subgroup `rationalIdentitySubgroup J` of finite index;
  the published `finiteIndexSemisimplicityAscent` (characteristic zero) gives semisimplicity of
  `ρ.rationalRepresentation`. This is the averaging over `G(k^a)/G°(k^a)` in Milne's proof of
  22.43 "if".
- `identityComponent_isConnectedReductive_of_faithful h22 ψ hψ hss`: if
  `ψ : MatrixRepresentation J (Fin N)` is a closed subgroup whose rational-point representation is
  semisimple, then `IsConnectedReductive (identityComponent J)`. The published Clifford theorem
  `finiteDimensionalNormalRestrictionSemisimplicity` makes the restriction to the normal subgroup
  `rationalIdentitySubgroup J` semisimple; by the range comparison and
  `isSemisimpleStable_iff_rationalRepresentation` (module `RationalBridge`, applied to the
  reduced identity component) the closed-subgroup representation
  `ψ.restrict (identityComponentι J)` of the connected group `identityComponent J` is semisimple
  in the all-test sense; the second conjunct of `h22` ((c) ⇒ (a) of Milne 22.42) concludes.

## Provenance

Internal and derived. The route is Milne's proof of Corollary 22.43 (J. S. Milne, *Algebraic
Groups* (2017), registered as `milne-2017-algebraic-groups`, printed p. 478, PDF p. 494),
carried out on the abstract groups of rational points over an algebraically closed field: the
normality of `G°` (Proposition 1.52, printed p. 21) enters through the published normality of
`rationalIdentitySubgroup`, the finiteness of `G(k)/G°(k)` through the published finite
component quotient, and Theorem 22.42 (printed p. 477) through the hypothesis `h22`.
