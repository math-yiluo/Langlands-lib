# Coefficient automorphisms on rational-component quotients

Author: Worker 1107.

Let `k,L : Type u` be fields with `Algebra k L`, and let `H` be an actual
smooth affine group scheme over `Spec k`. Write `H_L` for the published
`GaloisPointComparison.baseChanged k L H`. The construction
`IdentityComponent.rationalComponentGaloisAction k L H` is the homomorphism

`Aut_k(L) →* MulAut (H_L(L) / (H_L)⁰(L))`

induced by the published coefficient action on actual rational points.
The quotient is the existing ordinary group
`RationalComponentQuotient H_L`, with the identity-component subgroup
interpreted as the image of the actual inclusion `(H_L)⁰ → H_L`.
The field extension is arbitrary; finite-dimensionality and the
Galois-extension property are not assumptions. The fields, group schemes
and test schemes share one arbitrary universe `u`.

## Point comparisons and subgroup preservation

The first three lemmas are in namespace `GaloisPointComparison` and
require no smoothness or affineness. `rationalConjugate_naturality`
proves that the point action commutes with the actual base change of
every group-scheme homomorphism defined over `k`. Its proof uses the
injective comparison `baseChangeCoeffEquiv`, its naturality, and the
published coefficient-action law `affinePointAut_target`.

`rationalExtend_eq_baseChangeSectionHom` identifies coefficient extension
with the existing pullback of rational sections. Both morphisms into the
actual scheme pullback have the same first projection, by their published
projection laws, and the same second projection, by their equations over
the base. Pullback extensionality proves equality.
`rationalConjugate_baseChangeSectionHom` then uses the coefficient
comparison and `GaloisPoint.conjugate_extend` to prove that every
pulled-back rational section is fixed.

The remaining declarations are in namespace `IdentityComponent` and
assume smoothness and affineness of `H`.
`rationalConjugate_mem_rationalIdentitySubgroup` constructs a factorization
through `(H_L)⁰` after conjugation. Write an identity-subgroup element
as a section `y` of `(H_L)⁰` followed by the inclusion. The inverse of
`baseChangeIso H (algebraMap k L)` turns `y` into a section of `(H⁰)_L`.
Conjugate that section using the coefficient action for the actual
`k`-group `H⁰`, and compose with the forward comparison to `(H_L)⁰`.
Naturality for `H⁰ → H` and both comparison inclusion equations prove the
required factorization. Applying this preservation to the inverse
coefficient automorphism gives
`rationalConjugate_mem_rationalIdentitySubgroup_iff`.

## Quotient action and fixed classes

`rationalComponentConjugateHom` is the universal quotient lift of point
conjugation followed by `rationalComponentProjection`. Subgroup
preservation supplies its kernel condition.
`rationalComponentConjugateHom_projection` computes its value on every
projected rational point. The identity and composition laws, named
`rationalComponentConjugateHom_one` and
`rationalComponentConjugateHom_mul`, follow on representatives from the
published point-action laws and surjectivity of the quotient projection.

`rationalComponentConjugate` packages this homomorphism as an automorphism
whose inverse is induced by the inverse coefficient automorphism. The
homomorphism composition laws prove both inverse equations.
`rationalComponentConjugate_toMonoidHom` and
`rationalComponentConjugate_projection` record its underlying homomorphism
and representative equation. Its identity and composition laws,
`rationalComponentConjugate_one` and `rationalComponentConjugate_mul`,
give `rationalComponentGaloisAction`.

`rationalComponentConjugate_baseChange` proves that every class in the
image of the published `rationalComponentBaseChange H (algebraMap k L)`
is fixed. On representatives this is the fixedness of pulled-back
sections above. `rationalComponentFixedSubgroup` forms the ordinary
subgroup of classes fixed by every coefficient automorphism, with
membership equation `mem_rationalComponentFixedSubgroup`.
`rationalComponentBaseChangeToFixed` factors the field-extension map
through this subgroup, and `rationalComponentBaseChangeToFixed_val`
computes its underlying value. Its injectivity,
`rationalComponentBaseChangeToFixed_injective`, follows from the published
injectivity of field extension on rational-component quotients.

For another smooth affine `k`-group `H'`,
`rationalComponentConjugate_naturality` proves that the quotient map
induced by the actual base change of a homomorphism `H → H'` commutes
with these automorphisms. Surjectivity of the projection reduces it to
the point naturality proved at the beginning.

## Provenance and scope

This is internal derived content. It composes the published
`GaloisPointRational`, `AffinePointAutomorphisms`,
`IdentityComponentRationalBaseChange`, `IdentityComponentRationalTransport`
and identity-component base-change constructions. The preceding paragraphs
describe the implemented Lean proofs of their new composition laws; no
external structure theorem is introduced.

There is no characteristic, perfection, connectedness or reductivity
assumption. This module constructs ordinary group actions and fixed
subgroups. It constructs no quotient scheme or sheaf quotient, makes no
comparison with points of such a quotient, and asserts no surjectivity
onto the subgroup of fixed classes. It supplies neither a topology or
continuity theorem for the action nor a comparison with a Galois action
on a scheme of connected components or on root data.
