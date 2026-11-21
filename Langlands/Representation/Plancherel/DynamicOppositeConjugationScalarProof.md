# Conjugation of the canonical opposite scalar

`Langlands.Plancherel.conditionalDynamicOppositeConjugationScalar` proves
`Langlands.Plancherel.ConditionalDynamicOppositeConjugationScalarStatement.{u,uV}`.
For the conjugate cocharacter, subgroup `gKg⁻¹`, and inducing representation
`gA`, the canonical opposite scalar is the image of the original scalar under
function-field transport along `parameterConjugationIso χ g`. The theorem uses
the published conditional data for both scalars and applies over
nonarchimedean local fields of arbitrary characteristic to connected reductive
groups.

## Section transport

Inverse conjugation `x ↦ g⁻¹ x g` carries both parabolics, the Levi, and both
radicals of the conjugate cocharacter to their original counterparts.
Precomposition gives the equivalences of normalized induced sections.
The Levi projection and the half-modulus character commute with this map, and
`conjugateParameter_apply` identifies the twist at the conjugate parameter with
the pullback of the original twist. The induced section equivalences intertwine
the group actions after pullback by inverse conjugation.

Precomposition on `gKg⁻¹` also gives the two compact-picture equivalences.
In each compact picture the covariance uses the Levi projection and the
untwisted inducing representation, so the equivalence works at every parameter.
Restriction commutes with these equivalences by evaluation at a point of
`gKg⁻¹`. Inverting the two restriction equivalences gives the corresponding
identities for extension to the ambient group.

## Integral and domain transport

On either radical the pushforward under inverse conjugation is a regular
Haar measure. Its mass on the intersection with `K` is one because the
preimage is the intersection of the conjugate radical with `gKg⁻¹`.
Uniqueness of this normalization gives the measure-preserving equivalence
of radicals. The radicals intersect trivially, so each quotient is identified
with the corresponding integration radical by a quotient chart. The Weil
compatibility and the mass-one measure on the trivial intersection make
each chart measure preserving. Composing the charts with inverse
conjugation gives the measure-preserving equivalences of both quotients.

At a quotient representative `v` and an ambient point `x`, the integrand
is the section evaluated at `v * x`. Inverse conjugation respects this
product. Pullback by the Levi equivalence transports the smooth-dual tests,
and change of variables in each scalar test transports the weak integral
in both directions. Transport and its inverse give the equivalences of the
full forward and reverse convergence domains. On each domain the integral
specifications of the two ambient families and uniqueness of the smooth
weak integral identify the corresponding output sections. Extension, this
ambient equality, and restriction give the forward and reverse compact
operator identities.

## Continuations and extraction

Pullback along a group equivalence and equivalence of representations preserve
irreducibility. The section equivalence therefore identifies the pointwise
irreducibility conditions. The helper
`conditionalCanonicalRationalScalar_conjugation_of_compact` pulls back the
source irreducibility open along reverse character restriction. It transports
both continuation denominators along the parameter isomorphism and conjugates
the polynomial numerators by the compact equivalences. The compact operator
identities give the clearing equations for these transported continuations.

Continuation independence and irreducibility-locus independence identify the
target scalar with the scalar computed from these transported data. Evaluating
the original compact composite on a normalized vector and functional, and
using the transported vector and functional for the conjugate composite,
gives coefficients that correspond under character transport. The helper
identifies the fractions presenting these coefficients on their common
regular region by uniqueness of the fraction. The function-field equivalence
then gives the required equality at the actual parameter isomorphism.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
IV.3 (3), printed p. 286 (PDF p. 52). Waldspurger compares the intertwining
operators by an isomorphism of their induced representations. The Lean proof
implements the comparison for the Library's transport statement at an
arbitrary rational point, with the compact subgroup and the measures
transported as well. The registered source is `waldspurger-2003-plancherel`
with PDF SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
[Waldspurger's article](https://doi.org/10.1017/S1474748003000082)
