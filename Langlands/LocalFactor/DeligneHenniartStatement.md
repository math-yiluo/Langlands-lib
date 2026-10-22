# Deligne--Henniart virtual twist stability

`Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.VirtualStabilityStatement`
is the proposition combining Deligne--Henniart Theorem 4.6 with the coarser
witness and valuation of Theorem 4.2, for finite extensions of the p-adic numbers.
It is a theorem statement, not a proof. Worker 46 authored the formulation;
Worker 33 contributed the base-component construction.

## Actual objects and scope

The quantifiers range over every prime `p`, every `PadicField F`, every supplied
reciprocity family `e`, and every assignment `epsilon` satisfying the published
`NonabelianSystem.IsSystem F e epsilon`. That hypothesis contains normalized
coherent reciprocity, additivity, Haar scaling, degree-zero induction and
agreement with the actual rank-one epsilon expression. It contains none of the
twisting conclusions below. No local-constant system is selected from an
unproved existence proposition.

`baseExtension F` is the bottom intermediate field in the fixed algebraic
closure: the actual image of `F`. Its field operations and p-adic algebra
structure are the existing ones. `fieldData F (baseExtension F)` supplies the
canonical local topology, normalized integer valuation, principal units and
additive conductor on this field. In particular, the valuation of a uniformizer
is one, and `n(psi)` is the largest integer for which `psi` is trivial on
`pi^(-n) O`. This is the conductor convention of DH81 section 0.3.

`baseWeil_eq_top` proves that the fixing subgroup is the whole actual local
Weil group: it unfolds the subgroup, uses the fixing subgroup of the bottom
intermediate field, and takes the preimage of the top subgroup.
`baseWeilInclusion` is its literal continuous subtype inclusion.
`realizeAtBase` first applies the published forward `LocalWeil.realizeExact`
map from the signed irreducible Weil lattice to continuous exact K0, then
restricts along this inclusion. `degree_realizeAtBase` proves preservation of
dimension using the degree identities for those two maps. No inverse to the
irreducible-lattice realization is chosen. The arbitrary base field makes this
a formulation for every p-adic local field; it does not assert a transport
comparison for designated non-base intermediate fields in one fixed system.

The lattice uses genuine continuous irreducible Weil isomorphism classes,
with finite signed integer coefficients. Carrier universes are `max uF uV`,
as required by the existing common-closure system. The input `v` has nonempty
signed constituent support and `PositiveBreakSupport F v`. Write

\[
a=\min\{\operatorname{break}(b):v(b)\ne0\}>0.
\]

The labels are the published intrinsic last breaks of the actual upper
ramification action. This is the source's alpha(v) on its wild constituent
support. The support uses surviving signed Weil constituents; coefficients
are not combined after restricting to inertia or merely by equality of labels.
Negative coefficients and negative total dimension are permitted. The zero
input `v` is excluded explicitly, so alpha(0) is never assigned a value.

## Exact and approximate witnesses

For a continuous nontrivial unitary additive character `psi`, `ExactWitness`
says that for every virtual lattice element `w` of signed dimension zero with
all surviving breaks strictly less than `a/2`, and for every regular additive
Haar measure `mu`,

\[
 \epsilon(w\otimes v,\psi,\mu)=\det(w)(\gamma).
\]

Both tensor arguments are their actual `realizeAtBase` images, tensor product
is the published continuous exact tensor operation, and the determinant is the
published exact determinant character. Evaluation at the field unit `gamma`
is expressed by requiring the displayed equality at every Weil element `g`
whose image under `reciprocityUnits F e (baseExtension F)` is `gamma`. This map
is the quotient projection to the actual topological abelianization followed
by the supplied reciprocity isomorphism. Thus it is surjective and its lift
formulation is nonvacuous; it chooses no inverse reciprocity lift. The statement
requires every lift, without assuming a separate determinant factorization.
The zero test `w` is included by the vacuous support bound, with no beta(0).

`ApproximateWitness` uses the larger strict bound `a`, and replaces the equality
by equality of the two `p^n`-th powers for some natural number `n`. For complex
units this says exactly that the epsilon/determinant ratio is a root of unity
of p-power order. The exponent is quantified after the test, measure and lift;
no uniform exponent is claimed. This is the relation in DH81 (4.2.1).

## The proposition

For every such `psi` and wild nonzero `v`, the proposition supplies a field
unit `gamma` with the following properties:

1. Its normalized valuation is
   \[
   \operatorname{ord}(\gamma)=A_{\mathrm{wild}}(v)+\dim(v)n(\psi),\qquad
   A_{\mathrm{wild}}(v)=\sum_b v(b)\operatorname{rank}(b)
                                    (1+\operatorname{break}(b)).
   \]
2. It is an exact witness. Moreover, a unit `gamma'` is an exact witness if and
   only if `gamma'/gamma` belongs to `principalUnits (ceil(a/2))`.
3. There is an approximate witness `gamma0`, congruent to `gamma` modulo
   `principalUnits 1`; a unit `gamma0'` is an approximate witness if and only
   if `gamma0'/gamma0` belongs to `principalUnits 1`.

The natural ceiling is appropriate because `a/2` is positive, the normalized
valuation is integral, and DH81 section 0.1 defines U(t) by the non-strict
condition `ord(u-1) >= t`. This gives the full witness coset, not merely
uniqueness of two selected witnesses. The universal Haar quantifier expresses
measure independence in dimension zero: `w tensor v` has dimension zero.

`wildArtinSum` constructs the displayed finite real sum. DH81 sections 0.5--0.6
give its arithmetic interpretation on wild support: Artin conductor is
dimension minus the inertia-invariant dimension plus Swan conductor, and the
Swan conductor of an irreducible is its rank times its unique break. A wild
irreducible has zero inertia invariants. The constructor itself does not prove
a general conductor descent theorem or this identification. This source
interpretation justifies the expression in the proposition without assuming
an unproved exact-lattice inverse or a selected finite-image presentation.

## Source correspondence and provenance

Original source: P. Deligne and G. Henniart, *Sur la variation, par torsion, des
constantes locales d'equations fonctionnelles de fonctions L* (1981), registered
as `deligne-henniart-1981-variation`, SHA256
`54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
The source locations are:

- Sections 0.1 and 0.3--0.6, printed pp.91--92 (PDF pp.3--4): unit filtration,
  additive conductor, signed virtual constituents and break conventions.
- Section 4.1 and Theorem 4.2, printed p.108 (PDF p.20): the approximate witness,
  uniqueness modulo U(1), and valuation formula (4.2.2).
- Theorem 4.6, printed p.110 (PDF p.22): the exact half-break relation,
  uniqueness modulo U(alpha/2), and congruence with the witness from (4.2.1).
- Section 4.19, printed p.116 (PDF p.28): a sign discrepancy in its recap,
  documented below rather than used as the valuation formula.

The exact and approximate relations translate 4.6 and 4.2(i). The valuation
clause follows from 4.2(ii) and the congruence in 4.6, since U(1) has valuation
zero. Thus the combined proposition has derived provenance. Section 4.2.2
prints `a(v) + dim(v)n(psi)`; section 4.19 prints a conflicting minus sign.
The plus sign agrees with 4.1.1 and the additive-conductor convention in 0.3.
The Lean statement uses the plus sign from 4.2.2 explicitly.

This is the ordinary unshifted epsilon relation. There is no spectral,
Weil--Deligne or equal-characteristic extension here. The source's additional
rank-one sufficiency assertions in 4.2(iii) are not separate targets in this
file. The broad host task also contains other theorem-statement families;
this unit covers its full wild virtual twisting relation and witness cosets,
and does not claim whole-task completion or prove the stated arithmetic result.
