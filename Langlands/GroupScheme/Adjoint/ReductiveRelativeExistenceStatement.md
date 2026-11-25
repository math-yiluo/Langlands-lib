# Existence of a reductive relative adjoint quotient: statement

This module defines the proposition
`Langlands.GroupScheme.ReductiveRelativeAdjointQuotientExistenceStatement.{u}`.
It does not prove it unconditionally. It proves implications in both
directions between this proposition and the published affine quotient
existence statement.

## Exact assertion

For every scheme `S : Scheme.{u}` and every group scheme `G` over `S`
satisfying `IsReductive G`, there exist an actual group scheme `A` over
`S` and an actual group-scheme homomorphism `q : G ⟶ A` satisfying
`IsRelativeAdjointQuotient q`.

The imported predicate requires reductivity of `G` and `A`, flatness,
surjectivity and local finite presentation of the underlying morphism of
`q`, and equality of the actual kernel range with the full
scheme-theoretic centre `center G` on all relative test schemes. The
source reductivity field repeats the premise. No part of `A`, `q` or
their quotient properties is supplied as a hypothesis.

The base is arbitrary: it need not be affine, reduced, connected,
noetherian or the spectrum of a field. No splitting, henselian,
completeness or residue-field condition is imposed. The centre can be
nonsmooth and can have positive dimension; `q` is not required to be
finite or an isogeny.

This is an existence statement for a relative quotient, stronger in
base scope than its application over a discrete valuation ring. It does
not assert existence of a relative isomorphism scheme, outer component
or inner-isomorphism torsor. The imported adapter proves the resulting
inner action and its base-change and field compatibility conditionally
on the quotient.

## Relation to the affine quotient statement

The published `RelativeAdjointQuotientExistenceStatement` in
`Adjoint.RelativeExistenceStatement` retains the affine target and full-centre
fppf quotient, without requiring target reductivity. That declaration and
its module remain unchanged.

`ReductiveRelativeAdjointQuotientExistenceStatement.of_affine` proves
that the published affine statement implies this reductive version.
It applies the supplied-quotient theorem `isRelativeAdjointQuotient`
from `Adjoint.RelativeReductivity` to the actual affine quotient obtained
from the hypothesis. That helper descends flatness and finite presentation,
uses the published field centre-quotient theorem on every field-valued
pullback, and applies the smooth-fibre criterion; its paired Markdown
describes the implemented proof.

`ReductiveRelativeAdjointQuotientExistenceStatement.to_affine` proves
the reverse implication by retaining affineness of the reductive target
and the same actual quotient map. Thus the two proposition definitions
are equivalent by proved implications. The unconditional construction of
the quotient is `relativeAdjointQuotientExistence` in
`Adjoint.RelativeExistenceProof`, which proves the affine statement; the
stronger formulation needs no separate existence proof.

## Original source and derived packaging

Brian Conrad, *Reductive group schemes* (2014), registered source
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`:

- Theorem 3.3.4, printed/PDF p.98, identifies the full scheme-theoretic
  centre of any reductive group scheme with its reductive centre,
  hence with a central subgroup of multiplicative type.
- The proof of Lemma 3.3.2, printed/PDF p.98, states that the fppf
  quotient by such a central multiplicative-type subgroup is represented
  by an affine scheme of finite presentation over the base, with its
  natural group structure.
- Corollary 3.3.5, printed/PDF p.100, treats the resulting quotient as
  reductive and identifies its centre; for the full centre it is
  trivial.

This Lean assertion is derived packaging of those results using the
Library's actual-kernel interface. The fppf quotient sheaf condition
gives a flat surjective quotient morphism and the full scheme-theoretic
kernel, rather than only exactness on rational points. Local finite
presentation follows from the finite-presentation quotient and the
source's smoothness and finite presentation over the base. The actual
group-scheme quotient construction and its full fppf kernel belong to the
unconditional proof `relativeAdjointQuotientExistence`, not to this
module. The included internal helper
proves reductivity from the affine quotient once it is supplied.
Triviality of the centre of the relative target is not an additional
field of the statement.

The retained source index records
`conrad-author-reductive-errata-check-2026-11-13`: its bounded check of
the author's homepage found no separate correction link attached to
the reductive-group notes, and the available author PDF matched the
registered PDF. No broader absence-of-errata claim is used.
