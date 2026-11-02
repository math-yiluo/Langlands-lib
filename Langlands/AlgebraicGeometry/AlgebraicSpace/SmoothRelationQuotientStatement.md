# The canonical etale quotient of a smooth algebraic-space relation

Worker 59, 1 November 2026.

This module constructs the presheaf and etale sheaf of classes of an actual
algebraic-space equivalence relation on an actual scheme. It states the
geometric quotient theorem required for this sheaf. It does not prove that
the quotient is an algebraic space, that it is effective, or that it has a
smooth presentation or a locally finite type etale atlas.

## Sources and derived scope

The registered original `stacks-smooth-quotient-local-finite-type-2026-11-01`,
SHA-256 `ea18197c7ff281b249564e51225bb653f30bbf175c60df3c275a9a3c15e14072`,
is retained under `literature/Stacks Project- flat equivalence-relation
quotients, etale sheaf criteria, and smooth-local finite type (2026-11-01)/`.
The relevant original HTML pages are:

- `04S6.html`, Theorem 80.10.1(1): the fppf quotient of a flat locally
  finitely presented equivalence relation in algebraic spaces is an
  algebraic space. Smooth projections are a special case.
- `076L.html`, Section 80.12, especially Lemmas 80.12.3–4 and their proofs:
  smooth covers identify the etale and fppf quotients. The proof of Lemma
  80.12.3 records effectiveness and smoothness of the quotient map using
  Groupoids in Spaces 78.19.5 and Descent on Spaces 74.11.26.
- `06FC.html`, Remark 74.20.5(3): local finite type is smooth local on
  source and target. A smooth surjective quotient with a locally finite
  type source consequently has locally finite type etale scheme atlases.

The statement is a derived smooth special case with the canonical quotient
fixed explicitly, rather than an assumption that an unspecified quotient
already exists. The kernel-pair and smooth-map conclusions are retained
from the quoted proof route. Their Lean proofs remain obligations.

This is the general geometric prerequisite of the Picard quotient argument
in Artin, *Versal deformations and algebraic stacks* (1974), Appendix item 2,
printed pp.186–187/PDF pp.22–23, registered as
`artin-1974-versal-deformations-algebraic-stacks`, SHA-256
`9bf1a078bdfa3b3d3dbad8152e408238b2ce367692a0bc1957ed8c255f47ff35`.
Artin first quotients the arrow scheme by the relation of equal endpoints;
the resulting algebraic space is a relation on the object scheme. A second
quotient gives the class sheaf. The generic theorem here contains no Picard
objects, no stack hypothesis, and no assumed Picard representability.

## Actual objects and relations

`IsSmooth` follows the existing `AlgebraicSpace.IsEtale` convention: every
base change along the functor of points of any scheme is represented by an
actual scheme, and every represented projection is smooth. The accompanying
`representable` and `projection` lemmas unpack the two components of this
definition. This predicate describes morphisms representable by schemes;
it is not a definition for all smooth morphisms of algebraic spaces.

Fix a scheme `U` over an arbitrary scheme `S`, an actual fppf algebraic space
`R` over `S`, and transformations `s,t : R -> U` of their entire presheaves.
`relation R s t T x y` means that an actual section of `R` over `T` has
endpoints `x,y`. `IsEquivalenceRelation` requires that the endpoint pair is
injective on every section type and that this relation is reflexive,
symmetric and transitive on every scheme test. Thus it encodes a
monomorphic equivalence relation, including its unique arrow sections.
There is no restriction to reduced, affine, quasi-compact, or field tests.

`pointSetoid` packages precisely that relation. `relation_map` restricts an
actual arrow section and uses the naturality of its endpoints. These
restrictions define `quotientPresheaf`; its identity and composition laws
are proved by quotient induction and the functor laws of scheme Yoneda.
`toQuotientPresheaf` is the actual quotient-class map. `quotientSheaf` is
its etale sheafification on the full category `Over S`, and `quotientMap`
is the composite with the sheafification unit. Its sections include all
etale sheaf sections, with no global representative required.

`HasSmoothProjections` requires an actual scheme `W`, a representable
surjective etale atlas `b : W -> R`, and actual morphisms `s0,t0 : W -> U`.
The equalities with `b >> s` and `b >> t` are equalities of whole natural
transformations. Both actual scheme morphisms must be smooth. This
expresses smoothness of the two algebraic-space projections on a common
etale atlas; it assumes no quotient and supplies no geometric property of
the class sheaf.

## Exact outstanding theorem

`SmoothRelationQuotientStatement.{u}` quantifies over all these data in
universe `u`. Its only further assumption is that `U -> S` is locally of
finite type. For the fixed canonical etale quotient `Q`, it asserts:

1. `Q` satisfies fppf descent on the entire slice site.
2. Its diagonal is scheme-representable on every complete presheaf base
   change.
3. The square with `R` above `U`, whose two lower maps are the fixed
   `quotientMap`, is a pullback in actual presheaves. This is full
   effectiveness, including all arrow sections.
4. The fixed map `U -> Q` is scheme-representable, smooth and surjective
   on every represented scheme base change.
5. An actual scheme `V` over `S` admits a representable surjective etale
   transformation to `Q`, and `V -> S` is locally of finite type.

These conclusions construct the geometric quotient; none is part of the
hypotheses. Accepting this proposition as a statement supplies no proof of
them and cannot discharge the Picard theorem. Any use of this quotient
result as a theorem requires its independently accepted Library proof.
