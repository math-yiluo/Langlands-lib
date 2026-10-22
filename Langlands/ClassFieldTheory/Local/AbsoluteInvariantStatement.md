# Existence of absolute local invariants compatible with restriction

Author: Worker 80.

`AbsoluteInvariantExistence.{u}` asserts that, for every prime `p`, there is
one family of additive isomorphisms

`inv F : absoluteCohomology F.Carrier 2 ≃+ RationalModIntegers`

for all `F : PadicField.{u} p`. For every compatible finite extension
`E/F`, the family satisfies

`inv E (absoluteRestriction F.Carrier E.Carrier 2 x) = [E:F] • inv F x`.

Here `[E:F]` is `Module.finrank F.Carrier E.Carrier`. The cohomology is the
existing continuous cohomology of the absolute Galois group with the
actual algebraic-closure units as discrete coefficients. The target is
the existing additive quotient of the rationals by the integers. The
restriction map is the existing map on these cohomology groups, induced
by the map of absolute Galois groups and inclusion of closure units.

The extension algebras respect the specified p-adic structures, as
expressed by `IsScalarTower (Padic p) F.Carrier E.Carrier`. The extra
algebra on the two closures and its `F.Carrier` scalar-tower certificate
specify any `F.Carrier`-compatible embedding of those closures. These
binders are precisely those of `InvariantFamily.AbsoluteRestriction`.
No additional agreement with the canonical embedding of `E.Carrier`
into its closure is required. The law holds for every such choice of
closure embedding. The finite extension need not be Galois.

This is an existence target, not a proof or a selected invariant family.
It isolates the absolute part of the existing invariant-family
predicates: equivalences package bijectivity, and the same restriction
law is imposed directly without introducing unused relative maps.
It asserts neither the arithmetic normalization on cyclic classes nor
uniqueness of the family. The fields and their closures share the
arbitrary universe `u`, matching the absolute restriction API. Relative
invariants for independent field universes remain a separate obligation
of `CohomologyExistence.{u,v}`.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, Greenberg English translation, Springer
GTM 67 (1979), Chapter XIII, section 3, Propositions 6 and 7, printed
pages 193–194 / PDF pages 198–199. Registered source:
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 80 read these original pages and the supporting Chapter X,
sections 3–4, printed pages 154–156 / PDF pages 160–162. No project
errata entry for this source was present when checked.

Serre's field `K` is `F.Carrier`, and his finite extension `L` is
`E.Carrier`. Proposition 6 says that the absolute invariant is an
isomorphism to `Q/Z`. Proposition 7 gives the multiplication-by-degree
restriction formula, first for unramified and totally ramified
extensions and then for a general finite extension. These canonical
maps supply the simultaneous family whose existence is asserted here;
the target does not retain their explicit normalization formula.

Serre defines the Brauer group as absolute degree-two Galois cohomology
in X.4. Section X.3 gives its continuous-cochain description. Proposition
5 of X.4 establishes independence of the base-field-compatible closure
embedding, supporting the universal closure-embedding quantifier here.
P-adic fields satisfy the complete discretely valued and finite residue
field hypotheses of XIII.3. A proof must establish the invariant and
these properties for the imported cohomology objects and maps; no
unproved identification with a central-simple-algebra model is assumed.
