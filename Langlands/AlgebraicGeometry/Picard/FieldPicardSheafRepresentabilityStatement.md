# Scheme representability of the fppf Picard sheaf over a field

`Langlands.AlgebraicGeometry.Picard.FieldPicardSheafRepresentabilityStatement.{u}`
states that for every field `k : Type u` and every scheme
`X : Over (Spec (CommRingCat.of k))`, properness of `X.hom` implies
existence of a scheme `P` over the same field with:

- `IsSeparated P.hom`;
- `LocallyOfFiniteType P.hom`;
- a natural representation of
  `RelativePicard.classSheafPresheaf X.hom` by `P`.

The imported functor is the underlying set-valued presheaf of the actual
fppf Picard class sheaf. Its published definition sheafifies the ordinary
relative presheaf of actual line-bundle isomorphism classes on
`T ×_k X`, on `Scheme.fppfTopology.over (Spec (CommRingCat.of k))`.
The published `RelativePicard.forgetSheafIso` identifies it naturally
with the underlying set-valued presheaf of the abelian-group-valued
Picard sheaf, compatibly with the sheafification units. Thus the target
is the actual relative Picard sheaf of the source definition.
The parameter-first fibre product agrees with `X ×_k T` through the
published `relativeSpaceSymmetry`.

The last conjunct is
`Nonempty ((RelativePicard.classSheafPresheaf X.hom).RepresentableBy P)`.
For every test scheme `T` over `k`, an inhabitant supplies a bijection
from the actual morphisms `T ⟶ P` in the slice category to all sections
of the sheaf on `T`. For any morphism `h : T ⟶ U` of test schemes and
any `g : U ⟶ P`, the bijection sends `h ≫ g` to the restriction along
`h` of the section classified by `g`. This is the naturality field in
Mathlib's `Functor.RepresentableBy`. In particular, the quantification
is over all test schemes and all sheaf sections, including sections
that need not have a global line-bundle representative.
The sheaf takes values in `Type (u+1)`; `RepresentableBy` permits the
category and value universes to differ, so no smallness hypothesis or
universe reduction is introduced.

The sole geometric hypothesis is properness over the spectrum of an
arbitrary field, including imperfect fields. The representing object
is an actual scheme. The statement adds no projectivity, smoothness,
reducedness, connectedness, rational point, chosen section, group
structure, dual, universal bundle, or representability hypothesis.
It claims separatedness and local finite type, without asserting
quasi-compactness or finite type of the full representing scheme.

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, Chapter VI §1: Definition (6.1), printed p.87
(PDF p.91), specifies the associated fppf Picard sheaf; paragraph
(6.3)(iii), printed p.89 (PDF p.93), asserts exactly this scheme
representability, separatedness and local finite type for a proper
scheme over a field. Paragraph (6.3) returns to the general case
without the additional assumptions used in (6.2). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Worker 368 read PDF pp.91–93 directly and verified the fingerprint.
The source cites Murre and Oort for this representability result.
The `RepresentableBy` formulation is its internal categorical
packaging, using the published actual Picard presheaf and sheaf.

This file defines the proposition; it supplies no proof of the
representability theorem. A separate proof task must prove this exact
published proposition.
