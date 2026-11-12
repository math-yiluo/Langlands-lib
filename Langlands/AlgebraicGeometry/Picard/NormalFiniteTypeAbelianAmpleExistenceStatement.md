# Ample line bundles on abelian schemes over a normal finite-type integer domain

Authors: Worker 3570.

Worker 3570 wrote the Lean file, checked the cited source pages and wrote this
description, as part of the decomposition of
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement` agreed with Worker 5067
in proof task `de799868-75c2-4835-b620-f024e5969aa8` (Task 5600).

## Statement

`Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianAmpleExistenceStatement.{u}`
is a proposition with the single universe parameter `u`. Its body is

```lean
∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Algebra.FiniteType ℤ R]
  (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
  ∃ L : LineBundle A.X.left, L.IsAmple
```

It quantifies over every commutative ring `R : Type u` that is an integral
domain, integrally closed in its field of fractions (Mathlib's
`IsIntegrallyClosed R`) and finitely generated as a `ℤ`-algebra, and over every
Library abelian scheme `A` over `S = Spec (CommRingCat.of R)`. It asserts that
the total space `A.X.left` carries some line bundle `L` that is ample.

- `Langlands.AbelianScheme S`, from `Langlands.AbelianScheme.Basic`, is a
  commutative group scheme over `S` whose structure morphism is smooth and
  proper with geometrically connected fibres. No polarization or projectivity
  is part of the data.
- `LineBundle A.X.left` is the Library's type of line bundles (locally free
  modules of rank one) on the scheme `A.X.left`, from
  `Langlands.AlgebraicGeometry.Picard.LineBundle`.
- `L.IsAmple`, from `Langlands.AlgebraicGeometry.Picard.Ample`, means that
  `A.X.left` is quasi-compact and every point lies in the generation locus of
  a global section of some positive tensor power of `L` whose locus is an
  affine open. This is the absolute notion of ampleness (EGA II 4.5).

Since `S` is affine, an ample line bundle on `A.X.left` is the same as a line
bundle that is ample relative to `A.X.hom` (EGA II 4.6.6), and, `A` being
proper over `S`, its existence is the statement that `A` is projective over
`S`. The Lean statement only asserts the existence of an ample line bundle; it
does not mention relative ampleness, a projective embedding or a polarization
of `A`.

## Scope

`R` ranges over all integrally closed finite-type `ℤ`-domains: for example
`ℤ`, rings of integers of number fields, polynomial rings over them and over
finite fields, and finite fields. `A` ranges over all Library abelian schemes
over `Spec R`. Nothing else is assumed. The proposition proves nothing; it is
a statement definition only.

## Provenance

This is a derived specialization of a published theorem; no source states this
exact Lean proposition.

G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990),
registered source
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`,
Chapter I §1:

- Proof of Theorem 1.9, printed p.6 (PDF p.18): "Let us first assume that `S`
  is irreducible and normal (in fact, geometrically unibranch is enough). We
  claim that `A` is (globally) projective over `S`." The proof extends a
  polarization of the generic fibre to a homomorphism `h : A → A^t` (step (a),
  using the scheme `Corr_S(A)`) and shows that the pull-back of the Poincaré
  sheaf along `(id_A, h)` is relatively ample (step (b), using the theorem of
  the cube, Riemann–Roch for abelian varieties and semicontinuity).
- Remark 1.10(a), printed p.7 (PDF p.19): "any abelian algebraic space over a
  noetherian normal scheme `S` is in fact a (globally) projective abelian
  scheme over `S`."
- Printed p.3 (PDF p.15), case (c), attributes the projectivity of abelian
  schemes over geometrically unibranch, for example normal, bases to
  Grothendieck (Raynaud, *Faisceaux amples sur les schémas en groupes et les
  espaces homogènes*, LNM 119, XI 1.4). The complete book is registered as
  `provided-5d5546c6572c2556d06cb8181d9d78944bca00a4138a3ab39df0a5810f0fd485`
  under the Chapter IV catalogue title; its SHA-256 is
  `29bce9a9be67396fd1bd8f0396e57d5ff08325eed53819e240eb14155711f38d`.
  XI 1.4 is on printed p.161 (PDF p.165).

For `R` an integrally closed Noetherian domain, `S = Spec R` is an irreducible
normal Noetherian scheme, so the source applies. A Library abelian scheme is in
particular an abelian algebraic space in the source's sense. The source's
"globally projective over `S`" is expressed for the affine base `S` by the
existence of an ample line bundle on the total space, as explained above.
Worker 3570 read the cited pages of the registered PDF. No source-specific
errata note was found in the Library's `notes/errata/` directory.

## Related Library statements

The Library contains statements about ample line bundles on abelian schemes
with narrower or different scope, among them
`Langlands.GroupScheme.FieldAmpleExistenceStatement` (over a field),
`Langlands.AbelianScheme.ValuationRingAmpleExtensionStatement` (generic
ampleness over a valuation ring) and
`Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingStatement`
(spreading ampleness from one fibre to an affine neighbourhood). None of them is
a premise of the present proposition.

## Use

`Langlands.AlgebraicGeometry.Picard.normalFiniteTypeAbelianPicardSheafAFScheme_of_ample`,
in `NormalFiniteTypeAbelianPicardSheafAFSchemeReduction`, combines this
proposition with
`AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement` to obtain
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`, an input of the proof of
`FiniteTypeAbelianPicardSheafSchemeStatement` planned in task
`de799868-75c2-4835-b620-f024e5969aa8`.
