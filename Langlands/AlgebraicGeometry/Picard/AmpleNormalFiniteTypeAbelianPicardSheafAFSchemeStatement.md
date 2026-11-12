# The Picard sheaf of a projective abelian scheme over a normal finite-type integer domain is an AF scheme

Authors: Worker 3570.

Worker 3570 wrote the Lean file, checked the cited source pages and wrote this
description, as part of the decomposition of
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement` agreed with Worker 5067
in proof task `de799868-75c2-4835-b620-f024e5969aa8` (Task 5600).

## Statement

`Langlands.AlgebraicGeometry.Picard.AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}`
is a proposition with the single universe parameter `u`. Its body is

```lean
∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Algebra.FiniteType ℤ R]
  (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
  (∃ L : LineBundle A.X.left, L.IsAmple) →
    ∃ P : Over (Spec (CommRingCat.of R)),
      PointTopology.HasFiniteAffineNeighborhoods P.left ∧
        Nonempty ((RelativePicard.classSheafPresheaf A.X.hom).RepresentableBy P)
```

Write `S` for `Spec (CommRingCat.of R)` and
`F = RelativePicard.classSheafPresheaf A.X.hom`. The proposition quantifies
over every integrally closed domain `R : Type u` of finite type over `ℤ` and
every Library abelian scheme `A` over `S`. If the total space `A.X.left`
carries an ample line bundle (`LineBundle.IsAmple`, from
`Langlands.AlgebraicGeometry.Picard.Ample`), then there is an object `P` of
`Over S` such that

1. every finite set of points of the scheme `P.left` is contained in one
   affine open subscheme
   (`Langlands.AlgebraicGeometry.PointTopology.HasFiniteAffineNeighborhoods`,
   that is `∀ s : Set X, s.Finite → ∃ U : X.affineOpens, s ⊆ U.val`), and
2. `F` is represented by `P` in the sense of Mathlib's
   `Functor.RepresentableBy`: bijections `(T ⟶ P) ≃ F.obj (op T)` for every
   `T : Over S`, natural in `T`.

The conclusion is exactly that of
`Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`;
the only difference is the additional premise that an ample line bundle
exists. Since `S` is affine and `A` is proper over `S`, this premise says that
`A` is projective over `S`.

`F` is the underlying presheaf of the Library sheaf
`RelativePicard.classSheaf A.X.hom`: Mathlib's sheafification, for
`Scheme.fppfTopology.over S` and in `Type (u+1)`, of the presheaf of
isomorphism classes of actual line bundles on `T ×_S A`. Test objects range
over the whole slice `Over S`. Apart from conjunct 1, nothing is required of
`P`. No group structure on `P`, universal bundle, decomposition into projective
pieces or property of `A` other than the premise is asserted. The proposition
proves nothing; it is a statement definition only.

## Provenance

This is a derived specialization of the published argument; no source states
this exact Lean proposition.

G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990),
registered source
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`,
Chapter I §1:

- Remark 1.5(a), printed p.2 (PDF p.14): `Pic(X/S)` is the fppf sheaf
  associated to `T/S ↦ Pic(X ×_S T)`; `RelativePicard.classSheaf A.X.hom`
  formalizes it as a sheaf of sets.
- Printed p.3 (PDF p.15), case (b): when `A` is locally projective over the
  base, `A^t` is a scheme "by Hilbert schemes", and "in all three cases above
  `Pic(A/B)` is also a scheme".
- Theorem 1.9(b), printed p.5 (PDF p.17): any finite set of points in
  `Pic(A/S)` over an affine open subset of `S` is contained in an open affine
  subscheme.
- Proof of Theorem 1.9, printed p.6 bottom to p.7 top (PDF pp.18–19): once
  `A_T̃` is a projective abelian scheme over the normalization `T̃` of an
  irreducible component, "By Grothendieck's theory of Hilbert schemes,
  `Pic(A/S)_T̃` is also a scheme which is a union of open and closed projective
  schemes. Clearly any finite set of points in either `A_T̃` or `Pic(A/S)_T̃`
  is contained in an affine open subscheme."

D. Mumford, J. Fogarty and F. Kirwan, *Geometric Invariant Theory*, 3rd
edition (1994), registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`:

- Chapter 0, §5(d), printed pp.22–23 (PDF pp.35–36): for a flat projective
  morphism `X → T` over a locally Noetherian base whose geometric fibres are
  varieties and which has a section, Grothendieck's existence theorem gives a
  group scheme `Pic_{X/T}` representing the functor of normalized invertible
  sheaves; it is the disjoint union of open and closed pieces indexed by
  Hilbert polynomials.
- Chapter 6, §1, printed p.117 (PDF p.130): for a projective abelian scheme
  `X → S`, "it is known that `Pic(X/S)` exists in this case (cf. Ch. 0, §5,
  (d))".

Here `S = Spec R` is an irreducible normal Noetherian scheme, equal to its own
normalization, and the premise makes `A` projective over `S`; this is the
situation of the quoted step of Faltings–Chai with `T̃ = S`. The finite-set
property is Theorem 1.9(b) for the affine base `S`, written as conjunct 1.
The source's decomposition of `P` into open and closed projective pieces is not
stated; it implies conjunct 1 because a finite set of points meets only
finitely many pieces, and a scheme projective over an affine scheme has the
finite-set property. Worker 3570 read the cited pages of both registered PDFs.
No source-specific errata note was found in the Library's `notes/errata/`
directory.

## Future proof obligations

A proof must construct, for every `R`, `A` and ample `L`, an actual `P` with
the finite-set property and a natural bijection with the exact Library presheaf
`F` on all test objects. Following the sources this requires the existence of
the Picard scheme of a projective abelian scheme (Hilbert schemes, or another
correct argument), the comparison between the source's normalized or
fppf-sheafified Picard functor and `RelativePicard.classSheaf A.X.hom`, and the
finite-set property. None of these is a premise of the proposition.

## Use

`Langlands.AlgebraicGeometry.Picard.normalFiniteTypeAbelianPicardSheafAFScheme_of_ample`,
in `NormalFiniteTypeAbelianPicardSheafAFSchemeReduction`, combines this
proposition with `NormalFiniteTypeAbelianAmpleExistenceStatement` to obtain
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`.
