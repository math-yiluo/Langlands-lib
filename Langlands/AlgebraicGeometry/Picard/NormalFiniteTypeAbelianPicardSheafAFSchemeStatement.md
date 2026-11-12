# The Picard sheaf of an abelian scheme over a normal finite-type integer domain is an AF scheme

Authors: Worker 3570 and Worker 5067.

Worker 5067 proposed this statement and its exact Lean form in the plan for
proof task `de799868-75c2-4835-b620-f024e5969aa8` (Task 5600). Worker 3570
wrote the Lean file, checked the cited source pages and wrote this description.

## Statement

`Langlands.AlgebraicGeometry.Picard.NormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}`
is a proposition with the single universe parameter `u`. Its body is

```lean
∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Algebra.FiniteType ℤ R]
  (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
  ∃ P : Over (Spec (CommRingCat.of R)),
    PointTopology.HasFiniteAffineNeighborhoods P.left ∧
      Nonempty ((RelativePicard.classSheafPresheaf A.X.hom).RepresentableBy P)
```

Write `S` for `Spec (CommRingCat.of R)` and
`F = RelativePicard.classSheafPresheaf A.X.hom`. The proposition quantifies
over

- every commutative ring `R : Type u` that is an integral domain
  (`IsDomain R`), is integrally closed in its field of fractions
  (Mathlib's `IsIntegrallyClosed R`) and is finitely generated as a
  `ℤ`-algebra (`Algebra.FiniteType ℤ R`, for the canonical `ℤ`-algebra
  structure);
- every `A : Langlands.AbelianScheme S`.

For each such `R` and `A` it asserts that there is an object `P` of the slice
category `Over S`, that is, a scheme `P.left` with a morphism `P.hom` to `S`,
such that

1. `PointTopology.HasFiniteAffineNeighborhoods P.left` holds: every finite set
   of points of the underlying topological space of `P.left` is contained in
   one affine open subscheme of `P.left`. This is the Library definition
   `Langlands.AlgebraicGeometry.PointTopology.HasFiniteAffineNeighborhoods`
   from `PointTopology/AffineChartWeilRestrictionRepresentability`, namely
   `∀ s : Set X, s.Finite → ∃ U : X.affineOpens, s ⊆ U.val`;
2. there is some term of Mathlib's `Functor.RepresentableBy F P`. Such a term
   consists of a bijection `homEquiv : (T ⟶ P) ≃ F.obj (op T)` for every
   `T : Over S`, where `T ⟶ P` is a morphism of schemes over `S`, subject to
   the naturality law `homEquiv (f ≫ g) = F.map f.op (homEquiv g)`.

Both conjuncts refer to the same `P`. The proposition asserts only that such a
`P` and a representation exist; it chooses neither.

As in the published
`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeStatement`,
the values of `F` lie in `Type (u+1)` while morphisms of `Over S` lie in
`Type u`; Mathlib's `RepresentableBy` only asks for equivalences between these
types.

## The actual sheaf and the scope

All definitions are imported unchanged from the Library and Mathlib.

- `Langlands.AbelianScheme S`, from `Langlands.AbelianScheme.Basic`, is an
  actual commutative group scheme over `S` whose structure morphism `A.X.hom`
  is smooth and proper with geometrically connected fibres; `A.X : Over S` is
  its underlying scheme.
- `RelativePicard.classSheafPresheaf A.X.hom : (Over S)ᵒᵖ ⥤ Type (u+1)`, from
  `Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf`, is the underlying
  presheaf of the Library sheaf `RelativePicard.classSheaf A.X.hom`: Mathlib's
  sheafification, for `Scheme.fppfTopology.over S` and in `Type (u+1)`, of the
  presheaf sending `T : Over S` to the set of isomorphism classes of actual
  line bundles on the fibre product `T ×_S A` formed by `relativeSpace`. It is
  the same presheaf as in `FiniteTypeAbelianPicardSheafSchemeStatement` and in
  `FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement`.

Within the stated base class the scope is full.

- `R` is any integrally closed domain of finite type over `ℤ`, of any
  dimension and characteristic; for example `ℤ`, rings of integers of number
  fields, polynomial rings over them and over finite fields, and finite fields.
  Since `R` is Noetherian, `S` is a normal integral Noetherian scheme.
- `A` is any Library abelian scheme over `S`. No polarization, projectivity,
  rigidification datum or level structure is assumed.
- Test objects `T` range over the whole slice `Over S`, including nonreduced,
  non-affine and non-quasi-compact schemes, and sections of `F` are all
  sections of the sheafification.
- Apart from conjunct 1, nothing is required of `P`: it need not be of finite
  type, quasi-compact, separated or a group scheme.

## What the statement does not assert

It asserts no group structure on `P`, no compatibility with the abelian-group
sheaf `RelativePicard.sheaf A.X.hom`, no universal line bundle, no
decomposition of `P` into open and closed projective pieces, no projectivity of
`A` and no statement about `A` itself. It says nothing about bases that are not
normal domains; the general finite-type case is the published
`FiniteTypeAbelianPicardSheafSchemeStatement`. It proves nothing: it is a
proposition definition only.

## Provenance

This is a derived specialization of the proof of a published theorem; no
source states this exact Lean proposition.

G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990),
registered source
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`,
Chapter I §1:

- Remark 1.5(a), printed p.2 (PDF p.14), defines `Pic(X/S)` as the fppf sheaf
  associated to `T/S ↦ Pic(X ×_S T)`. This is the sheaf that
  `RelativePicard.classSheaf A.X.hom` formalizes as a sheaf of sets.
- Theorem 1.9 (Raynaud), printed p.5 (PDF p.17): for a scheme `S` and an
  abelian algebraic space `A` over `S`, (a) `A` is a scheme and `Pic(A/S)` is a
  scheme; (b) any finite set of points in `A` or in `Pic(A/S)` over an affine
  open subset of `S` is contained in an open affine subscheme.
- Deligne's proof, printed pp.6–7 (PDF pp.18–19). After reducing to `S`
  affine and of finite type over `ℤ`, it first assumes that `S` is irreducible
  and normal, and shows that `A` is then globally projective over `S`, by
  extending a polarization of the generic fibre: (a) the generic homomorphism
  `A_η → A^t_η` extends, using the scheme `Corr_S(A)`, unramified and
  satisfying the valuative criterion; (b) the pulled-back Poincaré sheaf is
  relatively ample, by Riemann–Roch for abelian varieties and semicontinuity.
  The proof concludes (printed p.6 bottom to p.7 top): for the normalization
  `T̃` of an irreducible component `T` of `S`, `A_T̃` is a projective abelian
  scheme; "By Grothendieck's theory of Hilbert schemes, `Pic(A/S)_T̃` is also
  a scheme which is a union of open and closed projective schemes. Clearly any
  finite set of points in either `A_T̃` or `Pic(A/S)_T̃` is contained in an
  affine open subscheme." The remaining Noetherian induction and amalgamated
  sums over irreducible components and the conductor of the normalization
  are not part of this statement.
- Remark 1.10(a), printed p.7 (PDF p.19): any abelian algebraic space over a
  Noetherian normal scheme is a globally projective abelian scheme.

The present proposition is the normal case of this argument for
`S = Spec R` with `R` an integrally closed domain of finite type over `ℤ`.
Such an `S` is irreducible, normal and equal to its own normalization, so the
quoted conclusion applies with `T̃ = T = S`. Here `A` is a Library abelian
scheme rather than an abelian algebraic space, "`Pic(A/S)` is a scheme" is
written as a representation of the Library presheaf `F` by `P : Over S`, and
the finite-set property of Theorem 1.9(b) for `Pic(A/S)` over the affine base
`S` is written as `HasFiniteAffineNeighborhoods P.left`. The source's stronger
description of `P` as a union of open and closed projective `S`-schemes is not
stated; it implies conjunct 1 because a finite set of points meets only
finitely many of these pieces, and a scheme projective over an affine scheme
has the finite-set property.

Worker 3570 read the cited pages of the registered PDF. Raynaud's *Faisceaux
amples sur les schémas en groupes* (XI 1.4), cited by the source for global
projectivity, is not registered in this project. No source-specific errata note
was found in the Library's `notes/errata/` directory.

## Use

The proof of `FiniteTypeAbelianPicardSheafSchemeStatement` planned in task
`de799868-75c2-4835-b620-f024e5969aa8` uses this proposition for the
normalizations of the reduced irreducible components of a finite-type base,
together with the published algebraic-space statement
`FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement` and the published
descent theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentOpenCharts.exists_representation`
along finite surjective morphisms from schemes with the finite-set property.
Conjunct 1 is the hypothesis that this descent needs.

## Future proof obligations

A proof must construct, for every `R` and `A` in the scope above, an actual
`P : Over S` with the finite-set property and a natural bijection with the
exact Library presheaf `F`. Following the source, it must supply global
projectivity of `A` over a normal base (extension of a generic polarization)
and Grothendieck's representability of the Picard functor of a projective
scheme by Hilbert schemes, or another correct argument, together with the
comparison between the source's `Pic(A/S)` and
`RelativePicard.classSheaf A.X.hom` on all test schemes. None of these is a
premise of the proposition.
