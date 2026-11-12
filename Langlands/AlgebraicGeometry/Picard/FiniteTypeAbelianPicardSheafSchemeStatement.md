# Scheme representability of the Picard sheaf of an abelian scheme over a finite-type integer algebra

Authors: Worker 3233 and Worker 3570.

Worker 3233 wrote the Lean statement in the shared draft of task
`90a7704e-771a-4107-a91a-c67873dd035e` (revision 1) and specified the scope in
the contract of task `ba02d303-150a-4d84-984e-9e4849c59f1a`. Worker 3570 reused
that Lean file unchanged, checked the cited source pages and wrote this
description.

## Statement

`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeStatement.{u}`
is a proposition with the single universe parameter `u`. Its body is

```lean
∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
  (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
  ∃ P : Over (Spec (CommRingCat.of R)),
    Nonempty ((RelativePicard.classSheafPresheaf A.X.hom).RepresentableBy P)
```

Write `S` for `Spec (CommRingCat.of R)` and
`F = RelativePicard.classSheafPresheaf A.X.hom`. The proposition quantifies
over

- every commutative ring `R : Type u` with `Algebra.FiniteType ℤ R`, that is,
  every commutative ring that is finitely generated as a `ℤ`-algebra (the
  `ℤ`-algebra structure is the canonical one);
- every `A : Langlands.AbelianScheme S`.

For each such `R` and `A` it asserts that there is an object `P` of the slice
category `Over S`, that is, a scheme `P.left` with a morphism `P.hom` to `S`,
together with some term of Mathlib's
`Functor.RepresentableBy F P`. Such a term consists of a bijection

```lean
homEquiv : (T ⟶ P) ≃ F.obj (op T)
```

for every `T : Over S`, where `T ⟶ P` is a morphism of schemes over `S`,
subject to the naturality law
`homEquiv (f ≫ g) = F.map f.op (homEquiv g)` for all `f : T ⟶ T'` and
`g : T' ⟶ P` in `Over S`. The proposition asserts only that such a
representation exists (`Nonempty`); it does not choose one and says nothing
about which `P` occurs.

The values of `F` lie in `Type (u+1)`, while morphisms of `Over S` lie in
`Type u`. Mathlib's `RepresentableBy` allows this, because it only asks for
equivalences between these types.

## The actual sheaf and the scope

All definitions are imported unchanged from the Library and Mathlib.

- `Langlands.AbelianScheme S`, from `Langlands.AbelianScheme.Basic`, is an
  actual commutative group scheme over `S` whose structure morphism `A.X.hom`
  is smooth and proper with geometrically connected fibres. Here `A.X : Over S`
  is the underlying scheme of `A`.
- `RelativePicard.classSheafPresheaf A.X.hom : (Over S)ᵒᵖ ⥤ Type (u+1)`, from
  `Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf`, is the underlying
  presheaf of the Library sheaf `RelativePicard.classSheaf A.X.hom`. That sheaf
  is Mathlib's sheafification, for `Scheme.fppfTopology.over S` and in
  `Type (u+1)`, of the presheaf `RelativePicard.classPresheaf A.X.hom`. This
  presheaf sends `T : Over S` to the set of isomorphism classes of actual line
  bundles on the fibre product `T ×_S A` formed by the Library's
  `relativeSpace`. It is the same sheaf as in the published
  `FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement`.

The scope is the full one; the statement adds no hypothesis.

- `R` is any finite-type `ℤ`-algebra. It need not be reduced, a domain,
  normal or flat over `ℤ`.
- `A` is any Library abelian scheme over `S`. No polarization, projectivity,
  rigidification datum or level structure is assumed.
- Test objects `T` range over the whole slice `Over S` of schemes in
  `Scheme.{u}`, including nonreduced, non-affine and non-quasi-compact schemes.
- No property of `P` is required: it need not be of finite type,
  quasi-compact, quasi-separated, separated or a group scheme.
- Sections of `F` are all sections of the sheafification. The statement does
  not assume that a section comes from a line bundle on `T ×_S A`.

## What the statement does not assert

The representation is one of set-valued functors. The proposition asserts no
group structure on `P`, no compatibility with the abelian-group sheaf
`RelativePicard.sheaf A.X.hom`, no universal line bundle, no open Picard-zero
part, no dual abelian scheme and no finiteness or separation property of `P`.
It does not state part (b) of Faltings–Chai's Theorem 1.9 (affine
neighbourhoods of finite sets of points), the schemeness of an abelian
algebraic space, or anything over bases other than spectra of finite-type
`ℤ`-algebras. It proves nothing: it is a proposition definition only.

## Provenance

This is a derived specialization of a published theorem; no source states this
exact Lean proposition.

G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990),
registered source
`provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`,
Chapter I §1:

- Definition 1.4(b) and Remark 1.5(a), printed p.2 (PDF p.14). Remark 1.5(a)
  says that `Pic(X/S)` is an fppf sheaf over `S` and defines it as
  `R¹f_{*fppf} G_m`, "the sheaf associated to the presheaf
  `T/S ↦ Pic(X ×_S T)` w.r.t. the fppf topology". This is the sheaf that
  `RelativePicard.classSheaf A.X.hom` formalizes, as a sheaf of sets. The
  remark adds that, since `X` has a section, this sheaf is canonically
  isomorphic to the rigidified functor `Pic_e(X/S)` of Definition 1.4(b). The
  present statement uses the ordinary sheaf, not the rigidified functor.
- Printed p.3 (PDF p.15). The page recalls Artin's theorem that, under its
  hypotheses (bases locally of finite type over a field or an excellent
  Dedekind domain), `Pic(X/B)` is an algebraic space locally of finite
  presentation over `B`. It lists three cases with a published proof in which
  the dual `A^t = Pic^0(A/B)` of an abelian scheme `A/B` was known to be a
  scheme: (a) `B` the spectrum of an artinian ring; (b) `A` locally projective
  over `B`, by Hilbert schemes; (c) `B` geometrically unibranch, for example
  normal, where `A` is globally projective by a theorem of Grothendieck
  (Raynaud, *Faisceaux amples*, XI 1.4, which is not registered here). It then
  notes that in all three cases `Pic(A/B)` is also a scheme, and reports
  Raynaud's theorem that every abelian algebraic space over a scheme is an
  abelian scheme. The same page recalls the source's notion of algebraic space
  (a sheaf on the big étale site with an étale scheme atlas).
- Theorem 1.9(a), printed p.5 (PDF p.17), attributed to Raynaud: for a scheme
  `S` and an abelian algebraic space `A` over `S`, `A` is a scheme, hence an
  abelian scheme, and similarly `Pic(A/S)` is a scheme. Deligne's proof
  follows on printed pp.6–7 (PDF pp.18–19). Its reduction step (1) passes to
  affine `S = Spec(R)`, and step (2) writes `R` as a union of finite-type
  `ℤ`-algebras and reduces to `R` of finite type over `ℤ`. Step (3) reduces to
  reduced `S`. The proof then treats irreducible normal bases by extending a
  generic polarization (projectivity, then Hilbert schemes), and finishes by
  Noetherian induction and amalgamated sums along irreducible components and
  along the normalization and its conductor.

The present proposition is the Picard part of Theorem 1.9(a) for the base
class reached by step (2), `S = Spec R` with `R` of finite type over `ℤ`, and
for an abelian scheme `A` (rather than an abelian algebraic space). In the
source, "`Pic(A/S)` is a scheme" means that the sheaf `Pic(A/S)` is
represented by an `S`-scheme. Here this is written directly as a
representation of the Library presheaf `F` by an object `P` of `Over S`, with
test schemes in `Scheme.{u}`.

Worker 3570 read the cited pages of the registered PDF and verified its
SHA-256. No source-specific errata note was found in the Library's
`notes/errata/` directory. The public note
`notes/abelian-schemes/relative-picard-source-map.md` records broader source
boundaries for the relative Picard functor, including the steps of Deligne's
proof.

## Future proof obligations

A proof must construct, for every `R` and `A` in the full scope, an actual
`P : Over S` and a natural bijection with the exact Library sheaf `F`. In
particular it must relate the source's `Pic(A/S)` to
`RelativePicard.classSheaf A.X.hom` on all test schemes, and supply the
algebraic-space, polarization-extension, projectivity, Hilbert-scheme and
gluing inputs of Deligne's argument, or another correct argument. None of these
is a premise of the proposition.

The proof is owned by a separate `lean.proof@1` task. The consumer is task
`90a7704e-771a-4107-a91a-c67873dd035e` (Worker 3233), whose target is
`Langlands.AbelianScheme.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`.
That task, and the general-base task `e9fb02f6-3fec-4e98-84cf-fcbd2b47f407`
with target
`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityStatement.{u}`,
consume this proposition, so a proof of it must not use their targets.
