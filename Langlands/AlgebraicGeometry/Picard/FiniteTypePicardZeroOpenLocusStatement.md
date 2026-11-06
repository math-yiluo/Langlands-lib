# Geometric Picard-zero openness over finite-type integer algebras

`Langlands.AbelianScheme.FiniteTypePicardZeroOpenLocusStatement.{u}`, in the
module `Langlands.AlgebraicGeometry.Picard.FiniteTypePicardZeroOpenLocusStatement`,
is a proposition definition. It is the following statement:

```lean
∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
  (A : AbelianScheme (Spec (CommRingCat.of R)))
  (P : Over (Spec (CommRingCat.of R)))
  (L : RigidifiedFamily A P),
  ∃ U : P.left.Opens, IsPicardZeroOpenLocus A L U
```

The `ℤ`-algebra structure on `R` is Mathlib's canonical instance
`Ring.toIntAlgebra`, so `Algebra.FiniteType ℤ R` says that `R` is a quotient of a polynomial ring in
finitely many variables over `ℤ`. The file imports only
`Langlands.AlgebraicGeometry.Picard.OpenLocus` and
`Mathlib.RingTheory.FiniteType`, and it defines no new geometric notion.

## Meaning of the open-locus predicate

`IsPicardZeroOpenLocus` is the existing predicate from
[`OpenLocus`](OpenLocus.md). It is defined over an arbitrary base and makes no
existence assertion. Here `S = Spec R`, and `U` satisfies it when the
following holds for every test `T : Over (Spec R)` and every morphism
`h : T ⟶ P` over `Spec R`:

```text
IsPicardZeroClass A
  (RigidifiedLineBundle.classifyingMap A.X.hom
    (unitSection A) (unitSection_comp A) L T h)
  ↔ Set.range h.left ⊆ (U : Set P.left).
```

- The classifier is the class of the actual rigidified relative pullback of
  `L` along `h`. By the published `isPicardZeroOpenLocus_iff`, the left side is
  `IsPicardZeroFamily A` of
  `(RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
  (unitSection_comp A) h).obj L`.
- `IsPicardZeroFamily` ([`RelativePicardZero`](RelativePicardZero.md)) moves
  the underlying bundle from `T ×_S A` to the chosen total space of
  `(baseChange T.hom).obj A`, which is `A ×_S T`. It then applies
  `IsGeometricallyPicardZero` ([`GeometricPicardZero`](GeometricPicardZero.md)).
  That predicate asks the following for every algebraically closed field
  `K : Type u` and every morphism `Spec K ⟶ T.left`: the line bundle restricted
  to the base-changed abelian scheme over `Spec K` must be isomorphic to its
  pullback under translation by every `K`-section. This is the Library's
  geometric-fibre translation-invariance convention. The statement uses that
  predicate unchanged and does not redefine it through algebraic equivalence
  or connected components.
- The right side says that `h` lands in `U`. By the published
  `existsUnique_openLocusLift_iff`, this holds exactly when `h` factors uniquely
  through the actual open subscheme `openLocusParameter P U`.

So the statement asserts the following. Pulling back the given family
defines a subfunctor of the functor of points of `P` over `Spec R`, namely the
tests whose pullback is geometrically Picard-zero. This subfunctor is
represented by an open subscheme of `P`.

## Exact scope

- Every commutative ring `R : Type u` of finite type over `ℤ` is allowed, with
  no reducedness, normality or connectedness premise.
- Every `A : AbelianScheme (Spec R)` is allowed, with no projectivity,
  polarization, existing-dual (`HasDualScheme`) or representer premise.
- The parameter `P : Over (Spec R)` is arbitrary. It need not be
  quasi-separated, locally of finite type or finitely presented over `Spec R`.
- The family `L : RigidifiedFamily A P` is any actual rigidified family on `P`.
  It is not assumed universal and need not come from an ambient Picard
  representer.
- The test quantifier inside `IsPicardZeroOpenLocus` ranges over all schemes
  `T` over `Spec R` and all morphisms `h`, including nonreduced and
  non-quasi-separated tests.
- No ordinary/geometric comparison, smooth-family comparison or open locus is
  supplied as input. The declaration is universe-polymorphic in `u`, and every
  object lives in that one universe.

Compared with the published
[`FieldPicardZeroOpenLocusStatement`](FieldPicardZeroOpenLocusStatement.md),
the base here is the spectrum of a finite-type `ℤ`-algebra rather than a field.
This statement also drops that statement's `LocallyOfFiniteType P.hom` and full
rigidified universality premises. The field statement is not a formal
specialization of this one, since a field is of finite type over `ℤ` only when
it is finite.

## Original sources and derived provenance

This is a derived specialization. No original source states this exact Lean
proposition. Both originals are registered and kept under the project
`literature/` directory. The SHA-256 hashes below were rechecked against the
retained files.

- G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties* (1990),
  source
  `provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`,
  SHA-256
  `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e`,
  file `Faltings-Chai - Degeneration of Abelian Varieties (1990).pdf`.
  - Chapter I, Definition 1.4, printed p.2 (PDF p.14), works with an abelian
    scheme `X/S` with unit section `e`. Part (a) defines a rigidification of an
    invertible sheaf as an isomorphism `O_S ≅ e^*ℒ`. Part (b) identifies
    `Pic(X/S)` with isomorphism classes of invertible sheaves on `X ×_S T`
    rigidified along `e_T`. Part (c) defines the subfunctor `Pic^0(X/S)` by
    requiring, for every point `t ∈ T`, that `ℒ ⊗ κ(t)` be algebraically
    equivalent to zero on `X_t`.
  - Remark 1.5(b), same page, asserts that `Pic^0(X/S)` is an open subfunctor
    of `Pic(X/S)`. The assertion is made over an arbitrary base `S` and before
    any representing space is introduced.
  - The digression on printed p.3 (PDF p.15) quotes Artin's algebraic-space
    representability, introduces the open subspace for `Pic^0`, and describes
    the dual abelian algebraic space and its Poincaré sheaf. These are further
    substantive inputs that the present statement does not use or assert.
- B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*,
  preliminary draft, source
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
  file `Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
  - Chapter VI §3, printed p.95 (PDF p.99), treats the rigidified Picard
    functor of an abelian variety over a field and the morphism
    `φ_L : X → Pic_{X/k}`, `x ↦ [t_x^*L ⊗ L^{-1}]`.
  - Theorem (6.18) and Definition (6.19), printed p.96 (PDF p.100), make
    `Pic^0_{X/k}` an abelian variety, the dual, with Poincaré bundle restricted
    from the ambient one.
  - Corollary (7.22), printed p.106 (PDF p.110), identifies `Pic^0_{X/k}` with
    the kernel of `φ : Pic_{X/k} → Hom(X, X^t)`. Its proof uses Proposition
    (7.21), printed p.105 (PDF p.109), over an algebraically closed field.

This kernel description over algebraically closed fields motivates the
Library's translation-invariance convention. It is a statement about a
field, not a relative openness theorem for arbitrary families or all test
schemes. Faltings–Chai Remark 1.5(b) is the relative openness assertion.
Pulling the open subfunctor back along the element of `Pic(X/S)(P)` defined by
an actual family `L` gives an open subscheme of `P`. This explains the
arbitrary `P`, the arbitrary `L` and the all-test criterion. Restricting to
affine bases of finite type over `ℤ` follows the consumer's reduction route.
Faltings–Chai Theorem 1.9 (Raynaud) is stated on printed p.5 (PDF p.17). Its
proof begins on printed p.6 (PDF p.18) with reduction steps (1) to an affine
base `Spec R` and (2), writing `R` as a union of finite-type `ℤ`-subalgebras
and using finite presentation of `A`, to `R` of finite type over `ℤ`. Here the
restriction is a scope choice, not a hypothesis of the sources, and no such
limit argument is part of this statement. No source-specific errata note was
found in the checked project, Library or workspace `notes/errata` locations.
The public source map
[`relative-picard-source-map`](../../../notes/abelian-schemes/relative-picard-source-map.md)
records the same convention difference and construction boundaries.

## Source convention and Library convention

The two conventions differ in two ways.

1. **Which fibres are tested.** The source tests the fibre `X_t` over the
   ordinary residue field `κ(t)` at each point `t` of the test scheme. The
   Library tests every morphism `Spec K ⟶ T` with `K` algebraically closed in
   universe `u`.
2. **What is tested.** The source asks that the bundle be algebraically
   equivalent to zero. The Library asks for existence of an isomorphism
   `t_x^* ℒ ≅ ℒ` for every `K`-section `x` of the base-changed abelian scheme.
   This is the vanishing of the Mumford homomorphism on `K`-points.

This statement adopts the Library convention only. Any proof must derive the
geometric-fibre open locus. It may not replace the predicate by the source
predicate or assume that the two agree.

## Obligations of a later proof

Statement publication proves nothing. A separate proof of this proposition
must, among other things:

- Compare the source's residue-field algebraic equivalence with the exact
  geometric-fibre translation-invariance predicate. This includes invariance
  under extension to algebraically closed fields in universe `u`, and a
  kernel identification in the style of EVM (7.21)–(7.22) for the actual
  base-changed bundles. A citation is not a proof.
- Justify the actual rigidified relative pullback comparisons. These are
  compatibility of the classifier with composition (`classifyingMap_comp`),
  the transport between `T ×_S A` and the chosen `A ×_S T`, and the
  base-change conventions of `fibreLineBundle`.
- Construct the open set `U` in `P` and prove openness for the arbitrary
  parameter `P` and family `L`, without a representer, universality, an
  existing dual or the consumer representability theorem. Those would be
  circular here.
- Establish the criterion for every test `T` and `h`, including nonreduced
  tests. A bijection on geometric points alone does not prove this. The
  published `picardZeroGeometricDetection : PicardZeroGeometricDetectionStatement.{u}`
  (module `Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricDetectionProof`)
  reduces the family predicate to geometric points. Worker 390's generic bridge
  `Langlands.AbelianScheme.isPicardZeroOpenLocus_of_geometricPoints`, in the
  unreviewed shared draft (revision 2) of task
  `36b1e8df-b124-45f9-bdb3-fb9e4668b55f`, would then give the all-test
  criterion from an open with the exact geometric-point criterion. That draft
  is Worker 390's work and is not accepted mathematics. A proof should reuse it
  only after its independent acceptance, and should check the exact current
  declarations.

The field openness workflows (`36b1e8df-b124-45f9-bdb3-fb9e4668b55f` and
`62f404d2-11a6-4bc9-a050-066d12b3bfd4`) and the geometric component comparison
workflows (`3f328056-1296-4cf4-a9c4-5e9a4acd84bb` and
`58fe8476-5045-4662-9a48-c3b2a2616489`) are owned separately. Their
dependency direction is kept: this statement, any open locus it supplies,
and any adapter from openness are not to be used as inputs to those
comparisons.

## What is not asserted

This file supplies no proof and no new axiom. It asserts none of the
following:

- ambient Picard representability, an algebraic space or group algebraic
  space;
- properness, smoothness, schemeness or group structure of the open
  subscheme;
- a universal family, or the smooth-family comparison.

Openness for each actual supplied family does not by itself classify every
section of an ordinary Picard sheaf. A section that is not induced by an
actual rigidified family on the test scheme is outside its scope. Worker 139's
finite-type existence task `90a7704e-771a-4107-a91a-c67873dd035e` uses this
statement as one geometric prerequisite. That task keeps its exact
finite-type representability target. The general-base reduction stays in task
`e9fb02f6-3fec-4e98-84cf-fcbd2b47f407`.
