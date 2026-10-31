# Abelian-scheme structure from local abelian charts and a section

Statement design: Workers 344 and 1109. Formalization, Markdown and Lean
checks: Worker 1043.

`Langlands.AbelianScheme.AbelianSchemeStructureOfOpenCoverStatement.{u}` is
the proposition

```lean
∀ (S : Scheme.{u}) (P : Over S) (s : 𝟙_ (Over S) ⟶ P)
  (𝒰 : S.OpenCover.{u}),
  (∀ i, ∃ B : AbelianScheme (𝒰.X i),
    Nonempty ((Over.pullback (𝒰.f i)).obj P ≅ B.X)) →
    ∃ (B : AbelianScheme S) (e : P ≅ B.X), s ≫ e.hom = η[B.X]
```

In words: let `P` be a scheme over an arbitrary base `S` with a section `s`.
If, over every member of some open cover of `S`, the restriction of `P` is
isomorphic, as a scheme over that member, to the underlying scheme of some
abelian scheme, then `P` is isomorphic over `S` to the underlying scheme of
an abelian scheme over `S`, by an isomorphism carrying `s` to the unit
section. This module defines only that proposition. It contains no proof, and
it asserts nothing about whether its hypothesis holds for any particular `P`.
The module imports only `Langlands.AbelianScheme.Basic` and introduces no
other definition.

## The data

All schemes, slice categories and covers use the single universe `u`.

- `S : Scheme.{u}` is an arbitrary scheme. No quasi-separated, noetherian,
  reduced, connected or affine condition is imposed.
- `P : Over S` is an arbitrary object of the slice category: a scheme
  `P.left` with a structure morphism `P.hom : P.left ⟶ S`. Nothing is
  assumed about `P` beyond the local hypothesis below; in particular `P`
  carries no group structure.
- `s : 𝟙_ (Over S) ⟶ P` is an arbitrary morphism from the monoidal unit of
  `Over S`. The monoidal structure is Mathlib's cartesian monoidal structure
  on `Over S` (the instance in `Mathlib.AlgebraicGeometry.Pullbacks`, built
  from `Over.cartesianMonoidalCategory`). Its unit is the terminal object, `S`
  with the identity structure morphism (`Over.tensorUnit_left` and
  `Over.tensorUnit_hom` hold by `rfl`). Hence `s` is exactly a global section
  of `P.hom`: a scheme morphism `s.left : S ⟶ P.left` with
  `s.left ≫ P.hom = 𝟙 S`. Every global section is allowed.
- `𝒰 : S.OpenCover.{u}` is Mathlib's open cover of `S`: an index type
  `𝒰.I₀ : Type u`, schemes `𝒰.X i` and open immersions
  `𝒰.f i : 𝒰.X i ⟶ S` whose images cover `S`. The index type is arbitrary;
  no affine, finite or quasi-compact condition is imposed on the cover or on
  its members.

## The local hypothesis

For an index `i`, `(Over.pullback (𝒰.f i)).obj P : Over (𝒰.X i)` is the
actual restriction of `P` to the member `𝒰.X i`: by Mathlib's definition of
`Over.pullback` it is `Over.mk (pullback.snd P.hom (𝒰.f i))`, the chosen
fibre product of `P.hom` and `𝒰.f i`, viewed over `𝒰.X i` by the second
projection. This is the same pullback convention as the Library's
`AbelianScheme.baseChange`.

The hypothesis says that for each `i` there exist

- an actual `B : AbelianScheme (𝒰.X i)`, the Library bundle described below,
  and
- an isomorphism `(Over.pullback (𝒰.f i)).obj P ≅ B.X` in the slice category
  `Over (𝒰.X i)`, that is, an isomorphism of schemes from the restriction of
  `P` to the underlying scheme of `B` that commutes with the structure
  morphisms to `𝒰.X i`.

The isomorphism is wrapped in `Nonempty`, so only its existence is asserted;
no isomorphism is chosen. It is an isomorphism of underlying schemes over the
member only. It is not required to send the restriction of `s` to the unit
section of `B`, and it is not related to any group structure on `P`, which
has none.

The local hypotheses are independent existentials, one for each index. They
supply no chosen local abelian schemes or isomorphisms, and they impose

- no compatibility between the group laws of the local abelian schemes for
  indices `i` and `j` over the overlap of `𝒰.X i` and `𝒰.X j`,
- no compatibility between their unit sections,
- no relation between the local unit sections and the restriction of `s`,
- no compatibility, transition or cocycle condition on the local
  isomorphisms.

## The conclusion

The conclusion provides

- one actual `B : AbelianScheme S`,
- an isomorphism `e : P ≅ B.X` in `Over S`, that is, an isomorphism of
  schemes `P.left ≅ B.X.left` commuting with the structure morphisms to `S`,
- such that `s ≫ e.hom = η[B.X]`. Here `η[B.X] : 𝟙_ (Over S) ⟶ B.X` is the
  unit morphism of the monoid object `B.X` (Mathlib's `MonObj.one`, with the
  notation from `open scoped CategoryTheory.MonObj`), that is, the unit
  section of `B`. So `e` carries the given section `s` to the unit section.

Equivalently, transporting `B`'s structure along `e`, the scheme `P` itself
carries a structure of abelian scheme over `S` whose unit section is `s`.

The conclusion makes no uniqueness claim, about `B`, about `e` or about the
group law. It does not require the group law of `B` to restrict to, or be
isomorphic as a group scheme to, any of the local abelian schemes of the
hypothesis, and it does not require `e` to restrict to any of the local
isomorphisms. The originally supplied local group laws need not be preserved.

## The abelian-scheme bundle

`AbelianScheme T`, from `Langlands.AbelianScheme.Basic`, is used unchanged
for `T = S` and for `T = 𝒰.X i`. It extends `CommGroupScheme T`: an actual
group object in `Over T` (Mathlib's `Grp (Over T)`, with its multiplication,
unit and inverse morphisms) whose underlying monoid object is commutative
(`IsCommMonObj`). In addition, the structure morphism `X.hom` is smooth,
proper and geometrically connected (Mathlib's `Smooth`, `IsProper` and
`GeometricallyConnected`). `B.X` denotes the underlying object of `Over T`.
The global abelian scheme in the conclusion is therefore commutative, smooth,
proper and has geometrically connected fibres over `S`.

## What is retained and what is not assumed

Every universe `u`, every base scheme `S`, every scheme `P` over `S`, every
global section `s` and every universe-`u` open cover of `S` is retained.
There is no further hypothesis: no compatibility of local group laws, unit
sections or isomorphisms, and no quasi-separatedness, noetherianity,
reducedness, finite-cover, projectivity, polarization, representability or
descent hypothesis.

## Provenance

This is an internal derived prerequisite. Workers 344 and 1109 designed it,
while executing task `e78fdff3-f2d0-4fd9-9f9a-92fc56f7b43d`, for the proof of
`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement`
(module
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement`).
That proof glues the underlying local parameter schemes to a scheme `P` over
`S` and obtains a section `s` by classifying the trivial rigidified class; it
then needs an actual abelian-scheme structure on `P`. The universal property
it establishes depends on the underlying `P`, not on a group law, so the
originally supplied local group laws need not be preserved. The
section-compatible conclusion supports the recentring step described below.

No external source is claimed to state this exact proposition, and no
literature is cited for it.

This statement module does not import, and changes nothing in, any existing
Library pair. In particular the open-cover smooth-family representability
statement and the pointed-morphism rigidity statement
`Langlands.AbelianScheme.PointedMorphismRigidity` and its proof
`Langlands.AbelianScheme.pointedMorphismRigidity` (module
`Langlands.AbelianScheme.PointedMorphismRigidityProof`) are unchanged.

## Intended proof route (future obligations)

The following route is recorded for the separate proof task. None of it is
assumed by the proposition or proved by this module.

1. Transport. For each index `i`, choose a local isomorphism and transport
   the group structure of the local abelian scheme to the restriction of `P`
   (for example with Mathlib's `GrpObj.ofIso`).
2. Recentring. The restriction of `s` is a section of the restriction of `P`.
   Translation by the appropriate section (Mathlib's `GrpObj.mulRight`) is an
   isomorphism of the restriction of `P` sending the transported unit to the
   restriction of `s`; transporting the group structure along it gives a
   commutative group law with unit the restriction of `s`. Smoothness,
   properness and geometric connectedness concern only the underlying
   morphism, so each restriction becomes an abelian scheme with unit the
   restriction of `s`.
3. Rigidity. Over an overlap of two members, the canonical identification of
   the two restrictions of `P` preserves these units. The published theorem
   `Langlands.AbelianScheme.pointedMorphismRigidity` proves
   `PointedMorphismRigidity`: over an arbitrary base, a unit-preserving
   morphism from a group scheme that is smooth, proper and geometrically
   connected to a group scheme of finite presentation is a homomorphism. An
   abelian-scheme target is of finite presentation, being smooth (hence
   locally of finite presentation) and proper (hence quasi-compact and
   separated). The identifications are therefore homomorphisms, so the
   recentred local group laws agree on overlaps.
4. Gluing. The multiplication and inverse morphisms are then glued along open
   covers of `P ×_S P` and of `P` induced from `𝒰`, using Mathlib's
   `Scheme.OpenCover.glueMorphisms`; the group-object identities,
   commutativity and the unit equation are checked locally with
   `Scheme.OpenCover.hom_ext`.
5. Geometry. Smoothness and properness are local on the target (Mathlib
   provides `IsZariskiLocalAtTarget` for `IsProper` directly and for
   `Smooth` through its `HasRingHomProperty` instance), and
   geometric connectedness is a fibrewise condition
   (`GeometricallyConnected.iff_geometricallyConnected_fiber`), each fibre of
   `P.hom` lying over some member. With `B.X = P` and `e` the identity, the
   unit equation then holds because the glued unit is `s`.

These are proof leads, not hypotheses or established results of this
statement. The canonical identifications of iterated pullbacks, and any
auxiliary lemma they require, belong to the proof task.
