# Affine representation and scheme-local morphism properties

Author: Worker 208.

This module imports the published `AlgebraicSpace.Thickening` foundation and
Mathlib's finite-morphism and open-immersion modules. It defines affine scheme
representation and the representable finite and open-immersion properties.
It also supplies their elementary accessors and the implication from a closed
immersion, hence from an unrestricted thickening, to a finite morphism.

## Sources and provenance

The retained originals are the registered Stacks Project HTML snapshots of
1 November 2026:

- `stacks-algebraic-spaces-foundations-2026-11-01`, directory SHA-256
  `398dc48cec8605ced66045042e97948174a3ec96d41edb157b703103a6b04be9`:
  `025V.html`, [Definition 65.5.1](https://stacks.math.columbia.edu/tag/025V).
  A representable transformation has a scheme-morphism property when every
  represented scheme base change has that property. The definition assumes
  the scheme property is stable under base change and fppf local on the base.
- `stacks-algebraic-space-thickenings-2026-11-01`, directory SHA-256
  `ccb6ba86c00dce19994e249af819e4ed6aa7958b0fff47061565d127630d29da`:
  `02YU.html` and its text aid, [Definition 65.12.1(1)](https://stacks.math.columbia.edu/tag/02YU).
  Open immersions of algebraic spaces are representable open immersions in
  the preceding scheme-test sense.
- `stacks-algebraic-space-affine-descent-2026-11-01`, directory SHA-256
  `10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`:
  `03ZN.html` and its text aid, [Section 67.45](https://stacks.math.columbia.edu/tag/03ZN).
  Lemma 67.45.1 identifies representable finite morphisms by affine scheme
  tests; Lemma 67.45.3 identifies the representable convention with the
  affine-test Definition 67.45.2. Lemma 67.45.10 states that a closed immersion
  is finite.
- The same affine-descent snapshot, `07VQ.html` and its text aid,
  [Lemma 70.15.1](https://stacks.math.columbia.edu/tag/07VQ), motivates asking
  for actual affine scheme representations. Its finite-surjective affine
  descent assertion is not proved or assumed by this module.

Definition 65.5.1 and its comments, Definition 65.12.1 and its comments,
and the full retained Sections 67.45 and 70.15 with comments were read.
No source-specific errata note was found in the checked project, Library
or workspace locations. The finite convention is implemented directly as a
relative scheme property; the equivalences in Lemmas 67.45.1 and 67.45.3
explain its mathematical agreement with the source, rather than supplying
additional Lean comparison theorems here.

The affine-representation predicate is an internal specialization of the
published `IsRepresentedByScheme`: the actual representing scheme must
additionally be affine. The accessors below are elementary interfaces for
these definitions. The finite implication uses the actual Mathlib
closed-immersion-to-finite instance, transported through relative properties.
Mathlib is pinned at commit
`5ed2965256430c3649e86755f9576b54eca72435` by the prepared environment.

## Actual affine scheme representation

All names are in `Langlands.AlgebraicGeometry.AlgebraicSpace`. For arbitrary
`u`, `S : Scheme.{u}` and `X : AlgebraicSpace S`,
`IsRepresentedByAffineScheme X : Prop` is precisely

```lean
∃ U : Over S, AlgebraicGeometry.IsAffine U.left ∧
  Nonempty ((schemeYoneda S).obj U ≅ X.presheaf)
```

The witness is an actual scheme over `S`. Its underlying scheme `U.left`
is affine in Mathlib's absolute sense. No affineness condition is placed
on `U.hom : U.left ⟶ S`, and the base may be any scheme.
The other conjunct supplies an actual natural isomorphism with the
space's presheaf. As in `Basic`, `schemeYoneda S` is lifted Yoneda with
values in `Type (u + 1)`; all base, test and representing schemes remain
in `Scheme.{u}`.

`IsRepresentedByAffineScheme.representedByScheme` forgets the affine
conjunct and retains the scheme and natural-isomorphism witness.
`schemeToSpace_isRepresentedByAffineScheme U`, given the actual instance
`AlgebraicGeometry.IsAffine U.left`, supplies `U` itself and the identity
natural isomorphism. These proofs only unpack or construct witnesses.

## Finite morphisms and open immersions

Let `F G : Presheaf S` and let `f : F ⟶ G` be an actual natural
transformation. The two predicates are

```lean
def IsFinite (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@AlgebraicGeometry.IsFinite.{u})
    (Over.forget S)).relative (schemeYoneda S) f

def IsOpenImmersion (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
    (Over.forget S)).relative (schemeYoneda S) f
```

The scheme properties in this display are Mathlib's root-namespace
predicates. `inverseImage` forgets the map to `S` and applies the property
to the actual scheme morphism. Mathlib's `relative` includes
`IsRepresentableMorphism f` as its first conjunct. For its second conjunct,
for every actual `U V : Over S`, every
`g : (schemeYoneda S).obj U ⟶ G`, every
`a : (schemeYoneda S).obj V ⟶ F` and every `p : V ⟶ U` satisfying

```lean
IsPullback a ((schemeYoneda S).map p) f g
```

the actual scheme morphism `p.left : V.left ⟶ U.left` must be finite,
respectively an open immersion. The square has the pullback universal
property in the actual presheaf category. Every representing square is
tested, so the definition does not depend on the selection of one
representability witness. This is precisely the convention of the
published `IsEtale`, `IsSurjective` and `IsClosedImmersion`.

Mathlib's `AlgebraicGeometry.IsFinite` requires an affine scheme morphism
whose ring map on every affine open of the target is finite. Its
`AlgebraicGeometry.IsOpenImmersion` is the actual scheme open-immersion
property. The new predicates are defined for arbitrary presheaves and
transformations. For an algebraic-space morphism `h : X ⟶ Y`, apply them
to the existing `hom h : X.presheaf ⟶ Y.presheaf`.

`IsFinite.representable` and `IsOpenImmersion.representable` extract the
representability conjuncts. Their respective `projection` lemmas take
`g`, `a`, `p` and the displayed `IsPullback` witness, and return
`AlgebraicGeometry.IsFinite p.left` or
`AlgebraicGeometry.IsOpenImmersion p.left`. Their proofs extract the
second conjunct.

`IsFinite.pullback_finite` and
`IsOpenImmersion.pullback_openImmersion` take any
`hr : IsRepresentableMorphism f` and any scheme test `g`, and return the
corresponding scheme property for `(hr.snd g).left`. They apply the
arbitrary-projection accessor to `hr.fst g`, `hr.snd g` and
`hr.isPullback g`. In particular, the caller may use the representability
witness supplied by the geometric property itself, or any other witness.

## Closed immersions and arbitrary thickenings are finite

`IsClosedImmersion.finite` has the full type

```lean
{S : Scheme.{u}} → {F G : Presheaf S} → {f : F ⟶ G} →
  IsClosedImmersion f → IsFinite f
```

The implemented proof applies
`MorphismProperty.relative_monotone` to the inverse-image scheme
properties. For an arbitrary map `p : V ⟶ U` over `S`, it installs the
given `AlgebraicGeometry.IsClosedImmersion p.left` as a local instance
and obtains `AlgebraicGeometry.IsFinite p.left` from Mathlib's
unrestricted instance in `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
Relative monotonicity keeps representability and applies this implication
to every represented square.

`IsThickening.finite : IsThickening f → IsFinite f` extracts
`IsThickening.closedImmersion` and applies the preceding implication.
It applies to the existing general `IsThickening`; no nilpotence,
first-order, nth-order or finite-order condition is an argument. The
thickening's geometric surjectivity remains available separately through
the published `IsThickening.surjective`.

## Scope

The new definitions and lemmas impose no extra geometric or order
hypothesis. The published `Basic`, `Thickening` and
`SchemenessOfThickeningStatement` Lean/Markdown pairs and their import
closures are unchanged. This is a focused definition unit: it establishes
no finite-surjective affine descent, open-space lifting, gluing, general
schemeness theorem, reduction construction or integral-morphism predicate.
It contains no Picard or actual-family comparison result.
