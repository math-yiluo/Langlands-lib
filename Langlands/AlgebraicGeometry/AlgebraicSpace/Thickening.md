# Representable closed immersions and thickenings

Author: Worker 133.

This module imports `Langlands.AlgebraicGeometry.AlgebraicSpace.Basic` and
extends its geometric predicates on actual natural transformations. It defines
closed immersions, arbitrary thickenings, nth-order thickenings, first-order
thickenings and uniformly finite-order thickenings. Every base and test scheme
remains in `Scheme.{u}` for arbitrary `u`.

## Original sources and translation

The registered source is `stacks-algebraic-space-thickenings-2026-11-01`, the
retained Stacks Project HTML snapshot downloaded on 1 November 2026. The
relevant permanent references are:

- [Definition 65.12.1, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU):
  a closed immersion of algebraic spaces is representable by schemes and is a
  closed immersion on every represented scheme base change, using the
  convention of Definition 65.5.1 already implemented in `Basic`.
- [Definition 37.2.1 in Section 37.2, Tag 04EW](https://stacks.math.columbia.edu/tag/04EW):
  a scheme thickening is a closed immersion inducing equality of underlying
  topological spaces; first and nth orders use powers of the defining ideal
  on the thickened target.
- [Definition 76.9.1 in Section 76.9, Tag 05ZJ](https://stacks.math.columbia.edu/tag/05ZJ):
  the analogous thickening and order terminology for algebraic spaces.
- [Section 87.9, Tag 0AI6](https://stacks.math.columbia.edu/tag/0AI6), introductory
  discussion through the paragraph before Lemma 87.9.3: a scheme thickening
  is a closed immersion surjective on points, and testing this property on
  represented scheme projections agrees with the algebraic-space notion.
- [Section 26.10, Tag 01IM](https://stacks.math.columbia.edu/tag/01IM),
  especially Lemma 26.10.1 and Definition 26.10.2: the scheme closed-immersion
  convention and its defining quasi-coherent ideal on the target.

The retained 02YU, 04EW, 05ZJ and 01IM pages and their comments were read, as
were the immersion discussion and comments of Section 65.12 (Tag 02YT) and
the indicated introductory part of 0AI6. Source-specific errata notes were
absent in the checked project, current Library and workspace
`notes/errata/` locations. Some nth-order and finite-order clauses of 04EW
and 05ZJ visibly repeat the smaller space as its own ambient space. We use
the intended closed immersion `X → X'` and the ideal on `X'`, as specified
by their displayed ideal inclusions.

The general-thickening conjunct is explicit in `IsNthOrderThickening`.
The source explains that nilpotence of the defining ideal already forces
the topological condition (in particular, comment 5487 of 04EW discusses
square zero). This is the mathematical rationale for retaining that
conjunct without changing the intended notion. This module proves no
comparison or equivalence theorem deriving that conjunct from kernel
nilpotence, and introduces no ideal-sheaf category on algebraic spaces.

## Actual geometric tests

All declaration names below are in
`Langlands.AlgebraicGeometry.AlgebraicSpace`. Let `S : Scheme.{u}`,
`F G : Presheaf S`, and `f : F ⟶ G`. The presheaf category, slice fppf
topology and lifted `schemeYoneda S` are exactly those of `Basic`, with
values in `Type (u + 1)`. For an algebraic-space morphism `h : X ⟶ Y`, apply
the predicates to `hom h : X.presheaf ⟶ Y.presheaf`.

`IsClosedImmersion f` is

```lean
(MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
  (Over.forget S)).relative (schemeYoneda S) f
```

Here the scheme predicate is the root namespace Mathlib predicate.
Mathlib's `MorphismProperty.relative` includes
`IsRepresentableMorphism f`. Its other conjunct requires
`AlgebraicGeometry.IsClosedImmersion p.left` for every actual
`U V : Over S`, `g : (schemeYoneda S).obj U ⟶ G`,
`a : (schemeYoneda S).obj V ⟶ F`, and `p : V ⟶ U` for which

```lean
IsPullback a ((schemeYoneda S).map p) f g
```

holds in the actual presheaf category. Thus the projection
`p.left : V.left ⟶ U.left` is a genuine scheme morphism. The square has the
pullback universal property; it is not merely commutative.

`IsThickening f` is `IsClosedImmersion f ∧ IsSurjective f`, using precisely
the published geometric-surjectivity predicate. It asserts surjectivity
on points of every represented scheme projection. Each such projection
is therefore a surjective closed immersion of schemes, the scheme-test
translation from 0AI6. This definition imposes no exponent or nilpotence
bound, no objectwise surjectivity condition on `f.app`, and no assumption
that the source or target algebraic space is represented by a scheme.

## Kernel ideal-sheaf data and order quantifiers

Mathlib's `Scheme.Hom.ker` has type
`Scheme.IdealSheafData U.left` for `p.left : V.left ⟶ U.left`. It is data
for a quasi-coherent ideal sheaf on the **target** test scheme, including
ideals on every affine open with the required localization compatibility.
Mathlib constructs it as the largest such ideal data contained in the
componentwise kernel. For a quasi-compact scheme morphism,
`Scheme.Hom.ker_apply` identifies each affine-open ideal with
`RingHom.ker ((p.left).app W).hom`. Every scheme projection here of a
closed immersion is affine by the instance in
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; affine morphisms
are quasi-compact. Consequently this kernel has exactly the intended
affine-section kernels in the situation used by these definitions.
There is no added quasi-compactness hypothesis on the spaces or the base.

The multiplication and natural-number powers are Mathlib's existing
`Scheme.IdealSheafData` operations. `IdealSheafData.ideal_pow` identifies
them with the actual ideal powers on each affine open, and
`IdealSheafData.zero_eq_bot` identifies the zero data with `⊥`.
Thus `(p.left).ker ^ (n + 1) = ⊥` is vanishing of the actual kernel
ideal-sheaf power on the target test scheme.

`IsNthOrderThickening n f` is the conjunction of `IsThickening f` and
this equality for **every** represented square displayed above. Both
`U` and `V`, both presheaf projections, and the actual map `p` range over
all such squares. The definition does not choose a particular representing
scheme to formulate the order condition.

`IsFirstOrderThickening f` abbreviates `IsNthOrderThickening 1 f`, so the
power is `1 + 1 = 2`. `IsFiniteOrderThickening f` is exactly

```lean
∃ n : ℕ, IsNthOrderThickening n f
```

A single `n` precedes all scheme tests and all represented squares. An
assertion choosing an exponent separately after each test is weaker and
is not this definition. An arbitrary thickening need not satisfy a
uniform finite-order bound. The exponent `n + 1` allows `n = 0` and is
vanishing by that exponent; it asserts no minimality or exact nilpotency
index.

## Elementary accessors and implemented proofs

`IsClosedImmersion.representable` and `IsClosedImmersion.projection`
extract the relative property's two conjuncts. The latter supplies the
actual scheme closed-immersion property for any represented square.
`IsClosedImmersion.pullback_closedImmersion` specializes it to the
chosen square of any supplied `hr : IsRepresentableMorphism f`.

`IsThickening.closedImmersion`, `IsThickening.surjective` and
`IsThickening.representable` expose its defining properties.
`IsThickening.projection_closedImmersion` and
`IsThickening.projection_surjective` apply the corresponding existing
projection APIs to any represented square. The surjectivity conclusion
is Mathlib's actual scheme `Surjective p.left`.
`IsThickening.pullback_surjective` gives it for the square chosen by any
representability witness.

`IsNthOrderThickening.thickening` and
`IsNthOrderThickening.representable` expose the underlying thickening
and its representability. `IsNthOrderThickening.kernel_pow_eq` extracts
the specified equality for any represented square.
`IsNthOrderThickening.pullback_kernel_pow_eq` applies that accessor to
`hr.fst g`, `hr.snd g`, and `hr.isPullback g`, using exactly the published
`IsRepresentableMorphism` API; it works with any supplied witness `hr`,
including `hf.representable`.

`IsFirstOrderThickening.thickening` exposes the thickening conjunct, and
`IsFirstOrderThickening.kernel_sq_eq` specializes the general power
accessor, with `1 + 1` definitionally equal to `2`.
`IsFiniteOrderThickening.thickening` opens its existential and extracts
the thickening conjunct from its nth-order witness. All these proofs
only unpack definitions or apply the existing represented-square API.

The source-backed definitions are translated through `Basic` and the
pinned Mathlib APIs. The accessors and the choice-independent
all-square presentation are elementary implementation interfaces. This
unit assumes no noetherianity, reducedness, finite type,
quasi-separatedness, or global quasi-compactness. It imposes no
representability-by-schemes condition on a general space's structure
map. It changes no Picard or rigidified-family interface and proves no
schemeness invariance, Picard deformation/effectivity, Artin
representability, or conductor gluing result.
