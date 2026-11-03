# Extensions of split series along fppf quotients

This derived unit proves that the published finite Ga-series predicate
`RelativeRoot.HasSplitSeries` is closed under extensions. Let `N` be a closed
subgroup of `P` and let `q : P ⟶ Q` be an fppf quotient map with kernel exactly
`N`. If `N` has a split series of length `m` and `Q` one of length `n`, then `P`
has one of length `m + n`. Milne, *Algebraic Groups* (2017), §16.g "Split
solvable groups", printed p.343 (PDF p.359), calls this fact obvious:
"Extensions of split solvable groups are obviously split". In the relative
scheme setting of `HasSplitSeries`, the subgroups of the series must remain
smooth and connected and the quotient maps must remain fppf. Most of the work
is checking these conditions. The unit changes no published definition.

## Definition

`translationAction j : P.X ⊗ N.X ⟶ P.X`, for a homomorphism `j : N ⟶ P`, is the
right translation action of `N` on `P` through `j`. On points it sends `(p, n)` to
`p * j n`. `comp_translationAction` records this point formula.

## The torsor square

`comp_eq_one_of_range_kernelι_eq`: if the kernel of `q` has the same range as `j`
on every test, then `j ≫ q = 1`.

`isPullback_translationAction`: let `j` be a monomorphism whose range equals the
range of `kernelι q`. Then the square with sides the first projection
`P × N ⟶ P`, the translation action `P × N ⟶ P`, and `q` twice is a pullback in
`Over B`. Two points `x, x'` of `P` with equal images under `q` differ by a unique
point of `N`: `x⁻¹ * x'` lies in the kernel and hence in the range of `j`, and `j`
is a monomorphism. The lift is `(x, y)` with `j y = x⁻¹ * x'`. Both of its
equations and its uniqueness follow from the group laws on points.
`isPullback_translationAction_left` maps this square to schemes by the forgetful
functor `Over B ⥤ Scheme`.

## Descent to the quotient map

In the torsor square, the first projection `P ×_B N ⟶ P` is the base change of
the structure map `N.X.hom` along `P.X.hom`. The translation action is the base
change of `q` along `q`. So any property of `N.X.hom` that is stable under base
change holds for the translation action, and it descends to `q` along `q` when
`q` is a cover for which the property descends.

- `smooth_of_range_kernelι_eq`: suppose `q` is flat, surjective and
  quasi-compact and `N` is smooth over the base. Then `q` is smooth. This uses
  Mathlib's fpqc descent `MorphismProperty.of_isPullback_of_descendsAlong` with
  `Q = Surjective ⊓ Flat ⊓ QuasiCompact`.
- `geometricallyConnected_of_range_kernelι_eq`: suppose `q` is surjective and `N`
  is geometrically connected over the base. Then `q` is geometrically connected.
  This uses the published descent of `GeometricallyConnected` along surjective
  morphisms.

## Helpers

- `IsClosedSubgroup.of_range_eq`: let `i` be a monomorphism with the same range
  as a closed subgroup `j`. Then `i` is a closed subgroup. Both `i` and `j`
  represent the same subgroup functor, so `i` factors as an isomorphism followed
  by `j`.
- `isNormal_range_kernelι`: the range of the kernel inclusion of a homomorphism
  is a normal subgroup functor.

## Extension closure

`HasSplitSeries.of_fppfQuotient` takes the following hypotheses:

- `N` is smooth and geometrically connected over the base `B`, and
  `hN : HasSplitSeries m N`;
- `j : N ⟶ P` is a closed subgroup;
- `q : P ⟶ Q` is quasi-compact and `IsFppfQuotient (range j) q`;
- `HasSplitSeries n Q`.

Its conclusion is `HasSplitSeries (m + n) P`. The proof is by induction on `n`,
for all `P`, `Q`, `j` and `q` at once.

- `n = 0`. `Q` is trivial on every test, so the kernel of `q` is all of `P` and
  `j` has the same range as `𝟙 P`. The published
  `IsClosedSubgroup.sourceIsoOfRangeEq` gives `N ≅ P`, and the published
  `HasSplitSeries.of_iso` transports `hN`.
- `n + 1`. The series of `Q` gives a closed normal subgroup `j' : K' ⟶ Q`, smooth
  and connected over the base, with a split series of length `n`, and an fppf
  quotient `q' : Q ⟶ V` with kernel `K'`, where `V` is a one-dimensional vector
  group. Set `P₁ = kernel (q ≫ q')`, with inclusion `i₁`. The new first step
  of the series of `P` is `i₁` with quotient map `q ≫ q'`. Its kernel is exact by
  definition, `isNormal_range_kernelι` gives normality, and flatness,
  surjectivity and local finite presentation are stable under composition.
  The following facts about `P₁` come from the base-change square below:
  - `kernelι q'` is a closed subgroup by `IsClosedSubgroup.of_range_eq`, and
    `kernel q'` is isomorphic to `K'`. So `kernel q'` is smooth over the base
    and connected.
  - The induced map `q₁ : P₁ ⟶ kernel q'` makes the square with `i₁`,
    `kernelι q'` and `q` a pullback, by pasting the two kernel pullback squares.
    So `i₁` is a closed immersion.
  - `q₁` inherits flatness, surjectivity, local finite presentation and
    quasi-compactness from `q`. It also inherits smoothness and geometric
    connectedness, which the descent lemmas above give for `q`.
  - `P₁` is smooth over the base, since `kernel q'` is and `q₁` is smooth.
  - `P₁` is connected by Mathlib's `GeometricallyConnected.connectedSpace`: `q₁`
    is geometrically connected and open, being smooth, and its target is
    connected.
  - `N` factors through `P₁` by `j₁`, which is a closed subgroup. The kernel of
    `q₁` has exactly the range of `j₁`, by checking points through the
    monomorphism `i₁`.

  The induction hypothesis, applied to `j₁`, `q₁` and the series of
  `kernel q' ≅ K'`, gives `HasSplitSeries (m + n) P₁`. This is the remaining
  field of `HasSplitSeries (m + n + 1) P`.

`HasSplitSeries.of_fppfQuotient_of_field` covers the case where the base is a
field `Spec k`. There it suffices that `N` be smooth, quasi-compact and connected.
Geometric connectedness follows from the published
`geometricallyConnected_of_connected`.

## Scope

The hypotheses on `N` are smoothness, geometric connectedness (or connectedness
over a field) and quasi-compactness of `q`. They are needed only to keep the new
first subgroup `P₁` smooth and connected, as the published `HasSplitSeries`
requires. The unit proves no statement about images or quotients of split
groups.
