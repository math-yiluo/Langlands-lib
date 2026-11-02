# Translations of a group scheme over an algebraically closed field

This module collects four general scheme-theoretic lemmas. They are used to prove
`Langlands.AbelianScheme.AlgClosedFieldDualSchemeRelativeDimensionStatement`, but none of
them mentions duals or line bundles. All declarations are in namespace
`Langlands.AlgebraicGeometry`. Each is proved in this file from Mathlib and one published
Library theorem, uses no `sorry`, and introduces no axiom.

The content is internal infrastructure, not a theorem quoted from a source. The
homogeneity lemma is the standard fact that translations act transitively on the rational
points of a group scheme. The proof of Theorem (6.18) of Edixhoven, van der Geer and
Moonen, *Abelian Varieties* (printed p.96, PDF p.100; registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`) cites (6.6) and (6.15) for the
group-scheme facts it needs. The Lean route instead uses this lemma to transport the origin
stalk to every closed point. The remaining lemmas are routine commutative algebra and
dimension bookkeeping.

## `GrpObj.exists_iso_apply_closedPoint`

Let `K` be algebraically closed and `G : Over (Spec K)` a group object (`[GrpObj G]`) whose
structure morphism is locally of finite type. For closed points `x y : G.left` there is an
automorphism `α : G.left ≅ G.left` with `α.hom ≫ G.hom = G.hom` and `α.hom x = y`.

Proof. Mathlib's `pointEquivClosedPoint` identifies closed points of a locally finite type
scheme over an algebraically closed field with rational points. So `x` and `y` give
sections `x' y' : 𝟙_ _ ⟶ G`. The automorphism is `(mulRight x')⁻¹ ≪≫ mulRight y'`, right
translation by `x'⁻¹ y'`, built from Mathlib's `GrpObj.mulRight`. The identity
`x' ≫ α.hom = y'` follows by `simp`. Evaluating its underlying scheme map at the closed
point of `Spec K` gives `α.hom x = y`. The required automorphism is the image of `α` under
`Over.forget`, and `Over.w` gives compatibility with `G.hom`.

## `isReduced_stalk_of_specializes`

For a scheme `X` and points with `y ⤳ x`, if the stalk at `x` is reduced, so is the stalk
at `y`.

Proof. Choose an affine open `U` containing `x`; it also contains `y`. The stalk at `y` is
a localization of `Γ(X, U)` (`IsAffineOpen.isLocalization_stalk`). Write a nilpotent
element as `r / s` with `(r / s)ⁿ = 0`. Then `m * rⁿ = 0` in `Γ(X, U)` for some `m` outside
the prime of `y`. Hence `m * r` is nilpotent in `Γ(X, U)`, so its germ at `x` is nilpotent
and therefore zero. Mapping along the specialization map of stalks
(`germ_stalkSpecializes`) shows that the germ of `m * r` at `y` is zero. Since `m` is a unit
in the stalk at `y`, the germ of `r` is zero, and so `r / s = 0`.

## `isReduced_of_isReduced_stalk_closedPoint`

A scheme `X` whose underlying space is Jacobson is reduced when its stalks at all closed
points are reduced.

Proof. In a Jacobson space every nonempty locally closed set meets the closed points
(`nonempty_inter_closedPoints`). Applied to the closure of `{y}`, this gives a closed point
`x` with `y ⤳ x`. The previous lemma transfers reducedness from the stalk at `x` to the
stalk at `y`. Mathlib's `isReduced_of_isReduced_stalk` concludes.

## `smoothOfRelativeDimension_of_ringKrullDim_stalk`

Let `f : X ⟶ Spec k` be smooth over a field `k`. If the stalk of `X` at every closed point
has Krull dimension `g`, then `f` is smooth of relative dimension `g`.

Proof. `X` is Jacobson because `f` is locally of finite type. Let `x : X`. Mathlib's
`Smooth.exists_isStandardSmooth` gives affine opens `U` of `Spec k` and `V ∋ x` of `X` with
`f.appLE U V e` standard smooth, hence standard smooth of some relative dimension `n`. The
restriction `V.ι ≫ f` is therefore smooth of relative dimension `n`. This uses the
`HasRingHomProperty` characterization on affines, the `arrowResLEAppIso` comparison and
`RingHom.isStandardSmoothOfRelativeDimension_respectsIso`. The open set `V` contains a
closed point `z` of `X`, which is also closed in `V`. The published theorem
`Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension` says that the stalk of
`V` at `z` has Krull dimension `n`. Via `V.stalkIso`, that stalk is the stalk of `X` at `z`,
whose dimension is `g` by hypothesis. Hence `n = g`, and the same chart witnesses relative
dimension `g` at `x`.

## Imports

- `Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof` (published proof
  of `FieldSmoothClosedPointStalkDimensionStatement`);
- Mathlib `AlgebraicGeometry.AlgClosed.Basic`, `AlgebraicGeometry.Morphisms.Smooth` and
  `CategoryTheory.Monoidal.Grp`.

The first lemma uses `set_option backward.defeqAttrib.useBackward true` and
`backward.isDefEq.respectTransparency false`. These options affect only elaboration.
