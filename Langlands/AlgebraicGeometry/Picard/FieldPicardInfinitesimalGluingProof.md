# Infinitesimal gluing for actual field Picard groupoids: proof

This module proves the published proposition
`Langlands.AlgebraicGeometry.Picard.FieldPicardInfinitesimalGluingStatement.{u}`
for every universe `u`, as the theorem

```
Langlands.AlgebraicGeometry.Picard.fieldPicardInfinitesimalGluing :
  FieldPicardInfinitesimalGluingStatement.{u}
```

Let `k : Type u` be a field, `X : Scheme.{u}` a scheme and `f : X ⟶ Spec k`.
Let `p : R →ₐ[k] A`, `q : R →ₐ[k] B`, `a : A →ₐ[k] C` and `b : B →ₐ[k] C` be
algebra maps between arbitrary commutative `k`-algebras of universe `u`. Assume
their underlying ring maps form a pullback square `h`, `b` is surjective, and
`RingHom.ker b` is nilpotent. The theorem shows that the specific published
functor `PicardGroupoid.affineSquareComparison f p q a b h` is an equivalence of
the actual groupoids. It is full, faithful and essentially surjective.
Essential surjectivity is effectivity for the actual gluing objects, with their
specified overlap isomorphisms. The argument patches actual line bundles and
actual isomorphisms, not isomorphism classes.

The properness hypothesis of the statement is introduced and not used, so the
proof holds for every scheme over a field. The field hypothesis is used through
the published `InfinitesimalCartesianCube`, which needs flatness over the field.
No condition is put on the test algebras beyond the statement's hypotheses.

The proof uses five helper modules, all in the namespace
`Langlands.AlgebraicGeometry.Picard.SquareGluingDescent`:
`SquareGluingCubes`, `SquareGluingDescent`, `SquareGluingRespect`,
`SquareGluingLegs` and `SquareGluingCech`. The route is internal: it is not
the finite projective patching route sketched in the statement's Markdown.
Full faithfulness comes from the published `SquareGluingFullyFaithful`.
Essential surjectivity comes from local effectivity, the published
`InfinitesimalLocalEffectivity`, followed by Čech gluing (`SquareGluingCech`).

## Inverse-image squares of opens

For a square `S : Sq` and an open `U` of `S.X`:

- `Sq.restrict S U` is the inverse-image square. Its corner is
  `(S.i₁ ≫ S.j₁) ⁻¹ᵁ U`, its legs are `S.j₁ ⁻¹ᵁ U` and `S.j₂ ⁻¹ᵁ U`, and its
  total scheme is `U`. Its maps are the published `leftRestriction`,
  `rightRestriction` and the restrictions `S.j₁ ∣_ U` and `S.j₂ ∣_ U`. The
  commutativity proof is the published `restriction_comm`.
- `Sq.restrictC S U` is the inclusion cube, whose maps are the four open
  inclusions. Its total map `U.ι` is an open immersion.
- `Sq.cart_restrictC`: the inclusion cube is cartesian. Its leg faces are the
  published `isPullback_morphismRestrict`. Its corner face is obtained after
  rewriting `leftRestriction` as a restriction by `Scheme.Hom.resLE_eq_morphismRestrict`.

## Families of opens

For a family `V : S.X → S.X.Opens`:

- `restrictFamily`, `restrictCFamily` and `trivialFamily` are the inverse-image
  squares, the inclusion cubes and the trivial line bundles
  `LineBundle.trivial (V x).toScheme`. They are named constants rather than
  lambdas; the kernel-related note below explains why.
- `cart_restrictCFamily` restates `cart_restrictC`. `restrictCFamily_cover`
  says the inclusion cubes cover `S.X` when `x ∈ V x` for all `x`. It uses
  `Scheme.Opens.range_ι`.
- `restrictFamily_C` and `restrictCFamily_R` are definitional equalities of
  functors. The comparison of `restrictFamily S V x` is the published
  `squareGluingComparison` of the restricted square. Restriction along
  `restrictCFamily S V x` is the published `SquareGluingRestriction.toOpen`.
  `trivialFamily_eq` unfolds `trivialFamily`.
- `nonempty_trivialFamily`: suppose the published predicate
  `InfinitesimalLocalEffectivity.IsEffectiveOn S.i₁ S.i₂ S.j₁ S.j₂ S.w D (V x)`
  holds. Then there is an isomorphism
  `(restrictFamily S V x).C.obj (trivialFamily S V x) ≅ (restrictCFamily S V x).R.obj D`.
  The proof rewrites the goal along the three equalities above and closes it
  with the effectivity hypothesis.
- `exists_iso_of_effective`: suppose `x ∈ V x` for every `x`, `FFOnCart S` holds,
  and `D` is effective on every `V x`. Then `D` is realized:
  `∃ L, Nonempty (S.C.obj L ≅ D)`. This is `Cech.exists_iso` from
  `SquareGluingCech`, applied to the inclusion cubes with the trivial bundles as
  local bundles.

Note on the kernel. Several equivalent formulations of these steps caused
kernel deterministic timeouts. In one, the realizations were built in
definitions, whose proofs are abstracted into auxiliary constants. In the
other, the families were passed as lambdas, which leaves beta-redexes in the
binder types the kernel checks. In both cases the kernel had to compare the
objects `F.obj N` of the gluing groupoids by unfolding actual module pullbacks.
The implemented version keeps every conversion inside theorems, uses
rewriting along functor-level equalities, and names the families as constants.

## The base-changed affine square

- `affineSq f p q a b h` is the square of relative spaces
  `(relativeSpace f).obj (affineBase k _)` over `C`, `A`, `B` and `R`. Its maps
  are the base changes `(relativeSpace f).map (affineBaseMap _)` of `a`, `b`,
  `p` and `q`. The commutativity proof comes from the published
  `relativeSquare_comm` and `affineSquare_comm`.
- `affineSq_C`: its comparison functor is, by definition, the published
  `PicardGroupoid.affineSquareComparison f p q a b h`.

## Full faithfulness

- `affineRestrictedCubes`: for every cartesian cube `c` into `affineSq` whose
  total map is an open immersion, the target square `T` satisfies the published
  hypothesis `SquareGluingFullyFaithful.AffineRestrictedCubes`. For an affine
  open `U` of `T.X`, compose the inclusion cube of `U` with `c`; the composite is
  cartesian. The published
  `InfinitesimalCartesianCube.cartesianCube_appTop_isPullback`, applied to the
  composite cube, gives the pullback square of global-section rings.
- `ffOnCart : FFOnCart (affineSq f p q a b h)`. Common affine trivializing covers
  of any two line bundles come from the published
  `LineBundle.exists_commonAffineTrivializingCover`. The published
  `SquareGluingFullyFaithful.full` and `SquareGluingFullyFaithful.faithful` then
  give a full and faithful comparison on the target of every such cube.
- `idC` is the identity cube of a square, and `cart_idC` says it is cartesian.
  Applying `ffOnCart` to `idC (affineSq ..)` shows the affine comparison itself
  is full and faithful.

## Essential surjectivity and the theorem

- `essSurj`: let `D` be an actual gluing datum on `affineSq`. For each point `x`
  of `X_R`, the published
  `InfinitesimalLocalEffectivity.affineSquareNeighborhood f p q a b h hb hn D ⊤ x`
  gives an affine open containing `x` on which `D` is effective. This uses
  surjectivity of `b` and nilpotence of its kernel. `exists_iso_of_effective`
  for this family of opens, with `ffOnCart`, realizes `D` by an actual line
  bundle on `X_R`.
- `affineSquareComparison_isEquivalence`: the published comparison is an
  equivalence, with fields `faithful`, `full` and `essSurj` from the two steps
  above.
- `fieldPicardInfinitesimalGluing` introduces the hypotheses of the statement
  and applies `affineSquareComparison_isEquivalence`.
