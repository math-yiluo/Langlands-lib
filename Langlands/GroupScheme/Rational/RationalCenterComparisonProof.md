# The scheme center of a reductive group over a local field

Author: Worker 712.

This file proves `Langlands.GroupScheme.RationalCenterComparisonStatement`
as the theorem `Langlands.GroupScheme.rationalCenterComparison`, whose type is
exactly `RationalCenterComparisonStatement.{u}`. Let `F : Type u` be a
nonarchimedean local field and `M` a group scheme over `Spec F` with
`IsConnectedReductive M`. Then

```text
schemeCenterPoints M = Subgroup.center (rationalPoints M).
```

The proof adds no assumptions. In particular it assumes nothing about the
characteristic of `F` or about the smoothness of the center. It uses three
fields of `IsConnectedReductive M`: `smooth`, `isAffineHom` and
`connectedSpace`. The triviality of the geometric unipotent radical is not
used.

## Route

The statement's Markdown names the literature route as Milne, *Algebraic
Groups*, Proposition 1.93 together with rational-point density from
unirationality (Theorem 17.93(b)). The implemented proof follows the shape
of Proposition 1.93: if the `F`-points of a smooth affine group separate its
coordinate functions, then a point central in `M(F)` is central in the
scheme-theoretic sense. It does not use unirationality. Density is obtained
from the local field structure instead, through the helper
`Langlands.RingTheory.LocalFieldDensity.exists_algHom_apply_ne_zero`. That
helper says: over a complete nontrivially normed field, the points of a
smooth domain with a point separate its elements. See
`Langlands/RingTheory/LocalFieldDensity/Density.md` and
`Langlands/RingTheory/LocalFieldDensity/ImplicitPoints.md`; its proof is an
implicit function theorem argument.

## From separating points to the scheme center

`RationalCenterComparisonProof.center_le_schemeCenterPoints`: let `k` be any
commutative ring and `M` an affine group scheme over `Spec k`
(`IsAffineHom M.X.hom`). Suppose that for every nonzero `d` in the
coordinate algebra `O(M) = Lie.coordinateAlgebra M` some `k`-algebra map
`y : O(M) → k` has `y d ≠ 0`. Then
`Subgroup.center (rationalPoints M) ≤ schemeCenterPoints M`.

Proof. Let `z` be central in `M(k)`. Write `e = Lie.coordinateIso M`, the
isomorphism `Spec O(M) ≅ M` over `Spec k`. Let `u = e.hom`, viewed as an
`O(M)`-valued point (`Lie.AffinePoints M O(M)`). Let `τ : M.X → Spec k` be
the map to the terminal object `Over.mk (𝟙 _)`. In the group of
`O(M)`-points put

```text
p₁ = (u ≫ τ ≫ z) * u,    p₂ = u * (u ≫ τ ≫ z).
```

1. For every `k`-point `y : O(M) → k`, `Lie.affineMap M y p₁ =
   Lie.affineMap M y p₂`. Write `T₀ = Spec k`, as the `algSpec` of `k`.
   Let `s = Spec y : T₀ → Spec O(M)`, let `w = s ≫ u`, and let `i : T₀ →
   Over.mk (𝟙 _)` be the map to the terminal object. The underlying map of
   `i` is `Spec (𝟙 k)`, so `i` is an isomorphism. Composition with `s`
   distributes over the products (`MonObj.comp_mul`), and `s ≫ u ≫ τ = i`
   because the target is terminal. So the claim becomes
   `(i ≫ z) * w = w * (i ≫ z)`. Writing `w = i ≫ (inv i ≫ w)` and pulling
   `i` out reduces this to the commutation of `z` with the `k`-point
   `inv i ≫ w`, which holds because `z` is central in `M(k)`.
2. `(τ ≫ z) * 𝟙 M.X = 𝟙 M.X * (τ ≫ z)` as endomorphisms of `M.X`.
   `e.hom` is an epimorphism, and precomposing with it turns the two sides
   into `p₁` and `p₂`. The coordinate map `Lie.pointCoordinates M` is a
   bijection from `O(M)`-points to `k`-algebra maps `O(M) → O(M)`, so it
   suffices that the two coordinate maps agree at every `d`. If they
   differed at `d`, the separation hypothesis would give `y` that is nonzero
   on their difference. But `Lie.pointCoordinates_naturality` and step 1 show
   that `y` composed with either coordinate map gives the same map.
3. The scheme center membership requires, for every test object `T'`, every
   `a : T' → Over.mk (𝟙 _)` and every `h : T' → M.X`, that `a ≫ z` commutes
   with `h`. Here `a = h ≫ τ`, since the target is terminal. Precomposing the
   identity of step 2 with `h` gives `(h ≫ τ ≫ z) * h = h * (h ≫ τ ≫ z)`.

## Local fields have a complete nontrivial norm

`RationalCenterComparisonProof.exists_algHom_apply_ne_zero_of_localField`:
for a nonarchimedean local field `F` and a smooth `F`-algebra `A` that is a
domain, every `x : A →ₐ[F] F` and every `a ≠ 0` give some `y : A →ₐ[F] F`
with `y a ≠ 0`.

Proof. Equip `F` with the uniform structure of its topological additive
group. Make the valuation `Valued.v` rank one: compose the embedding of the
value group (`MonoidWithZeroHom.ValueGroup₀.embedding`) with the embedding
into `ℝ≥0` provided by `IsRankLeOne`. Then `Valued.toNontriviallyNormedField`
makes `F` a nontrivially normed field. Its field structure is the given one,
so the `F`-algebra structure of `A` is unchanged. `F` is complete for this
structure; Lean finds this instance by `inferInstance`, from Mathlib's
instances for `IsNonarchimedeanLocalField`. The conclusion does not mention
the norm, so `exists_algHom_apply_ne_zero` applies directly.

## Assembly

`rationalCenterComparison`. Let `D = O(M)`.

- `D` is a domain by the published `CharacterLatticeProof.isDomain_coord`,
  which uses smoothness, affineness and connectedness.
- The structure map `Spec D → Spec F` is smooth. It equals the composite of
  the isomorphism `(Lie.coordinateIso M).hom.left` with the smooth map
  `M.X.hom` (`Over.w`). By `HasRingHomProperty.Spec_iff` and
  `RingHom.smooth_algebraMap`, `D` is a smooth `F`-algebra.
- `Lie.coordinateOrigin M : D →ₐ[F] F`, the coordinates of the identity
  point, is an `F`-point of `D`.

So `exists_algHom_apply_ne_zero_of_localField` shows that the `F`-points of
`D` separate its elements, and `center_le_schemeCenterPoints` gives
`Subgroup.center (rationalPoints M) ≤ schemeCenterPoints M`. The reverse
inclusion is the published `schemeCenterPoints_le_center`. The two
inclusions give the equality by `le_antisymm`.
