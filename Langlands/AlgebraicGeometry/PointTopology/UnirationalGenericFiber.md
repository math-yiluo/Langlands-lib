# Unirationality from a unirational base and a unirational generic fiber

Author: Worker 1630.

This derived helper proves a generic-fiber criterion for the published
predicate `PointTopology.IsUnirational`. A scheme `X` over a field `k` is
unirational in this sense when some nonempty open `U` of affine space
`𝔸(ι; Spec k)`, with `ι` finite, maps to `X` over `k` with dense image. All
schemes, fields and coordinate types live in one arbitrary universe `u`.

## Statements

`exists_factor_fromSpecResidueField` states the following. A morphism
`g : Spec K → X` from the spectrum of a field factors as
`Spec K → Spec κ(x) → X` through `X.fromSpecResidueField x`, where `x` is
the image of the unique point of `Spec K`. It is Mathlib's
`descResidueField_stalkClosedPointTo_fromSpecResidueField`, restated for an
arbitrary point `a` of `Spec K` and a given equation `g a = x`.

`isUnirational_iteratedAffineSpace` states that for finite `ι'` and `ι`
the iterated affine space `𝔸(ι'; 𝔸(ι; Spec k))` is unirational over `k`,
with its composite structure map to `Spec k`. The parametrization is the
whole of `𝔸(ι ⊕ ι'; Spec k)`. It maps to the iterated space by the
published isomorphism `affineSpaceSumIso` of
`Langlands.AlgebraicGeometry.PointTopology.IteratedAffineSpace`, which is
compatible with the maps to `Spec k`. The map is surjective, so its image
is dense.

`HasUnirationalDenseFiber f η` is a Prop-valued definition for a scheme
morphism `f : X ⟶ Y` and a point `η` of `Y`. It packages the two fiber
hypotheses used below.

- The scheme-theoretic fiber `f.fiber η` is unirational over the residue
  field `κ(η)`, with its structure map `f.fiberToSpecResidueField η`.
- The canonical map `f.fiberι η` from this fiber to `X` has dense image.

`IsUnirational.of_genericFiber` is the criterion. Its hypotheses are:

- `X` and `Y` are schemes over `k`, and `X` is locally of finite type over
  `k`.
- `f : X → Y` is a morphism over `k`.
- `Y` is unirational over `k`.
- `η` is a generic point of `Y`.
- The fiber of `f` over `η` is unirational over `κ(η)`, and the fiber has
  dense image in `X`.

The conclusion is that `X` is unirational over `k`.
`IsUnirational.of_hasUnirationalDenseFiber` is the same statement, with
the fiber hypotheses given as `HasUnirationalDenseFiber f η`.

No reducedness, irreducibility of `X`, separability, perfection or
infinitude assumption is added. The coordinate types remain finite.

## Proof

Let `p : U → Y` be a parametrization of `Y`, with `U` open in
`𝔸(ι; Spec k)`. Let `u` be the generic point of `𝔸(ι; Spec k)` and let
`L = κ(u)` be its residue field.

1. The open `U` is nonempty, so it contains `u`. The map
   `Spec L → 𝔸(ι; Spec k)` therefore lifts through `U`. Its point is
   generic in `U`, because the open immersion `U → 𝔸(ι; Spec k)` is
   inducing (`SchemeFiberGeometry.isGenericPoint_of_isInducing`). Since
   `p` has dense image, the point of `Spec L` maps to the generic point
   `η` of `Y`. So `Spec L → Y` factors through `Spec κ(η)`. This makes
   `L` a `κ(η)`-algebra.
2. By the published `IsUnirational.baseChange`, the base change of the
   fiber to `L` is unirational over `L`. It is parametrized by an open `V`
   of `𝔸(ι'; Spec L)`, with `ι'` finite.
3. Let `gen` be the generic point of `𝔸(ι'; 𝔸(ι; Spec k))`, which lies
   over `u`. Let `F` be its function field. The morphism
   `s : Spec F → 𝔸(ι'; Spec L)` is built with `AffineSpace.homOfVector`.
   Composed with `AffineSpace.map ι' (Spec L → 𝔸(ι; Spec k))`, it is the
   canonical map `Spec F → 𝔸(ι'; 𝔸(ι; Spec k))`, which sends the point of
   `Spec F` to `gen`. The map `AffineSpace.map ι' (Spec L → 𝔸(ι; Spec k))`
   is a preimmersion, as a base change of the preimmersion
   `Spec L → 𝔸(ι; Spec k)`, so it is inducing. Hence `s` sends the point
   of `Spec F` to a generic point of `𝔸(ι'; Spec L)`. That point lies in
   `V`, so `s` lifts through `V`.
4. Compose this lift with the parametrization of the base-changed fiber,
   the projection to the fiber, and `f.fiberι η`. The result is a
   morphism `φ : Spec F → X`. The projection from the base change is
   surjective, because `Spec L → Spec κ(η)` is surjective. Each map in the
   chain is continuous with dense image, so the point of `Spec F` goes to
   a generic point of `X`, and `φ` has dense image.
5. A chain of commutative squares shows that `φ` is compatible with the
   maps to `Spec k`. The squares are the fiber square, the base-change
   square, the parametrization squares over `L` and over `k`, the
   residue-field factorizations from steps 1 and 3, and the hypothesis
   `f ≫ Y.hom = X.hom`.
6. The iterated affine space is unirational over `k`
   (`isUnirational_iteratedAffineSpace`), and its stalk at `gen` is its
   function field. Worker 1420's published spreading lemma
   `IsUnirational.of_stalk` turns `φ` into a parametrization of `X`. It
   needs that `X` is locally of finite type over `k` and that the
   iterated affine space is germ-injective at `gen`, which holds for
   integral schemes.

The corollary `IsUnirational.of_hasUnirationalDenseFiber` unpacks the
definition and applies the criterion.

## Provenance

The criterion is derived. It is the standard argument that a dominant
family with unirational base and unirational generic fiber has a
unirational total space, written for the published actual-parametrization
predicate. The Lean proof uses Mathlib's scheme-fiber, residue-field,
stalk, affine-space and preimmersion interfaces. It also uses the
published Library modules `UnirationalBaseChange` (field-extension
transport), `UnirationalSpreading` (spreading out from a stalk) and
`IteratedAffineSpace` (coordinate sums and generic points). No external
theorem is asserted. This module proves no unirationality statement about
maximal-torus parameter schemes.
