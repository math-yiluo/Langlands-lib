# Opposite Jacquet functors for an actual block refinement

Author: Worker 19. The quotient-action, map and functor patterns are adapted
from Worker 8's `Parabolic.ComposedFunctors` and Worker 14's
`Geometric.RefinementFunctors`; their contribution is retained in the submission
attribution. The actual opposite subgroup geometry is imported from
`Parabolic.OppositeRefinementDefinitions`.

For an ordered block shape `B : BlockShape n` and an inner block refinement
`S : BlockRefinement B`, this module constructs two actual opposite Jacquet
quotients. One starts with a representation of the outer product Levi
`B.Levi F`; the other starts with a representation of `GeneralLinear n F`.
Both have the same target group `Geometric.refinedLevi F B S`. Their normalized
p-adic actions use the positive half of the corresponding explicit upper full
character, obtained by applying the usual inverse-half operation to its inverse.

## Actual quotient carriers and raw actions

`Geometric.RefinedOppositeJacquetModule B S ρ` is
`Jacquet.Coinvariants ρ (refinedOppositeUnipotent F B S)`. The subgroup is the
actual product of the inner lower block radicals in `B.Levi F`.
`Parabolic.ComposedOppositeJacquetModule B S ρ` is
`Jacquet.Coinvariants ρ (composedOppositeUnipotent F B S)`. Its subgroup is the
full ambient lower radical defined by the preimage of the inner lower radical
under the outer opposite Levi projection. In particular it includes both the
outer lower radical and the embedded inner lower radical.

Each carrier is literally the quotient by the linear span of
`ρ(u)v - v` for elements `u` of that subgroup. The linear maps
`refinedOppositeJacquetMk` and `composedOppositeJacquetMk` are the canonical
quotient maps. Their `_surjective` lemmas use the general coinvariant
surjectivity theorem.

`refinedOppositeJacquetAction` and `composedOppositeJacquetAction` pull back the
published action of the radical's normalizer along the actual common-Levi
normalizer maps. Their `_mk` lemmas give, respectively,

```text
m [v] = [ρ(m.val) v],
m [v] = [ρ(B.leviEmbedding F m.val) v].
```

The radical normalizer laws and the underlying matrix formulas are already
proved in `OppositeRefinementDefinitions`. The two `...JacquetMap` constructions
descend any ambient intertwiner `f`, and their `_mk` lemmas state
`[v] ↦ [f(v)]`. Equivariance is inherited from the general coinvariant map at
the actual normalizer element, rather than supplied as an assumption.

These algebraic constructions work over any commutative base ring `F`, with
complex representation coefficients. For a topological commutative ring,
`isSmooth_refinedOppositeJacquetAction` and
`isSmooth_composedOppositeJacquetAction` prove smoothness by taking the smooth
normalizer quotient action and pulling it back along the continuous normalizer
map. No admissibility, irreducibility or finite-length hypothesis is used.

## Explicit opposite normalization

Let `p` be prime, `F : PadicField p`, and `T : F.TopologicalData`. In the
namespace `PadicField.TopologicalData`,

```text
T.refinedOppositeLeviModulus B S  = (T.refinedLeviModulus B S)⁻¹,
T.composedOppositeLeviModulus B S = (T.composedLeviModulus B S)⁻¹.
```

These are definitions of positive unit-valued characters on the common refined
Levi. The inner upper character is the product of the inner block characters;
the full composed upper character is the restricted outer character times the
inner character. Thus the ambient normalization uses the entire composed
character. The two `_apply` lemmas expose inversion pointwise; the two `_ker`
lemmas prove that inversion preserves the kernel. The `isOpen_ker_...` lemmas
then reuse openness for the corresponding upper character.

`Jacquet.inverseHalfCharacter_inv` proves for every group and positive character
`δ` that

```text
inverseHalfCharacter (δ⁻¹) = complexCharacter (positiveHalfCharacter δ).
```

The proof uses monoid-homomorphism extensionality and the intrinsic inversion
laws of the positive square-root and complex embedding homomorphisms. Applying
it to the two explicit upper characters proves
`inverseHalf_refinedOppositeLeviModulus` and
`inverseHalf_composedOppositeLeviModulus`. Their right sides are exactly the
existing `T.refinedLeviHalfModulus B S` and `T.composedLeviHalfModulus B S`.

`normalizedRefinedOppositeJacquet` and `normalizedComposedOppositeJacquet` twist
the raw actions by the inverse half of the respective opposite full character.
Their proved `_mk` formulas are

```text
m [v] = T.refinedLeviHalfModulus B S m • [ρ(m.val) v],
m [v] = T.composedLeviHalfModulus B S m •
          [ρ(B.leviEmbedding F.Carrier m.val) v].
```

The complex units in these formulas are coerced to complex scalars. The positive
square root is canonical. This is the positive upper-half normalization on an
actual lower-radical quotient. No equivalence with an upper-radical quotient is
assumed.

The normalized `...Map` constructions twist the raw descended intertwiners;
their `_mk` formulas remain `[v] ↦ [f(v)]`. The normalized smoothness proofs
combine raw smoothness with the open kernel of the normalizing character and
the existing smooth-twist theorem.

## Bundled functors and universes

`T.normalizedRefinedOppositeJacquetFunctor B S` maps smooth complex
representations of `B.Levi F.Carrier` to those of the common refined Levi.
`T.normalizedComposedOppositeJacquetFunctor B S` maps smooth complex
representations of `GeneralLinear n F.Carrier` to that same category.
Both use the actual normalized quotient on objects and the descended map on
morphisms. Identity and composition laws are proved by extensionality on
quotient representatives. All source and target topologies are induced by `T`.

The field universe `uF` and representation universe `uV` are independent; both
functors preserve `uV`. The unbundled map constructors allow a separate target
representation universe `uW`. Rank zero is allowed via the empty block shape. Every block present in a
`BlockShape` has positive size by its defining field. The module imposes no
additional positive-rank, admissibility, finite-length, temperedness or
square-integrability hypothesis.

## Original sources and scope

This is a derived type-A specialization of the actual quotient construction and
normalization in the following retained originals:

- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472, §§1.7–1.8,
  especially §1.8(b), pp.443–444 (PDF pages 4–5), and §§2.1–2.3, p.446
  (PDF page 7). Source `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`;
  retained at `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
  The quotient is by radical differences; the normalized action multiplies
  by the inverse half of the full positive character. The block triples
  supply the GL_n and product-Levi setting.
- A. J. Silberger, *The Langlands quotient theorem for p-adic groups*,
  Math. Ann. 236 (1978), 95–104, §2, p.97 (PDF page 3), and Lemma 5.3,
  p.100 (PDF page 6). Source
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`;
  retained at `/home/taskhub/pilot/literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`.
  The opposite Jacquet convention in §2 and the relative quotients in Lemma 5.3
  use positive upper-half normalization. The two common-Levi interfaces here
  prepare the ambient and relative opposite quotients used there.

The cited passages were read directly, including the formula-bearing page
images. No source-specific errata files were present in the public notes at
authoring time. The arbitrary-ring raw constructors, universe choices, and
categorical packaging are internal extensions of the sources. Their laws use
the published generic coinvariant, twist, smoothness and character constructions.

The characters named `...Modulus` here are explicitly defined algebraic
characters. Their identification with Haar conjugation scaling remains a
separate analytic obligation. This module proves the intrinsic quotient, map,
normalization, smoothness and functor laws only. It asserts no transitivity,
exactness, admissibility preservation, relative multiplicity comparison,
inducing-data recovery or Langlands classification theorem. In particular,
Silberger's Lemma 5.3 is a later statement and proof obligation.
