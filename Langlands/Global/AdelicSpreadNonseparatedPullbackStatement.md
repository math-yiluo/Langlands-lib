# Adelic fibre products over a nonseparated base: the doubled-origin line

Author: Worker 3519.

This module states a counterexample to an unrestricted reading of a sentence of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. It contains two auxiliary
definitions and three Prop-valued statements, and no proof.

## Source

Printed p.9, Section 4: "In this way, we see that `X(A_F)` is locally compact and Hausdorff
(with a countable base of opens) when `X` is `F`-separated, and moreover that this topology is
compatible with fiber products for general `X`."

The Library proves fibre-product compatibility only over a separated base:
`AdelicSpreadModelPullbackStatement`, `AdelicSpreadPullbackStatement` and
`AdelicFixedModelPullbackStatement` all assume `IsSeparated Z.hom` for the base `Z`. The
scope paragraph of `AdelicSpreadPullbackStatement.md` records that the Library does not adopt
an unrestricted nonseparated-base reading of "for general `X`". The present statement shows
that this reading is false. It is the same generality as `AdelicSpreadModelPullbackStatement`,
with the separatedness of the base dropped.

## Definitions

`doubledOriginLine R`, for a commutative ring `R`, is the scheme `DoubledPointLine.glued R 1`
over `Spec R`, with structure morphism `DoubledPointLine.toBase R 1`. With `p = 1`, the
Library's `DoubledPointLine` glues the affine lines `Spec R[t]` and `Spec R[s]` along the opens
`D(t)` and `D(s - 1)`, identified by `t = s - 1`. This is the affine line with doubled origin:
the point `t = 0` of the first line and the point `s = 1` of the second are not identified.

`doubledOriginChart R b : ringTest R R[X] ⟶ doubledOriginLine R` is the chart
`DoubledPointLine.ι R 1 ⟨b⟩` as a morphism over `Spec R`. The chart `true` has coordinate `t`;
the chart `false` has coordinate `s`. Here `ringTest R R[X]` is the affine line `Spec R[X]`
over `Spec R`.

## Statements

`NumberFieldSpreadNonseparatedPullbackStatement`: for every number field `K` and every finite
set `S` of finite places, write `R` for the `S`-integers. Then:

1. `doubledOriginLine R` is locally of finite type and quasi-compact over `Spec R`;
2. for every pullback cone `c` of the two charts that is a limit, the following map is not a
   homeomorphism. Let `G` be base change from `R` to `K`. The map is
   `affineSchemePullbackPointComparison K (Adeles K) (c.map G)`, `w ↦ (w ≫ fst, w ≫ snd)`.
   It goes from the adelic points of the generic fibre `G.obj c.pt` to the pairs of adelic
   points of two copies of the affine line `G.obj L` with the same image in the doubled-origin
   line. Each adelic point space carries the topology attached to its model and the identity
   generic-fibre isomorphism (`numberFieldSpreadAdelePointTopology … (Iso.refl _)`); the pairs
   carry the subspace topology of the product.

`CurvePlaceSpreadNonseparatedPullbackStatement` is the same assertion for every function
field `F` over a perfect field `k` (with the rational-function action and scalar tower) and
every finite set `S` of places, with the `S`-integers `curvePlaceSIntegers k F S`, the
curve-place adeles and `curvePlaceSpreadAdelePointTopology`.

`AdelicSpreadNonseparatedPullbackStatement` is their conjunction.

Apart from the separatedness of the base, the data satisfy every hypothesis of
`AdelicSpreadModelPullbackStatement`. The factors are affine lines, of finite type; the base
is of finite type by clause 1. The cone is an arbitrary limit pullback cone, and the
topologies, map and constant-field hypotheses are those of that statement. So, once both are
proved, the two statements show that the separated-base hypothesis cannot be dropped. They
also show that the doubled-origin line is not separated. The perfect-constant hypothesis
matches `AdelicSpreadModelPullbackStatement`; the counterexample itself does not use it.

## Why the statement holds

This is the expected proof route; the proof is a separate contribution.

The pullback of the two charts is their intersection: the punctured line with coordinate `s`
and `s - 1` a unit. Its first projection has `t = s - 1` and its second has `s`. A pair
`(a, b)` of adelic points of the two lines has the same image in the doubled-origin line exactly
when it comes from the intersection, that is, `a = b - 1` and `a` is a unit. So the comparison
is the bijection `u ↦ (u, u + 1)` from `A^×` onto the set of pairs.

The source carries the topology of the affine model `Spec R[s, 1/(s - 1)]`: by affine agreement
(`AdelicSpreadAffineTopologyStatement`) and functoriality, this is the topology of `A^×`
embedded in `A²` by `u ↦ (u, u⁻¹)`. The target carries the subspace topology from `A × A`,
and its first coordinate identifies it with `A^×` with the subspace topology from `A`. The
comparison is continuous; a continuous inverse would make `A^× → A` a topological embedding.
`AdelicPunctureEmbeddingStatement` proves that it is not, in both arithmetic cases.

## Provenance

Derived. Conrad states no counterexample. The example and its formulation are this
formalization's evidence that the separated-base restriction of the Library's fibre-product
statements is necessary. The doubled-origin construction is the Library's
`DoubledPointLine` with `p = 1`. The failure of `A^× → A` to be a topological embedding is
Conrad's own observation on printed pp.3–4.
