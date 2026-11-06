# Non-open images of power maps on number-field adelic units

Author: Worker 105.

`NumberFieldPowerImageStatement` states, for number fields, the second counterexample in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
p.11. The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The
module only states the result and contains no proof.

Conrad writes: "Even if we restrict ourselves to surjective étale maps there are
counterexamples: the `n`th-power map `G_m → G_m` for `n > 1` not divisible by
`char(F)` is a finite étale map that induces the `n`th-power map `A_F^× → A_F^×`
whose image is not open." Here `F` is a global field.

## Statements

`PowerImageNotOpen S n`, for a commutative topological ring `S` and `n : ℕ`, is the
conjunction of two clauses.

1. The image of `x ↦ x ^ n` on `Sˣ` is not open. `Sˣ` carries Mathlib's units
   topology, induced by `x ↦ (x, x⁻¹)` into `S × Sᵐᵒᵖ`.
2. For every commutative ring `R` and every `R`-algebra structure on `S`, the image of
   `p ↦ p ≫ affineLinePuncturePow R n` on actual `S`-points of the punctured affine
   line `affineLinePuncture R` is not open. These points carry the Library's
   topology on points of affine schemes (the evaluation topology of
   `Langlands/AlgebraicGeometry/PointTopology/AffineScheme.lean`), as in the
   published `AdelicPunctureEmbeddingStatement`. `affineLinePuncturePow R n` is the
   actual morphism `t ↦ t ^ n` of `G_m = affineLinePuncture R`, from
   `Langlands/AlgebraicGeometry/PointTopology/AffineLinePuncturePow.lean`.

The statement is:

- `NumberFieldPowerImageStatement`: for every number field `K` and every `n ≥ 2`,
  `PowerImageNotOpen (Adeles K) n`, with Mathlib's full adele ring `Adeles K`,
  including the archimedean factors, and its topology.

The function-field case, with its additional hypotheses, is stated separately as
`CurvePlacePowerImageStatement` in a module that imports this one.

## Relation to the source and derived content

Conrad's `A_F^×` is `G_m(A_F)`. The second clause states the assertion for actual
scheme points and the actual power morphism. The first clause states it for the
unit group. The published homeomorphism `affineLinePunctureUnitHomeomorph`
identifies the two settings, and `affineLinePunctureUnitHomeomorph_pow` identifies the
two power maps. Clause 2 is stated for every base ring `R` because the punctured line
and its power morphism are defined over any `R`. The case `R = ℤ`, with the
canonical algebra structure, is Conrad's `G_m` over the integers.

The characteristic of a number field is `0`, so every `n > 1` is included. Conrad
gives no argument for non-openness; any proof is separate.

Also derived here: the names and the packaging of the unit and scheme-point clauses
into `PowerImageNotOpen`.
