# Proof of the failure of embedding for adelic punctured-line points

`Langlands.Global.adelicPunctureEmbedding` proves the published proposition
`Langlands.Global.AdelicPunctureEmbeddingStatement` in an arbitrary universe
`u`, importing its unchanged module
`Langlands.Global.AdelicPunctureEmbeddingStatement`. The statement records
Brian Conrad's remark in *Weil and Grothendieck approaches to adelic points*
(2011), printed pp.3–4, that `U(R) → X(R)` can fail to be a topological
embedding for the punctured affine line in the affine line over an adele ring.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The sequential proof below is a derived implementation of that remark,
using the published comparison homeomorphisms and arithmetic unit sequences.

## Generic reduction

`affineLinePunctureEmbeddingObstruction_of_tendsto` works over an arbitrary
commutative topological ring `S`. It takes a sequence of units whose values
tend to `1` and whose inverse values do not tend to `1`. It proves the three
clauses of `AffineLinePunctureEmbeddingObstruction S` as follows.

- Clause 2: suppose `Units.val` is an embedding for Mathlib's units topology.
  The sequence then tends to `1` in `Sˣ`, by the inducing characterization of
  neighbourhoods. Since `fun u => (u⁻¹ : S)` is continuous for the units
  topology (`Units.continuous_coe_inv`), the inverse values tend to `1`. This
  contradicts the hypothesis.
- Clause 1: suppose `Sˣ` is a topological group for the topology induced by
  `Units.val`. Neighbourhoods in this topology are pulled back from `S`
  (`nhds_induced`), so the sequence tends to `1` there. Continuity of inversion,
  followed by the continuous inclusion into `S`, makes the inverse values tend
  to `1`. This is again a contradiction.
- Clause 3: fix a base ring `R` and suppose that postcomposition with
  `affineLinePunctureι R` is an embedding of actual relative point spaces. By
  `affineLinePunctureUnitHomeomorph_val`, `Units.val` equals the composite of
  three maps. The first is the inverse of the homeomorphism
  `affineLinePunctureUnitHomeomorph R S` from punctured-line points to `Sˣ`. The
  second is the point map. The third is the affine-line coordinate homeomorphism
  `affineLinePointHomeomorph R S`. Homeomorphisms are embeddings and embeddings
  compose, so `Units.val` would be an embedding. This contradicts clause 2.

## Arithmetic cases

For a number field `K`, the sequence is `numberFieldUnitSequence K` from
`AdelicUnitSequence`. It has archimedean coordinates `1` and a uniformizer at
one finite place, and the place escapes to infinity. Its values tend to `1`
(`tendsto_numberFieldUnitSequence_val`). Its inverse values do not
(`not_tendsto_numberFieldUnitSequence_inv`). For a function field `F` over an
arbitrary constant field `k`, the sequence is `curvePlaceUnitSequence k F`,
with the corresponding two lemmas. The topological-ring instances on
`Adeles K` and `CurvePlaceAdeleRing k F` are the existing ones. No further
hypothesis is used.
