# Haar moduli across a closed normal subgroup

Author: Worker 1423.

Helper module for the proof of
`Langlands.HaarModulus.VectorFiltrationHaarModulusStatement`. Declarations are in
namespace `Langlands.QuotientIntegration`.

## Declarations

- `normalLeftQuotientHomeomorph H`: for a normal subgroup `H`, the Library's left-coset
  space `LeftQuotient H` (the quotient by `QuotientGroup.rightRel H`) is homeomorphic to
  the quotient group `G ⧸ H` by the identity on representatives, because the two coset
  relations agree for normal subgroups (`Subgroup.Normal.mem_comm_iff`).
- `quotientGroupAutomorphism H α hα`: a continuous automorphism `α` of `G` with
  `α x ∈ H ↔ x ∈ H` induces the continuous automorphism `gH ↦ α(g)H` of `G ⧸ H`
  (`QuotientGroup.congr`, continuity through the quotient map).
- `mulEquivHaarChar_eq_mul_quotientGroupAutomorphism`: let `G` be a locally compact
  Hausdorff group and `H` a closed normal subgroup, both carrying regular left Haar
  measures `μG`, `μH` that are also right invariant (unimodularity). Then for `α` as
  above,
  `mulEquivHaarChar α = mulEquivHaarChar (α|H) * mulEquivHaarChar (α on G ⧸ H)`,
  where `α|H` is the Library's `subgroupAutomorphism H α hα`.

## Proof

The Library's `compatibleMeasureExists` supplies a measure `ν` on `LeftQuotient H`
compatible with `μG` and `μH` (the quotient integral formula), and
`map_quotientAutomorphism` computes its pushforward under the automorphism induced by
`α` as `(δH / δG) • ν`, with `δG`, `δH` the moduli of `α` on `G` and on `H`. Transporting
`ν` along `normalLeftQuotientHomeomorph` gives a right-invariant regular measure `νQ` on
`G ⧸ H`; its inversion `νQ.inv` is a regular left Haar measure. The pushforward of
`νQ.inv` under the induced automorphism is again `(δH / δG)` times itself, so
`mulEquivHaarChar_smul_map` yields `δQ * (δH / δG) = 1`, after cancelling the positive
finite measure of a compact neighbourhood of the identity. Rearranging gives
`δG = δH * δQ`.

This is the standard multiplicativity of the module of an automorphism along a closed
normal subgroup; the route through the Library's quotient-integration interface is
internal.
