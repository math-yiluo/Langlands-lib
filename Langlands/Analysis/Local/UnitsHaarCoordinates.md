# Haar measure on a compact open subgroup in additive coordinates

The module `Langlands.Analysis.Local.UnitsHaarCoordinates` proves two measure identities.

- `restrict_eq_smul_map_normalizedHaar`: in a second countable topological group `G` with
  its Borel structure, a left Haar measure `μ` restricted to a compact open subgroup `K` equals
  `μ K` times the pushforward under the inclusion of the normalized Haar measure
  `normalizedHaar K` of `K`.
- `map_val_restrict_compactOpen`: let `R` be a locally compact, second countable, Hausdorff
  topological ring whose value map `Units.val : Rˣ → R` is an open embedding. Let `μ` be a
  Haar measure on `Rˣ`, `νR` an additive Haar measure on `R` and `K` a compact open subgroup
  of `Rˣ`. Then `Units.val` carries `μ` restricted to `K` to the multiple
  `μ K * (νR (val '' K))⁻¹` of `νR` restricted to the image `val '' K`.

## Proof

For the first identity, pull `μ` back to `K` along the inclusion. The pullback is finite,
since `K` is compact, and left invariant, since left translation by an element of `K`
preserves `K`. It is therefore its total mass `μ K` times `normalizedHaar K`
(`haarMeasure_unique`). Pushing forward along the inclusion recovers `μ` restricted to `K`,
because the inclusion of an open set is a measurable embedding.

For the second identity, the composite `K → Rˣ → R` is an open embedding with range
`val '' K`. The Library theorem `Langlands.BaseChange.map_normalizedHaar_eq_restrict_of_units`
identifies the pushforward of `normalizedHaar K` along it with a normalized multiple of
`νR` restricted to that range. Combining with the first identity gives the stated constant.

## Role

This internal lemma expresses Haar measure on a group of units near the identity in the
additive coordinates of the ring. The local charts for the ordinary Weyl map
(`Langlands.Analysis.Local.WeylChartTorus`) use it for the ambient group and, through the
same Library theorem, for the torus.
