# Proof of the open full-measure inverse-row tail locus

Author: Worker 230.

This module proves the published internal proposition
`Langlands.GeneralLinear.PadicMirabolicTailConullStatement` from
`Langlands.Group.GL.MirabolicTailConullStatement`. The closing theorem
`Langlands.GeneralLinear.padicMirabolicTailConull` has exactly
`PadicMirabolicTailConullStatement.{uF}` as its complete type. It keeps the
arbitrary field carrier universe and adds no assumptions or outer parameters.
The statement module and its imports are unchanged.

For every prime `p`, every `F : PadicField p`, every supplied
`T : F.TopologicalData` and every `a b : ℕ` (zero included), write
`G = GeneralLinear (a + b + 1) F.Carrier`. `G` carries the unit-group topology
induced by `T.topology` and the Borel measurable space `borel G` of that
topology. Let `L = Fin.last (a + b)` be the last index. The theorem proves two
things.

1. The set of `g` such that some entry `(g⁻¹) L (Fin.natAdd a j)`,
   `j : Fin (b + 1)`, is nonzero is open.
2. Every measure `μ` on `G` with `μ.IsHaarMeasure` gives measure zero to the
   set `E` of `g` with `(g⁻¹) L (Fin.natAdd a j) = 0` for all `j : Fin (b + 1)`.

The proof uses the actual inverse `g⁻¹` in the unit group, the actual last row
and all `b + 1` tail coordinates.

## Supplied-topology certificates

The proof introduces `T.topology` and the Borel space `borel G`, so
`BorelSpace G` holds by `rfl`. It then makes these published certificates
available as local hypotheses:

- `PadicField.TopologicalData.fieldT2` (`Langlands.LocalField.Topology`):
  the field is Hausdorff.
- `generalLinearTopologicalGroup` and `generalLinearLocallyCompactSpace`
  (`Langlands.Group.GL.Padic`): `G` is a locally compact topological group.
- `generalLinearSecondCountableTopology` (published in
  `Langlands.Representation.Smooth.SmallRealizationProof` and reexported by
  the imported `Langlands.Group.GL.CountabilityProof`): `G` is second countable.
- `IsTopologicalRing F.Carrier` is found by instance search from the stored
  `T.valuativeRel` and `T.localField`.

Every certificate uses exactly the supplied `T.topology`. No canonical
topology is substituted.

**Inner regularity.** For each Haar measure `μ`, `μ.InnerRegular` is found by
instance search. The term that elaboration produces uses Mathlib's
`Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaCompactSpaceOfBorelSpaceOfSigmaFinite`.
Its inputs are:

- pseudo-metrizability, from `TopologicalSpace.metrizableSpace_of_t3_secondCountable`
  (Urysohn metrization: a regular Hausdorff, second-countable space is
  metrizable). Regularity comes from the topological-group structure.
- sigma-compactness, from `SeparableWeaklyLocallyCompactGroup.sigmaCompactSpace`
  (separability follows from second countability).
- sigma-finiteness, from `Measure.IsHaarMeasure.sigmaFinite`.

The target statement assumes no regularity, normalization or null-locus
property.

## Openness

The map `g ↦ (g⁻¹) r k` is continuous for all indices `r` and `k`: compose
`Units.continuous_val` with continuity of inversion, then use
`Continuous.matrix_elem`. The open set is rewritten with `Set.ofPred_exists`
as a union over `j` of the sets `{g | (g⁻¹) L (Fin.natAdd a j) ≠ 0}`. Each of
these is open by `isOpen_ne_fun`.

## Null exceptional set

**Steinhaus step.** The generic lemma
`haar_null_of_forall_nhds_disjoint_translate` covers any locally compact
topological group with a Borel space. It states the following. Let `μ` be an
inner regular Haar measure and `E` a measurable set. Suppose every
neighbourhood `U` of `1` contains some `u` with `u * x ∉ E` for all `x ∈ E`.
Then `μ E = 0`.

The proof is by contradiction. If `μ E > 0`, Mathlib's Steinhaus theorem
`MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos` makes `E / E` a
neighbourhood of `1`. Its hypotheses are local compactness, inner regularity,
a Haar measure and a measurable set of positive measure. Choose `u` in `E / E`
moving `E` off itself. Writing `u = y / x` with `x, y ∈ E` gives `u * x = y ∈ E`,
which is a contradiction.

**Elementary unipotents.** Fix indices `i ≠ j` and a parameter `t`.
The imported `Langlands.GeneralLinear.transvectionUnit` from
[Transvection](Transvection.md) is shared with the intersection-Levi
character proof. `transvectionUnit i j hij t` is the actual unit with value
`Matrix.transvection i j t = 1 + t E_{ij}` and inverse
`Matrix.transvection i j (-t)`. Both unit laws follow from
`Matrix.transvection_mul_transvection_same` and `Matrix.transvection_zero`.

- `transvectionUnit_zero`: at `t = 0` the unit is `1`.
- `continuous_transvectionUnit`: the map `t ↦ transvectionUnit i j hij t` is
  continuous into `G`. Use `Units.continuous_iff`: each entry of the value and
  of the inverse is a constant or a constant plus `±t`.
- `inv_transvectionUnit_mul_apply_same`: in each row `r`, column `j` of
  `(transvectionUnit i j hij t * g)⁻¹` equals
  `(g⁻¹) r j + (-t) * (g⁻¹) r i`. Rewrite with `mul_inv_rev`, then apply
  `Matrix.mul_transvection_apply_same`.
- `exists_inv_apply_ne_zero`: every row of `g⁻¹` has a nonzero entry. If row
  `r` were zero, the `(r, r)` entry of `g⁻¹ * g = 1` would be zero.

**Small nonzero parameters.** `padic_exists_ne_zero_mem_nhds_zero T` proves
that every neighbourhood of `0` in `T.topology` contains a nonzero element.
Because `T.moduleTopology` makes the topology the `Padic p`-module topology,
the algebra map `Padic p → F.Carrier` is continuous (`continuous_algebraMap`).
So the preimage of the neighbourhood is a neighbourhood of `0` in `Padic p`.
`Padic p` is a nontrivially normed field, so this preimage contains a nonzero
`c` (Mathlib's `NeBot (𝓝[≠] 0)` instance). Its image is nonzero because a ring
homomorphism out of a field is injective (`map_ne_zero`).

**Covering.** For `i : Fin a`, let

`E i = {g | (g⁻¹) L L = 0 ∧ (g⁻¹) L (Fin.castAdd (b + 1) i) ≠ 0}`.

Take `g` in the exceptional set.

- `(g⁻¹) L L = 0`: the tail coordinate `j = Fin.last b` is `L`, by
  `Fin.natAdd_last`.
- By `exists_inv_apply_ne_zero`, row `L` of `g⁻¹` has some nonzero entry `k`.
- By `Fin.addCases`, `k` is either a head index `Fin.castAdd (b + 1) i` or a
  tail index `Fin.natAdd a j`. A tail index is impossible, since all tail
  entries vanish. So `g ∈ E i`.

Hence the exceptional set lies in `⋃ i, E i`. When `a = 0` this union is empty.
By `measure_mono_null` and `measure_iUnion_null`, it suffices that each `E i`
is null.

**Each piece is null.** Each `E i` is measurable: it is the intersection of a
closed set and an open set defined by continuous entries. Write
`c = Fin.castAdd (b + 1) i`. Comparing values shows `c ≠ L`, because
`i < a ≤ a + b`.

Given a neighbourhood `U` of `1`, continuity of the transvection map at `0`
and `transvectionUnit_zero` make `{t | transvectionUnit c L _ t ∈ U}` a
neighbourhood of `0`. The previous step gives a nonzero `t` in it, so
`u = transvectionUnit c L _ t` lies in `U`.

Suppose `g` and `u * g` both lie in `E i`. Then
`inv_transvectionUnit_mul_apply_same` with row `L` gives
`0 = 0 + (-t) * (g⁻¹) L c`. So `t = 0` or `(g⁻¹) L c = 0`, and both are
false. Thus `u` moves `E i` off itself. The Steinhaus step then shows that
`E i` is null.

## Provenance

This is a derived internal proof of an internal coordinate statement. It uses
only published Library topology certificates and standard Mathlib results:
Steinhaus's theorem, Urysohn metrization, inner regularity of sigma-finite
measures on sigma-compact pseudo-metrizable Borel spaces, the transvection
matrix identities, and continuity of the algebra map for module topologies.
It follows the route sketched in the task: a finite cover by pieces with a
nonzero head coordinate, translated off themselves by elementary unipotents
with small nonzero parameters. It constructs no parabolic or mirabolic product,
orbit identification, quotient measure or representation-theoretic object.
