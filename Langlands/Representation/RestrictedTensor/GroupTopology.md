# Finite-coordinate topology of restricted groups

This module constructs an internal topological API for the actual cofinite
restricted product `Langlands.RestrictedTensor.RestrictedGroup G H`. The index
type has universe `uI` and the local group types have independent universe `uG`.
The reference objects `H i` are subgroups of the given groups `G i`. All
topologies are the original Mathlib restricted-product, product, and subgroup
topologies.

The construction supports the finite-coordinate separation used in the
project's restricted-tensor factorization work. Its definitions and proof route
are internal derived mathematics, not a transcription of a named theorem in
the literature. The foundations used here are Mathlib's
`Topology/Algebra/RestrictedProduct/Basic`,
`Topology/Algebra/RestrictedProduct/TopologicalSpace`, product-neighborhood
theorems, and total-disconnectedness transfer through a continuous injection.
No additional mathematical axioms are introduced.

## Finite-coordinate equivalences

For a finite set `S`, `ComplementGroup H S` is the actual restricted product
indexed by `{i // i ∉ S}`. `complementProjection` is restriction to these
coordinates, constructed with `RestrictedProduct.mapAlongMonoidHom`. Injectivity
of subtype inclusion gives the required cofinite-filter convergence.

`finiteAssemble` puts the finite family and the complementary restricted-product
element back into one family. The set of nonreference coordinates is contained
in the union of `S` and the image of the complementary element's finite
exceptional set. `finiteSplitMulEquiv` proves the two inverse laws and
multiplicativity coordinatewise.

If each local group is a topological group and every `H i` is open,
`finiteSplitEquiv H hH S` is the continuous multiplicative equivalence

```text
RestrictedGroup G H ≃ₜ* (∀ i : S, G i) × ComplementGroup H S.
```

The forward map is continuous by coordinate evaluation and
`RestrictedProduct.mapAlong_continuous`. For the inverse, the auxiliary
`splitIntegralSubgroup` is open: its first factor is a finite intersection of
open coordinate conditions, and its second factor is the all-reference
subgroup. On this subgroup the inverse factors continuously through the
product `∀ i, H i` and `RestrictedProduct.structureMap`. Continuity at the
identity then gives continuity of the multiplicative inverse map everywhere.
This argument does not assume compactness.

The four `finiteSplitEquiv_fst`, `finiteSplitEquiv_snd`,
`finiteSplitEquiv_symm_apply_mem`, and
`finiteSplitEquiv_symm_apply_not_mem` lemmas give all coordinate formulas.
There are no nonemptiness hypotheses on `S`, its complement, or the index
type, so the empty and finite index cases are included.

`singletonCoordinatesEquiv` evaluates a product over a singleton.
`singletonSplitEquiv H hH i` consequently has target
`G i × ComplementGroup H {i}`. Its `fst`, `snd`, and inverse coordinate lemmas
give the corresponding formulas. In particular,
`singletonSplitEquiv_symm_mulSingle` proves exactly

```text
(singletonSplitEquiv H hH i).symm (g, 1)
  = RestrictedProduct.mulSingleMonoidHom H i g.
```

Thus the inverse has the local-factor-first orientation needed by two-factor
representation arguments and uses the existing Mathlib insertion.

## Locally profinite properties

`restrictedGroup_t2Space` exposes Mathlib's Hausdorff instance.
`restrictedGroup_isTopologicalGroup` supplies the existing topological-group
instance from openness of the reference subgroups.
`restrictedGroup_locallyCompactSpace` applies
`RestrictedProduct.locallyCompactSpace_of_group` when the local groups are
locally compact topological groups and all reference subgroups are compact
and open.

The `restrictedGroup_totallyDisconnectedSpace` instance transfers total
disconnectedness from the ordinary product along the continuous injective
coordinate map. It does not assert that the restricted-product topology is
the subspace topology from that product.

All these declarations apply unchanged to the complementary family
`fun i : {i // i ∉ S} => G i` with reference subgroups `fun i => H i`.
In particular the complement has universe `max uI uG`. Finite products of the
local groups use Mathlib's ordinary product instances. No countability,
sigma-compactness, or measure hypotheses occur.

## Compact tails and identity neighborhoods

`tailReferenceSubgroup H S` consists exactly of the elements equal to `1`
on `S` and lying in `H i` off `S`. This is the equivalence
`mem_tailReferenceSubgroup`. Every such element lies in the reference subgroup
at every coordinate, as recorded by `tailReferenceSubgroup_integral`.

`tailReferenceMap` maps `∀ i, H i` into the restricted product by replacing
the coordinates in `S` by `1`. It is continuous, and its range is precisely
the tail subgroup. If each `H i` is compact, the product is compact, so
`isCompact_tailReferenceSubgroup` follows by taking its continuous image.
Neither Hausdorffness nor openness is needed for this compactness proof.

For open reference subgroups, `exists_tailReferenceSubgroup_subset` says that
every neighborhood of the identity contains a tail subgroup for some finite
`S`. The proof pulls the neighborhood back through the open structure-map
embedding using `nhds_eq_map_structureMap`. The ordinary product neighborhood
filter supplies finitely many coordinate restrictions via `Filter.mem_pi'`.
A tail element has value `1` on each of these coordinates, so it satisfies
all those restrictions. Compactness is not used in this extraction.
`exists_tailReferenceSubgroup_le` specializes it to an arbitrary open subgroup.
These conclusions do not assert that the tail subgroup is open.

The smooth-vector consequence is in the companion `TailSmooth` module, so
this topological construction does not import the smooth-representation
definitions.
