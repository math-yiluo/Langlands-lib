# Compatible closure embeddings and the fixing subgroup

Author: Worker 134.

This module constructs `closureSubgroupEquiv K E`, a continuous multiplicative
equivalence from `Field.absoluteGaloisGroup E` to `E.fixingSubgroup`, for a
characteristic-zero field `K` and a normal intermediate field `E` of
`AlgebraicClosure K`, in an arbitrary common universe `u`. In particular it
applies to every finite Galois intermediate field. Finiteness of `E/K` is not
needed for this construction.

The embedding data are exactly an algebra structure from `AlgebraicClosure K`
to `AlgebraicClosure E` and its scalar tower over `K`. There is no assumption
that this embedding agrees with the canonical embedding of `E` into its own
algebraic closure. The local instance `canonicalClosureAlgebra` explicitly
selects that canonical `E`-algebra structure when forming field automorphisms
over `E`.

`closureSubgroupEquiv_subtype` proves that composing this equivalence with
subgroup inclusion is the existing `Field.absoluteGaloisGroup.mapOfAlgebra K E`.
`closureSubgroupEquiv_apply_val` gives the same certificate pointwise. These
identities concern the supplied embedding, with no choice or compatibility
premise added. This module is the group-level part of cohomology transport;
it does not construct the cohomology equivalence or prove degree-two exactness.

## Construction and certificates

`suppliedClosureEquiv` upgrades the supplied closure embedding to a
`K`-algebra equivalence. The upper closure is integral over `K`, hence over the
lower algebraic closure, and an integral extension of an algebraically closed
field has bijective algebra map.

Normality is used explicitly: `suppliedClosureEquiv_symm_mem` puts the inverse
image of each canonically embedded element of `E` back in `E`.
`suppliedClosureTwist` is the resulting `K`-automorphism of `E`.
`suppliedClosureEquiv_apply_subtype` expresses how the original closure embedding
acts on `E`, using the inverse of this twist. It need not fix the embedding
of `E` pointwise.

The commuting equation for normal restriction and this twist show that the
actual absolute Galois map lands in the fixing subgroup. `closureSubgroupMap`
restricts its codomain; continuity is inherited through the subgroup topology.
`closureSubgroupMap_commutes` records the field-level commuting square.
`closureSubgroupInverse` conjugates a fixing automorphism through the supplied
closure equivalence. The inverse-image membership lemma proves that the
conjugate fixes the canonical `E`. The two inverse identities follow by
cancelling the field equivalence in the commuting square; they define
`closureSubgroupMulEquiv`.

Characteristic zero is used only for the final topological construction:
the algebraic closure of `E` is then Galois, so its automorphism group is
compact for the Krull topology. The fixing subgroup is Hausdorff. The inverse
of the continuous bijection is therefore continuous, giving
`closureSubgroupEquiv`.

## Provenance and scope

This is a derived internal construction using Mathlib's algebraic closure,
normal restriction, Krull topology, and compact-to-Hausdorff inverse-continuity
results, together with the existing project closure coefficient module.
Its functorial convention agrees with Jean-Pierre Serre, *Local Fields*
(1979), Chapter X, sections 3–4, printed pages 154–156 / PDF pages 160–162:
a base-field-compatible embedding induces a group map in the opposite direction
characterized by the commuting square. Worker 134 read these pages directly.
The registered source is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`. No project errata
entry for this source was present when checked.

The implemented proof uses normality to handle each arbitrary compatible
embedding. It does not prove Serre's Proposition 5 asserting equality of
cohomology maps arising from different embeddings. No published module is changed.
