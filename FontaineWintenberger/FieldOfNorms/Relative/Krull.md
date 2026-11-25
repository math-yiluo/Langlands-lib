# The Galois correspondence of the relative field of norms is a homeomorphism

Module `FontaineWintenberger.FieldOfNorms.Relative.Krull`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field with perfect residue field, `L/K` an infinite separable APF extension and `M/L` a separable algebraic extension. The group isomorphism `RelFieldOfNorms.autEquiv` between the automorphisms of `M` over `L` and the automorphisms of `RelFieldOfNorms K L M` over the norm field `FieldOfNorms K L` is shown to be a homeomorphism for the Krull topologies on both sides. This is the topological part of Wintenberger's Corollary 3.2.3.

## Main definitions

* `RelFieldOfNorms.finiteImage K L M Q`: for a finite subextension `Q` of `M/L`, the image of `FieldOfNorms K Q` in `RelFieldOfNorms K L M`, as an intermediate field over `FieldOfNorms K L`. Membership is unfolded by `mem_relFieldOfNormsFiniteImage`.
* `RelFieldOfNorms.krullEquiv`: `RelFieldOfNorms.autEquiv` as an isomorphism of topological groups (`≃ₜ*`). `RelFieldOfNorms.krullEquiv_toMulEquiv` and `RelFieldOfNorms.krullEquiv_apply` say that the underlying isomorphism and its action are unchanged.

## Main results

* `RelFieldOfNorms.map_eq_on_stage_iff`: two `L`-endomorphisms `s`, `t` of `M` induce the same map on the image of the stage `Q` if and only if they agree on `Q`.
* `RelFieldOfNorms.finiteImage_finite`: `finiteImage Q` is finite over `FieldOfNorms K L`.
* `RelFieldOfNorms.autEquiv_mem_fixingSubgroup_iff`: `autEquiv σ` fixes `finiteImage Q` pointwise if and only if `σ` fixes `Q` pointwise.
* `RelFieldOfNorms.exists_finiteImage_ge`: every intermediate field of `RelFieldOfNorms K L M` that is finite over `FieldOfNorms K L` lies in some `finiteImage Q`.
* `continuous_relFieldOfNormsAutEquiv`, `continuous_relFieldOfNormsAutEquiv_symm`: `autEquiv` and its inverse are continuous.

## Proofs

A basis of neighbourhoods of the identity for the Krull topology is given by the fixing subgroups of finite subextensions (`krullTopology_mem_nhds_one_iff`). The finite images are finite and cofinal among the finite subextensions of the limit, and `autEquiv` matches the fixing subgroup of `Q` with that of `finiteImage Q`; this gives continuity in both directions at the identity, hence everywhere. The stage criterion `map_eq_on_stage_iff` rests on `RelFieldOfNorms.algMap_of_factor` and `RelFieldOfNorms.finiteHom_faithful` from `FontaineWintenberger.FieldOfNorms.Relative.Hom`.

## Remarks

`M/L` is any separable algebraic extension; it is not assumed Galois, so the automorphism groups are those of Mathlib's Krull topology on `M ≃ₐ[L] M` for a general algebraic extension.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3, Corollary 3.2.3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Relative/Krull.lean` (SHA-256 of the source file `7776c806d7971a2c57427c4c62ca42a496cf23aa89642c19f00cdcbd081f4241`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
