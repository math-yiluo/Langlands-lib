# Actual square-zero Picard obstruction in relative module cohomology

Work with actual schemes in arbitrary universe `u`.
For `p : X → Spec R`, `i : Z → X` and any `n : ℕ`,
`relativeIdealCohomologyAddEquiv p i n` is the underlying additive equivalence
of the existing `relativeCohomologyRestrictScalarsIso` on `kernelModule i`.
Its source is the unchanged absolute `idealCohomology i n`; its target is
actual relative cohomology of that same kernel module. No finiteness,
properness, flatness or quasi-coherence premise is needed.

Let `b : Y → X` be a closed immersion with nilpotent actual ideal sheaf,
let `j : Z → Y`, and fix `φ : R → S`, `p : X → Spec R`,
`p' : Y → Spec S` and the actual equality
`b ≫ p = p' ≫ Spec.map φ`.
`idealCohomologyMap_relative` identifies the existing ambient
`idealCohomologyMap b j` with the canonical
`closedImmersionCohomologyMap` of the actual `kernelModuleMap b j`,
after applying the existing scalar-restriction isomorphisms on both sides.
It holds for every degree and every actual ideal-cohomology class.
Neither independently defined map is replaced by a transported substitute.

The proof supplies the actual topological isomorphism of the nilpotent
closed immersion. This is equal to `asIso b.base` since both have the
same forward map. Apply
`relativeHAddEquiv_closedImmersionCohomologyMap` to the inverse image of
the class under the unchanged `idealCohomologyAddEquiv`.
The source additive equivalence cancels its inverse; the target composite
is exactly the already defined ambient ideal-cohomology map. This gives
the claimed equality with the specified base-ring square retained.

For the obstruction results, additionally assume `j` is a closed
immersion and `Z` is compact. Given square-zero actual ideal sheaves for
`j` and `j ≫ b`, `obstructionMap_relative` proves the same naturality
for the actual Picard obstruction of every `y : PicardGroupoid.Group Z`.
The proof rewrites by the published
`SquareZeroAmbientObstructionNaturality.obstructionMap_naturality`
and then applies the preceding map identity.

`obstructionMap_factorization` retains an actual equality
`wi : j ≫ b = i`, where `i : Z → X` is another specified closed
immersion with square-zero kernel. Its source coefficient map is
`eqToHom (congrArg kernelModule wi.symm) ≫ kernelModuleMap b j`.
Thus the actual source kernel and obstruction are transported along
the specified factorization, with no change to the target obstruction.
The proof eliminates the equality and applies `obstructionMap_relative`;
the identity transport then simplifies.

The provenance is internal, from the actual relative module/Ext
comparison and the published ambient obstruction naturality. These
identities provide the general ideal and obstruction comparison used by
Artinian quotients. Identifying the Artinian specialization, constructing
formal families and proving the exact field Picard-stack atlas remain
separate obligations.
