# Restricted standard decompositions inside rational-point Levis

Worker 165 supplies this internal adapter to the existing actual standard
subgroup family. Its only structural assertion is the explicitly supplied
`GroupScheme.StandardLeviIntersectionStatement`; this file does not prove that
assertion or change its status in the general reductive-group program.

`IsSemidirectDecomposition.subgroupOf` is a group-theoretic transfer. If
`P = M ⋉ U` in a group `H` and `P ≤ L`, the same three subgroups, read inside
`L` by `Subgroup.subgroupOf`, give a semidirect decomposition there.
Containment and normalization follow from the original conditions by
restriction. For each element of the restricted parabolic, the original
projection supplies its Levi factor. That factor belongs to `L` since
`M ≤ P ≤ L`. The original projection's residual-unipotent property proves
existence, and its characterization by `m⁻¹ p ∈ U` proves uniqueness.
Thus the proof establishes the full complement condition inside `L`.

`leviIndex_subset` records that mapping a finite subset of the subtype `J`
back to the ambient labels produces a subset of `J`. Its cardinality is
already preserved by the imported `card_leviIndex`.

Let `k : Type u` be any field, `G` an affine group scheme over `Spec k`, `T` a
commutative group scheme, `i : T.toGrp ⟶ G`, and `ν` a cocharacter of `T`.
The labels are literally `SimpleRoot i ν`, and `rootSet` is their actual
character image. The restricted construction additionally takes
`IsConnectedReductive G`, `IsMaximalSplitTorus i` and
`IsGenericCocharacter i ν`.

For a finite root subset `J` and `I : Finset J`, write `K = leviIndex J I`.
The lemma `rootSet_subset_iff` turns `K ⊆ J` into the exact character-subset
inclusion required by `StandardLeviIntersectionStatement`. Evaluate the
statement's first conjunct at the identity test object. It supplies the
containment, normality and complement data for

`L_J ∩ P_K = L_K ⋉ (L_J ∩ U_K)`.

`isSemidirectDecomposition_in_levi` uses normality to obtain the ambient
normalizer condition, reverses the supplied complement order, and applies
the group-theoretic transfer above. Restricting an intersection with `L_J`
to `L_J` gives the same subgroup as restricting the other factor. The result
is exactly the decomposition expected by `General.leviAlternatingOperator`:
`P_K.subgroupOf L_J`, `L_K.subgroupOf L_J` and `U_K.subgroupOf L_J`.

`standardLeviProjection` is the monoid homomorphism from that restricted
parabolic to that restricted Levi furnished by the derived decomposition.
It is constructed on actual rational points, without an arbitrary
decomposition parameter or a choice of a second indexing family.

No topology, finiteness, finite-length preservation, endpoint identification,
Weyl conjugation, unipotent product formula or representation-theoretic
identity is proved. In particular the second conjunct of the shared
intersection statement is unused. No characteristic, splitness of `G`,
quasisplitness, positive-rank or nonempty-root assumption is imposed.
The shared structural premise remains an obligation; this adapter does not
classify it as an allowed final external input.

The provenance is internal. The contribution follows by evaluation of the
existing shared statement and elementary subgroup restriction, with the
existing projection and complement characterizations. The source and
derived-formulation discussion for the structural assertion remains in
`GroupScheme/Rational/StandardLeviIntersectionStatement.md`; no new
literature claim is made here.
