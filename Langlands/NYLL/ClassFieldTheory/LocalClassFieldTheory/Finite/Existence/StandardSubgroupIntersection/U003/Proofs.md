# Finite abelian compositum standard norm containment: proof

This module proves
`Langlands.NYLL.LocalClassFieldTheory.finiteAbelianCompositum_normSubgroup_le_of_standard`
with the exact closed type of the published proposition
`Langlands.NYLL.LocalClassFieldTheory.finiteAbelianCompositum_normSubgroup_le_of_standardStatement`.
It unfolds that proposition and introduces its entire telescope in source order:
universe-zero `K`, the four instances `Field K`, `ValuativeRel K`,
`TopologicalSpace K`, and `IsNonarchimedeanLocalField K`, then
`H`, `ϖ`, `d`, `n`, `hϖ`, `hstandard`, `U`, `T`, `hUle`, and `hTle`.
There are no additional parameters or assumptions. In particular, both natural
numbers `d` and `n` may be zero.

## Meaning and implemented proof

The objects are the published actual finite abelian subextensions of
`intrinsicAbstractBase K`, their compositum, and their relative norm images in
the fixed part of `intrinsicAbsoluteUnits K`. Write
`e = baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)`.
The premises transport the two factor norm subgroups backwards using
`e.symm.toAddMonoidHom`. The conclusion transports `H.toAddSubgroup` forwards
using `e.toAddMonoidHom`.

For an element `x` of the compositum norm subgroup, the proof proceeds as follows.

1. Apply the published
   `ClassFormation.FiniteAbelianSubextension.normSubgroup_compositum_le_inf`
   (M296.032) to obtain membership in both factor norm subgroups.
2. Give each factor membership, with witness `x`, to the corresponding
   subgroup-map premise `hUle` or `hTle`. Thus `e.symm x` lies in the additive
   versions of both the degree-`d` unramified subgroup and the
   uniformizer-principal subgroup at `(1, n)`.
3. Apply the published
   `unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le` (M403.001)
   to place `Additive.toMul (e.symm x)` in the standard subgroup at `(d, n)`.
   This uses the supplied normalized valuation hypothesis `hϖ`.
4. Apply `hstandard` to obtain `e.symm x ∈ H.toAddSubgroup`, and use
   `e.apply_symm_apply x` to exhibit `x` in the forward image of that subgroup.

This is the original M403.003 proof route. No finite Galois variant M403.002,
local existence theorem, or norm-equality theorem is used.

## Source and modifications

The source is Naganori Yamaguchi's NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean#L133-L175).
The complete file was read, including namespace and scope declarations.
M403.003 has its docstring at lines 133–134, type at lines 135–154, and
proof at lines 155–175. The file SHA-256 is
`6a1c34851b46b17075888f452875eb49d31dcb167147dfde1eb2e3acc8cb99b1`.
The source is registered as `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`. No applicable NYLL erratum was
found in the Library errata notes.

The source theorem
`LocalClassFieldTheory.finiteAbelianCompositum_normSubgroup_le_of_standard`
becomes
`Langlands.NYLL.LocalClassFieldTheory.finiteAbelianCompositum_normSubgroup_le_of_standard`.
The `Langlands.NYLL` namespace prefix applies to its NYLL dependencies as well.
The published target supplies the complete source telescope. The proof unfolds
it and introduces all binders before the unchanged source proof body.
The original theorem docstring and copyright/author header are retained.
The broad source imports are replaced by the published target and its two
focused proof prerequisites. The unused source `universe u` and unnecessary
`noncomputable section` are omitted; the theorem remains closed and
universe-zero in `K`. No definitions, statements, instances, or imported
Library files are modified.

The adaptation retains Apache-2.0 attribution. The original
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) remain in the Library.

## Development checks

The focused proof compiles in the project Lean service with environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with zero errors and warnings.
Declaration inspection reports a theorem with no universe parameters and only
the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
The theorem's declared type is exactly the named closed statement.
These are development checks; independent proof acceptance additionally requires
the candidate's Lake build, exact-target validation, and semantic review.

All three imports are published Library modules. A textual comparison verifies
that the proof body after introducing the target telescope equals the pinned
source proof body modulo whitespace. Both files of the published target pair
are unchanged.
