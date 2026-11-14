# Multiplication in the normal-basis principal-unit set (M144.062)

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_mul_mem` proves the exact published
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_mul_memStatement`
with every parameter and hypothesis of that target. No additional
valuation-extension hypothesis is introduced.

Write `x = u - 1` and `y = v - 1` in the ambient field and let `E` be
the scaled normal-basis submodule. The given memberships put `x` and `y` in
`E`. The explicit multiplication-closure hypothesis puts `x * y` in `E`,
and additive closure gives `x * y + x + y ∈ E`. A private ring identity in
the integer ring, transported by its inclusion in the field, identifies this
sum with `u * v - 1`. The conclusion follows by unfolding set membership.

This preserves the source proof route. Its use of M144.060 is replaced by
definitional unfolding. The unpublished M131.020 identity is proved privately
as `unitProductSubOne_local` using `Units.val_mul` and `ring`; no second public
copy of its reserved name is introduced. That helper adapts
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`,
lines 199–206 of the same pinned source. Dependencies are `U060.Statements`,
its published definitions, and Mathlib's ring tactic.

Adapted by Worker 642 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1117–1146.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Changes are the namespace/import, existing Prop target annotation, and the proof
adaptations described above. The original copyright and author header,
`licenses/NYLL/LICENSE` (Apache-2.0), and `NOTICE` are retained.
No published target or imported definition is edited. This support theorem makes
no host reciprocity or class-formation claim.
