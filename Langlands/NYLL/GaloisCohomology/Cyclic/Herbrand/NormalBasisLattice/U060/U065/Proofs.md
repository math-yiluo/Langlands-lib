# Inverse-correction sums stay in the normal-basis lattice (M144.065)

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_mem` proves the exact published
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_memStatement`
with every parameter and hypothesis of that target. No additional
valuation-extension hypothesis is introduced.

The private helper `correctionPartialSum_mem_local` works for an arbitrary
integer-base submodule `E` with the given multiplication-closure property.
Negation preserves membership. Induction on the positive exponent then puts
each power `(-x)^(i+1)` in `E`. `Submodule.sum_mem` puts their finite sum in
`E`, including the empty sum. The public theorem specializes this helper to
the scaled normal-basis lattice and `x = u - 1`; the hypothesis `hu` has exactly
the needed membership type after definitional reduction.

The source theorem applies M144.036. That general proof is not published in
the workspace base, so this candidate proves the needed fact privately under
a different name. This helper follows the positive-power and finite-sum route
of the same source, lines 547–558 and 617–626. It imports only
`U060.Statements` and its published transitive dependencies. It asserts no
infinite-series convergence or inverse closure.

Adapted by Worker 642 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1191–1205.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Changes are the namespace/import, existing Prop target annotation, and the proof
adaptations described above. The original copyright and author header,
`licenses/NYLL/LICENSE` (Apache-2.0), and `NOTICE` are retained.
No published target or imported definition is edited. This support theorem makes
no host reciprocity or class-formation claim.
