# Membership of a supplied correction-product limit

Worker 519 proves the exact published target
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct_limit_memStatement`
with its source-adapted theorem name and complete telescope. The limit is a
supplied integer-ring unit, and convergence of the underlying integer-ring
partial products, closedness of the scaled lattice, and multiplicative closure
of the initial principal-unit set remain hypotheses.

Compose the given convergence with the continuous subtype inclusion from the
integer ring into the field. Subtract the constant one to obtain convergence
of the field-valued differences. Unfolding
`chosenNormalBasisPrincipalUnitSet` identifies membership with membership of
this difference in the scaled normal-basis lattice.
The M150.013 theorem imported from
`NormalBasisInfiniteProduct.U013.Proofs` puts every partial product in that
set. Mathlib's `IsClosed.mem_of_tendsto`, applied to the supplied closedness
hypothesis and this pointwise membership, puts the limiting difference in the
same lattice.

This is the argument of M150.016, lines 391–425 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`
at Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory` commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The direct closed-set application inlines the proof of M144.041, lines 674–679
of `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`.
Unfolding the carrier replaces the definitional equivalence M144.060,
lines 1096–1104 of that file. Neither reserved prerequisite theorem name is
declared here.

The pinned source is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registrations: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the Library.

Modifications: focused imports, namespace prefix, explicit exact-target
telescope, direct closed-set limit application, and definitional membership
unfolding. The original copyright and author header are retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. This result proves
membership of a supplied limit; it does not construct a limit or discharge a
host class-formation or reciprocity target.
