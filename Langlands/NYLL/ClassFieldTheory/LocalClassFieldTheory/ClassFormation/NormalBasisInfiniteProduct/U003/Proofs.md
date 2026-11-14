# Convergence of the normal-basis principal-unit sequence

Worker 519 proves the exact published target
`Langlands.NYLL.LocalClassFieldTheory.tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_boundStatement`
with its source-adapted theorem name and the complete original telescope.
The conclusion is convergence of the underlying integer-ring elements to one.

The private helper `m150_eventual_ideal_powers` proves that every neighborhood
of zero in the integer ring contains all sufficiently deep maximal-ideal
powers. Lift a subtype neighborhood to the field, take a valuation ball inside
it, and choose an irreducible element of the discrete valuation ring. Its
valuation is less than one, so `exists_pow_lt₀` produces a power with valuation
smaller than the ball radius. Mathlib's
`Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow` identifies that ideal
power with the valuation bound. Ideal-power monotonicity handles every deeper
power. All hypotheses required for these Mathlib results follow from the
supplied nonarchimedean local-field structure.

Apply the helper to a zero-neighborhood. For every sufficiently large `i`,
the M150.002 theorem imported from `NormalBasisInfiniteProduct.U002.Proofs`
puts `z i` in `principalUnits L (1 + i)`, so `z i - 1` lies in an ideal power
contained in that neighborhood. This proves convergence of the differences
to zero. Adding one proves convergence of the integer-ring sequence to one.
No completeness or existence of an infinite-product limit is asserted.

This follows M150.003, lines 95–117 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`
at Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory` commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The private helper combines the
arguments of M132.012 and M132.013, lines 160–198 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`.
It replaces the unpublished M132.013 theorem call without reserving or
publishing that prerequisite's adapted name.

The pinned source is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registrations: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the Library.

Modifications: focused imports, namespace prefix, explicit exact-target
telescope, and private combined neighborhood argument. The original copyright
and author header are retained; `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` apply. No host class-formation or reciprocity target is
claimed.
