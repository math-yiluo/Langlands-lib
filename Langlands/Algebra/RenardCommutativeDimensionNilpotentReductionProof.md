# Renard C.I: proof of the actual nilpotent-block reduction

`Langlands.Renard.commutativeDimensionNilpotentReduction.{u}` proves the
unchanged published
`CommutativeDimensionNilpotentReductionStatement.{u}`. It supplies all
three conjuncts for every finite-dimensional complex module in arbitrary
carrier universe, every natural tuple length and every original commuting
tuple. Only the third conjunct requires positive tuple length and bounds
on the canonical maxima at the supported actual block dimensions.

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, Appendix C.I,
printed p.275 / one-based PDF281. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Workers 709 and 16 read PDF281–282 and visually checked PDF281 in the
source work underlying this reduction; Worker 16 reread those pages and
visually checked PDF281 when preparing this proof. The opening proof
paragraph successively refines characteristic spaces, uses the finite-sum
power comparison and subtracts scalar parts. The following paragraph
defines the largest nilpotent-generated algebra dimension.

The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread on PDF18–19. It corrects the older edition's strict exponent
comparison to a non-strict comparison. The governing 2026 passage
already uses the non-strict comparison, including tuple length one.
No source-specific project or Library errata note was found.

## Comparison on every actual block

Fix the original tuple `a` and a complex eigenvalue tuple `χ`. The private
helper `blockDimension_le_canonicalMaximum` applies
`finrank_adjoin_le_nilpotentGeneratedMaxDimension` to the actual
`CommutingReduction.shiftedBlockTuple a hcomm χ` on
`CommutingReduction.jointSpace a χ`. Its entries commute and are
nilpotent by the published block construction. They are the original
restricted generators minus the scalar operators with eigenvalues `χ i`.

The equality `shiftedBlockTuple_adjoin_eq` identifies their unital
adjoin with the original `blockAlgebra a hcomm χ`. Scalars already
belong to the unital adjoin, so subtraction does not change that algebra
or add generators. The equality
`nilpotentDimensionTransport.{u, 0}.2` then identifies the maximum on this
actual block carrier with `nilpotentGeneratedPhi` at its complex
dimension. This is the required first conjunct. The comparison applies
to every `χ`, including unsupported zero spaces, and uses no positivity
or joint-decomposition premise.

## Sum over the exact supported subtype

The private assembly helper takes the exact joint-decomposition
proposition. The public theorem supplies it with the independently
published `commutingGeneralizedEigenspaceDecomposition.{u}`; it is not a
hypothesis of the resulting theorem.

For each supplied `Fintype` structure on exactly
`CommutingReduction.jointBlockIndex a`, the decomposition theorem bounds
the dimension of the original
`NilpotentFiltration.generatedAlgebra a` by the sum of the actual
`blockAlgebra` dimensions. Those algebras are the ranges of the original
evaluation restrictions, as established by `blockAlgebra_eq_range` in
the imported construction and used in the published decomposition proof.
Thus this comparison concerns the original generated algebra and its
actual images. Applying the first conjunct term by term gives the second
conjunct. The proof preserves the universal `Fintype` binder and sums
only over the original supported subtype.

## Conditional real-power conclusion

For positive `l`, write `r = 2 - Real.rpow 2 (1 - (l : ℝ))`.
The decomposition theorem proves finiteness of the supported subtype;
the proof installs `Finite` from that conclusion and obtains a `Fintype`
with `Fintype.ofFinite`. Its actual dimension identity, cast to the
reals, says that the sum of the supported block dimensions equals
`Module.finrank ℂ V`.

The second conjunct, also cast to the reals, first bounds the original
algebra dimension by the sum of canonical maxima. The stated estimates
on precisely those maxima bound this sum by the sum of the block
dimensions raised to `r`. The private helper `powerAssembly_fintype`
applies the independently published `commutativeDimensionPowerAssembly`
to `Fin (Fintype.card I)`. It uses the inverse of `Fintype.equivFin I`
to enumerate the supported index type `I`, then explicitly rewrites both
the sum of powers and the power's inner sum with `Equiv.sum_comp`.
Nonnegativity follows because block dimensions are natural numbers.
The resulting power of the total dimension is the required conclusion.

All subtraction and powers in this comparison are real operations.
The exponent comparison includes `l = 1`, where `r = 1`.

## Scope and provenance

The proof retains zero carriers, unsupported zero blocks, empty tuples
in the first two conjuncts, eigenvalue zero, and repeated or redundant
entries. Neither a decomposition, finite support, dimension sum,
faithfulness nor an original-algebra estimate is an additional premise.
All algebras are the actual unital adjoins. On the zero carrier the
supported sum is empty; the published decomposition and power results
cover this case.

These three explicit interfaces are derived from the source's opening
reduction and maximum definition, rather than three separately displayed
source lemmas. This proof establishes the reduction without asserting an
unconditional real-power bound for every canonical maximum. That bound,
the floor recurrence and numerical induction, and the remaining
whole-book program are separate obligations.

Worker 709 authored the reused conditional proof blueprint, including
the block comparison, finite-index power reindexing and assembly helper.
Worker 16 checked the published inputs and source correspondence,
applied the published joint proof to obtain the exact theorem, and
prepared this proof pair. The imported statement and supporting
published proofs are unchanged and retain their own authorship.
