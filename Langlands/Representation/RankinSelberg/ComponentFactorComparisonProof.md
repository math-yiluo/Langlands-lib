# Pair-factor comparison for actual irreducible components

Author: Worker 1747.

The theorem `Langlands.RankinSelberg.componentFactorComparison` proves the
unchanged proposition `ComponentFactorComparisonStatement`, with independent
field and four representation-carrier universes. For actual irreducible
components of two smooth ambient representations, any existing symmetric gamma
factors agree, and the component L-polynomial divides the ambient L-polynomial.
All factor certificates are premises. This is an internal supporting result;
it does not assert their existence or prove the square-integrable product formula.

The helper
`Whittaker.exists_coefficientModel_extension_of_smooth_subquotient` starts with
an actual invariant subspace and a surjective intertwiner to the component.
For a nonzero functional, smoothness descends to the invariant subspace and its
quotient. The occurrence of the nonzero functional then implies that the
character is locally constant. The published
`subquotientCoefficientModelInclusion` extends the functional to the smooth
ambient representation and preserves nonzeroness and the actual coefficient
functions. For the zero functional, the zero ambient functional has the required
coefficient-image inclusion. This argument works for a topological group whose
specified subgroup is a limit of compact subgroups.

`IsIrreducibleComponent.exists_coefficientModel_extension` extracts the actual
subspace and surjection from the component hypothesis and specializes this
helper to the upper-unipotent subgroup over the p-adic field. Its compact
containment is supplied by `upperUnipotent_isLimitOfCompactSubgroups`. Extending
each functional proves `IsIrreducibleComponent.whittakerSet_subset` and
`IsIrreducibleComponent.inverseWhittakerSet_subset`: every coefficient function
of the component belongs to the ambient intrinsic set, in the same function
space and for the same character.

`IsPadicPairGammaFactor.eq_of_components` takes nonzero standard and
inverse-character functionals from the component gamma certificate. In either
equal or unequal rank these are explicit premises of that certificate; the
reverse rank has no ordered certificate. Extend both functionals by the helper
and apply `IsPairGammaFactor.eq_of_model_le` to the nested coefficient images.
The residue cardinality is greater than one, as required for uniqueness of the
rational functional equations. This proof needs no full Whittaker-type premise
on the ambient representations.

`IsPadicPairLPolynomial.dvd_of_components` chooses one compatible quotient
measure from the component certificate and specializes both certificates at
that same measure. In equal rank, the intrinsic-set inclusions imply inclusion
of equal-rank zeta-value sets by `equalRankValuesOf_mono`. In unequal rank,
choose the block with `j = 0` and `k = r - n - 1`, transport the larger rank to
this block, and apply `unequalRankValuesOf_mono`. In both cases,
`Submodule.span_mono` gives inclusion of the Laurent spans and
`normalizedGeneratorSpanDivisibility` turns this into the displayed polynomial
divisibility. The reverse ordered rank is excluded by the certificate.

Finally, the theorem unfolds the symmetric relations according to the rank
order. When the first rank is larger or equal, it uses these two ordered
comparisons. When the second rank is larger, it interchanges both components
and both ambient representations before applying them. All p-adic relations use
the canonical topology, normalized absolute value, residue cardinality and Borel
structures from the statement.

The provenance is internal: smooth functional extension, the published
coefficient-image comparison for gamma equations, monotonicity of the actual
zeta-value sets and the published normalized Laurent-span divisibility lemma.
No further assertion from the literature is used in this proof.
