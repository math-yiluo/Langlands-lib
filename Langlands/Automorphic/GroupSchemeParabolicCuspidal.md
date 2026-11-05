# All-proper-parabolic vanishing on actual adelic functions

Work over any number field `F`, with the existing actual affine group scheme
`G`. For every `IsRationalParabolicRadical P U`, the actual subgroup
rational quotient of `U` is compact. The proof extracts a parabolic
representative `P₀`, its smooth connected unipotent radical `U₀`, and the
composite `U₀ → P₀ → G`. Closedness gives affineness of `U₀`.
`RepresentedAdelicSubgroupQuotient` then transfers the public unipotent
compactness theorem along the actual continuous surjection. No compactness
assumption is added to a group structure.

Now take `hG : IsConnectedReductive G` and retain the explicit structural
premise `hPD : ParabolicDynamicStatement`. The canonical
`properRationalParabolicRadicals hPD hG` indexes every proper rational
parabolic subgroup functor, with properness on all tests. The preceding
argument proves compactness of every member's actual unipotent rational
quotient.

`parabolicCuspidalSubrepresentation` is the existing family-vanishing
construction for this canonical family. It consists of actual continuous
rational-invariant complex functions with convergent constant term, equal
to zero at every actual ambient adelic argument, for every proper rational
parabolic. Its measures and their measurable spaces are supplied explicitly.
Positive right translation preserves the space by the existing
constant-term action identity. The subtype inclusion into the unchanged
continuous ambient representation is injective and intertwines that action.

For finite Borel measures on those quotients,
`hasConvergentProperParabolicConstantTerm` proves absolute Bochner
convergence for every continuous ambient function, using the proved
compactness and continuity of the descended integrand.
`mem_parabolicCuspidalSubrepresentation_iff` therefore reduces membership
to all-parabolic vanishing alone. If two such finite-measure families differ
by scalar multiplication and each scalar has nonzero real value,
`parabolicCuspidalSubrepresentation_eq_of_smul_measure` proves that the
spaces coincide. The proof uses the existing integral-rescaling formula;
the nonzero scalar cancels in the reverse implication. This does not
construct invariant, normalized Haar, or probability measures.

The module also intersects this same space with the existing infinite
plot-smooth/common-open-finite-stabilizer subrepresentation, and with its
existing slice-wise polynomial-growth subrepresentation for a supplied
matrix representation. These retain the original carriers and translation
actions. They do not yet impose compact or enveloping-center finiteness,
uniform derivative growth, or square integrability, and are not an
identification with the full source automorphic-form space.

The all-proper-parabolic vanishing condition is motivated by Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Definition 6.5.1,
printed p.167, and (6.18)–(6.19), printed pp.167–168. The present continuous
space is an ambient construction before imposing all automorphic-form
conditions. In particular it is not the full almost-everywhere cuspidal
subspace of `L²([G])` in (6.20)–(6.21). Standard/maximal-parabolic reduction,
normalized measures, cuspidal square integrability, closedness, density,
finite volume and full general-linear comparisons remain separate
obligations. The parabolic/cocharacter existence premise remains explicit.
