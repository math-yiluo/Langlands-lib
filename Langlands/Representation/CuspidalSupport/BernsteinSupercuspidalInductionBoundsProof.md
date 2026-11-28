# Numerical bounds for induction from supercuspidal representations

`Langlands.CuspidalSupport.bernsteinSupercuspidalInductionBounds` proves
`BernsteinSupercuspidalInductionBoundsStatement.{uF, uV}`. For the standard
cuspidal data of a `BernsteinStandardFamily`, the theorem bounds the
composition length of \(i_P^G\rho\) by \(l(M)\) and the rank of the
intertwiner space from \(i_P^G\rho\) to \(i_{P'}^G\rho'\) by the number of
cosets \(wW_M\) in the matching Weyl set \(W(\rho,\rho')\).
[Statement](BernsteinSupercuspidalInductionBoundsStatement.md)

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.5.4, Theorem (printed pp. 173–174,
PDF pp. 179–180), registered as
`renard-2026-representations-groupes-reductifs-padiques` with SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The statement gives the correspondence between the source's Weyl notation and
the cosets used in Lean.

## Common inputs

`jointSpecialCompactBasisExistence` supplies the special compact and
simultaneous standard basis. `rationalSpecialVertexCompactInputs_of_jointBasis`
extracts the special-vertex data with the finite Cartan covering.
`rationalCuspidalExtractionInputs_of_specialVertexInputs` combines the
geometric filtration with the exclusion of cuspidal subquotients from
proper-standard induction inside each standard Levi. This exclusion plays the
role of VI.5.2 in both bounds.
[Joint basis](../../BruhatTits/SpecialCompact/JointBasisProof.md)
[Extraction](../Aubert/General/RationalCuspidalExtractionFromSpecialVertex.md)

The relative root system and the rational normalizer and centralizer
comparisons give a Coxeter system on the actual Weyl quotient through
`exists_rootSpanPointCoxeterSystem`. It provides the finite Weyl group, the
root-length comparison, and the identification of actual Levi Weyl
subgroups with the corresponding standard Coxeter subgroups.

## Length bound

The extraction inputs give cuspidal Jacquet factor extraction, which in
turn gives nonzero Jacquet detection on the irreducible subquotients of a
cuspidal induction along standard Levis associated to the source Levi.
`pointSupercuspidalInduction_compositionLengthAtMost_sourceCosets` bounds the
length using this detection and the exact Jacquet functors. Its summed
geometric-filtration bound is at most the number of source-Levi cosets whose
representatives take \(M\) to a standard Levi, the definition of \(l(M)\)
in the statement. The proof applies this lemma to the representation of the
literal Levi subgroup. Irreducibility is transported through
`leviRationalPointHomeomorph`, and cuspidality is part of the datum.
[Length bound](../Aubert/General/RationalSupercuspidalInductionLengthBound.md)

## Hom bound

`HomBound.bernsteinInduction_rank_intertwiningMap_le_card_minimal_of_inputs`
uses first adjointness, the geometric filtration and proper-standard
exclusion to bound the rank by the number of minimal representatives of
\(W_{M'}\backslash W_G/W_M\) in \(W(\rho,\rho')\).
[Hom bound](BernsteinSupercuspidalHomBoundFamily.md)

The proof maps each such representative \(w\) to \(wW_M\). Equality of
images implies \(w^{-1}w'\in W_M\), so \(w\) and \(w'\) belong to the same
double coset under the Levi Weyl identification. The Coxeter theorem
`minimalRepresentativeUnique_proof` then gives \(w=w'\). The injection
bounds the count of minimal matching representatives by the required count
of matching cosets. Casting the natural-number inequality to cardinals
gives the second conjunct.
[Coxeter uniqueness](../../Group/RelativeWeylMinimalUniqueProof.md)
