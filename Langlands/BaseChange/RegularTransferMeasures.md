# Comparing the measures in regular concordance

`IsCompatible.eq_smul_of_subgroup_smul` derives the comparison of two actual quotient measures from the Library's compact-test Weil formula. For a closed subgroup, `realQuotientPositiveLifting` lifts each compactly supported continuous real test on the quotient to a compact test on the group. Averaging this lift with the first subgroup measure gives the quotient test. Averaging with the rescaled subgroup measure multiplies that test by the same scalar. Compatibility identifies both resulting integrals with the ambient group integral. Regular measure extensionality then gives `ν₁ = c • ν₂` when `μ₂ = c • μ₁`. At `c = 1` this gives uniqueness for fixed subgroup and ambient measures.

`normConjugator_on_sigmaCentralizer` compares two witnesses of norm association.
A twisted centralizer element commutes with the norm by the norm conjugation
formula. The two witnesses differ by an element of the centralizer of the
scalar-extended ordinary element. Under the stated commutativity assumption they
therefore act identically on the twisted centralizer.

`ConcordAt.of_associated_pair` uses Haar uniqueness on the twisted centralizer
to compare two choices of Haar measure by a positive scalar. The two
associations and the measurable embedding of the ordinary centralizer give
the same scalar on that centralizer. Inverse rescaling of the two quotient
measures and cancellation then turn a single normalized equality into the
universal equality in `ConcordAt`. The same measure argument gives
`orbitalIntegral_eq_zero_of_compatible` for the vanishing clause.

This is an internal measure comparison used for the rescaling of centralizer measures in Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique non nulle* (2011), I.2.5 and I.2.8, printed pp. 17 and 21. The compact-test argument uses the Library's definition of compatibility.
