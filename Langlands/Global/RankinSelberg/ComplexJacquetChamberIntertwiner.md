# The complex open-cell Jacquet intertwiner in the strict chamber

`chamberIntertwiner` is the complex-linear open-cell Jacquet integral
on the compact-finite vectors of the complex standard module. Its
integrating character has parameter \(a\). The theorem
`isComplexWhittakerIntertwiner_chamberIntertwiner` proves the
Library's intertwiner predicate for parameter \(-a\) when the inducing
list has the group rank and strictly decreasing real exponents.

Antidiagonal transpose reflection interchanges left and right
multiplication in the unipotent group and preserves the entry measure.
The resulting right Haar invariance allows translation in the open-cell
integral. The first-superdiagonal character is multiplicative there.
Translation by the inverse unipotent gives the character with parameter
\(-a\). Absolute integrability gives linearity, and associativity gives
compatibility with right compact translations. The chamber smoothness
theorem gives smooth values and compatibility with right derivatives.

For moderate growth the unitary translates of an inducing vector have
a uniform polynomial height bound. This follows from the standard
vector bound and submultiplicativity of the height, using the two
Frobenius norms. The integrable spherical majorant transfers this
bound to the Jacquet values. Consequently
`openCellIntegral_mem_complexWhittakerModel` puts every chamber value
in the exact Library model.

This realizes the chamber construction in Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §7.2, p. 47, with the upper Borel.
Continuation and comparison with arbitrary intertwiners remain open.
