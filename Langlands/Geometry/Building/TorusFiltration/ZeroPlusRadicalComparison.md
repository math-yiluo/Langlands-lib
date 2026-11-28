# The standard zero-plus group and the special-fibre radical

`exists_standardZeroPlus_radicalPreimage` identifies the intersection
of the strictly positive standard union and the connected Néron
integral points of a torus over `inertiaFixedField F`. The resulting
group is the inverse image of the rational points of the unipotent
radical of the connected Néron special fibre. Each section in this
preimage maps to a shallow induced image.

Henselian lifting and generic commutativity give commutativity on
residue points. `isCommMonObj_of_commuting_points` gives commutativity
of the smooth affine fibre. `solvableTorusQuotient` and the greatest
subgroup property of `IsUnipotentRadical` then characterize the
radical points as the points killed by powers of the residue
characteristic \(p\). The split torus quotient has injective
\(p\)-power maps and `exists_hasUniformPowerExponent_of_isUnipotent`
supplies the power in the radical.

The smooth extension of the bounded induced norm cover into the
connected Néron model decomposes each target section into a shallow
induced image and a section killed by an exponent prime to \(p\).
The shallow image lies in a positive minimal congruent model and
has \(p\)-primary reduction by `minimalCongruentPositiveUnipotent`.
It also lies in the standard term by standard functoriality.
If the original point lies in a positive standard term, its torsion
part lies in a positive geometric character subgroup. The character
calculation `eq_one_of_positiveDepth_of_pow` makes that part trivial.

Conversely, if the original reduction is \(p\)-primary, then the
torsion part reduces to the identity by the coprime power identity.
`IntegralModel.pow_pow_mem_congruenceKernelAt` puts its \(p\)-powers
arbitrarily deep in the congruence tower. Coprimality puts the torsion
part itself in all those kernels, and
`IntegralModel.eq_of_reductionAt_eq` proves it is the identity.
Thus the original section comes from the principal part of the norm
lift and lies in a shallow induced image.

The standard radical description is Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Proposition B.9.1, printed pp. 684–685,
PDF pp. 715–716. The proof uses the bounded norm cover from Definition
2.5.13 and the proof of Corollary B.8.7, together with the principal
and torsion factors of its units.
