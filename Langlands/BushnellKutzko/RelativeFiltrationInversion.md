# Inverse steps of the relative filtration

This module proves the relative multiplication identity used in the
adjoint lifting proof for Bushnell–Kutzko (1993), (1.4.7) and (1.4.10),
printed pp. 36–38. The identity concerns the filtration on the
intersection with `End_E(V)`, which the source identifies in (1.2.4),
printed pp. 24–25. The normalizing action of a nonzero relative scalar
shifts every lattice by a fixed integer.

For a coset of an `E`-subspace that avoids zero, a base-field linear
section of the quotient realizes the quotient as an endomorphism with
that subspace as kernel. The endomorphism has a filtration bound by
uniformizer clearing, and its constant nonzero value on the coset
bounds the possible depths of coset representatives. A representative
at greatest depth therefore belongs to every lattice meeting the
coset. After scaling by a nonzero relative scalar, the same property
holds in the scaled coset.

A finite linearly independent family splits the chain when each
summand of a linear combination belongs to every lattice containing
the sum. If the span is proper, adjoining such a representative of a
nonzero coset preserves this property. The dimension over `E` bounds
the lengths of these families, so one of greatest length spans and
forms a splitting basis.

Strictness gives a vector at each exact depth. Splitting its basis
expansion gives a scalar multiple of a basis vector at that depth.
For each basis vector at depth `i`, choose such a multiple at depth
`i - m`. The two rank-one maps sending the first coordinate line to
this vector and the second line back to the original basis vector
belong to steps `-m` and `m`, respectively, with inverse coefficients
in the two maps. Their composite is the projection onto the original
basis line. Summing these products gives the identity in `Q(m) · Q(-m)`.
Each factor commutes with `β` by `E`-linearity.
