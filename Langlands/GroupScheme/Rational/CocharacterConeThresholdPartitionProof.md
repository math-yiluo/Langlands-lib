# Proof of the cocharacter cone threshold partition

`thresholdPartition` proves the corrected partition in the proof of Renard
VII.1.2. It works on the published nonnegative cocharacter cone modulo the
common annihilator of the selected characters. The finite residue set
accounts for the classes between the steps of the chosen rays.
[Statement](CocharacterConeThresholdPartitionStatement.md)

The product of the integral pairing maps has kernel equal to the common
annihilator. It therefore gives an injective coordinate map on the quotient.
Residue classes map into a finite product of integer intervals, with
coordinate \(\alpha\) bounded by \(0\le r_\alpha<d_\alpha\). This proves
finiteness of the residue set.

For a nonnegative class, divide its pairing with each \(\alpha\) by
\(d_\alpha\) to obtain a natural quotient \(m_\alpha\). Subtract the
cocharacter sum \(\sum_\alpha m_\alpha t_\alpha\) from a representative.
The pairings of the resulting class are exactly the Euclidean remainders.
This gives surjectivity of the map that adds a residue to a natural
ray sum. Dividing the pairings of an equality of such sums recovers
identical exponents, since the residue coordinates fall in the fundamental
intervals. The remaining equalities of pairings then identify the residues
by injectivity on the quotient.

The equivalence on the exponent tuples separates the coordinates
\(\alpha\) with \(m_\alpha\le n\) into \(J\). On \(J\) it keeps
\(m_\alpha\) as an element of \(\{0,\ldots,n\}\). Outside \(J\) it
records \(m_\alpha-(n+1)\). Composing with the residue and ray-sum
equivalence gives the map that adds the residue to the sum with exponents
\(b(\alpha)\) on \(J\) and \(n+1+\ell(\alpha)\) off \(J\), for every
natural cutoff \(n\). With no characters the coordinate function type is
a singleton. The injective quotient map then identifies every class with
zero, which satisfies both the residue and cone conditions. The finite
index set and both exponent functions are empty.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026. VII.1.2, the partition after (VII.1.2.2),
printed pp. 222–223 (PDF pp. 228–229), and the chamber quotient in V.3.24,
printed p. 117 (PDF p. 123). Registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
