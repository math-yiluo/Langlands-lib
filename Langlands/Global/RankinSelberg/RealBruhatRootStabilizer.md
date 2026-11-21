# Simple-root stabilizers on the lower real Bruhat cells

`Langlands.Global.RankinSelbergGlobal.RealBruhatRootStabilizer.RealBruhatRootStabilizerStatement`
constructs a paired root action fixing each point in a real upper Bruhat cell
whose permutation differs from the order reversal. The left factor is upper
unipotent. The right factor is upper unipotent and carries the standard
character of one adjacent root. The paired infinitesimal action on ambient
matrices is nilpotent.

A permutation with only adjacent descents is the reversal, so a lower cell
has an adjacent ascent. Write the point using the Library's Bruhat coordinates
`b * p * v`. Conjugate the negative root parameter by `b * p` on the left and
the positive parameter by `v⁻¹` on the right. The ascent makes the left conjugate
upper unipotent. The two root parameters cancel at the point. Conjugation by
the unipotent `v` preserves the adjacent-entry sum, so the right character is
the scaled additive character of the root parameter. The companion derivative
identity gives its nonzero infinitesimal value for every nonzero scale.

The two matrix generators are square-zero. Left and right multiplication
commute, so the sum of these multiplication operators is nilpotent. The
companion lemmas identify that sum with the derivative of the paired action
on each ambient matrix and give the strict upper conditions on its generators.

This internal result uses the Library's Bruhat coordinates, elementary
transvections and real Whittaker character formula. It supplies the stabilizer
for removing distributions supported on the lower cells.
