# Actual orbit packet data for the full Levi

`OrbitPacketData.ofFullLevi` constructs the scalar and continuation data
used by the actual semistandard synthesis at an index whose Levi is the
whole rational-point group. It takes the displayed cocharacter
presentation, irreducible admissible inducing representative, and compact
open subgroup.

The cocharacter presents the full Levi, so its two opposite parabolics
are the whole group. Both compact factorizations use the identity
element of the compact. `forwardContinuationOfLeviEqTop` and
`reverseContinuationOfLeviEqTop` have constant numerators and
denominator one at the specified compact. Their full-domain lemmas
allow both continuation regions to be the entire complex unramified
parameter group. The inducing representation stays irreducible under
pullback to the displayed literal Levi. The full-Levi induction theorem
then gives irreducibility on that entire parameter group. Finally,
`rationalFunctionUnitaryRegular_inv_of_levi_eq_top` proves regularity of
the inverse of the exact composition scalar stored in the packet.

This is the full-Levi specialization of the intertwining and inverse
scalar used in Waldspurger, *La formule de Plancherel pour les groupes
p-adiques* (2003), IV.3, printed pp. 285–287 (PDF pp. 51–53), and
V.2, printed pp. 292–293 (PDF pp. 58–59).
The `OrbitPacketData` packaging is derived for the VI.3 synthesis.
[Original publication](https://doi.org/10.1017/S1474748003000082)
