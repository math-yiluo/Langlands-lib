# Finite Euler denominators under ramified cuspidal pair twists

`cuspidalPairRamifiedEulerVanishing` proves
`CuspidalPairRamifiedEulerVanishingStatement`. For an actual cuspidal pair
with its smooth-dual presentations and a fixed finite place, it gives a
conductor threshold. Every Hecke character whose finite component at that
place meets the threshold makes both certified Euler denominators equal to
one. The ordinary pair twists its first member by the character, and the
dual pair twists its first member by the inverse character. The threshold
allows independent positive ranks for the two members.

Finite-place genericity gives Whittaker type for both members. The local
highly ramified vanishing theorem gives the polynomial-one certificate for
the actual determinant twist. The comparison of generic class factors with
integral Rankin–Selberg factors, and the local equivalence for the global
Hecke twist, identify this certificate with the chosen finite denominator.
The same argument applies to the contragredient presentations. Inversion
preserves multiplicative conductor, so the maximum of the two bounds works
for both polynomials.

This uses Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), Proposition 2.13, printed p. 404 (PDF p. 39), through
`whittakerTypeHighlyRamifiedLVanishing`. The retained copy is registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The two polynomial equalities can be used separately when matching the
forward and dual finite-place products of two completed equations.
