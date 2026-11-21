# The standard Euler polynomial of a supercuspidal representation

For a p-adic field, a standard pair whose first component is irreducible supercuspidal
of rank greater than one and whose second component is trivial on GL₁ has polynomial
`1`. The statement takes an actual certified automorphic pair polynomial and uses its
supplied nontrivial additive character and self-dual Haar measure.

The proof passes from the class certificate to the supplied representatives. The first
component is generic by supercuspidality. The trivial rank-one component is generic,
so the generic Langlands comparison identifies the chosen polynomial with the direct
JPSS polynomial. The supercuspidal unequal-rank formula then makes that polynomial
`1`. This supplies the lower finite Euler comparison at the distinguished place in
Arthur–Clozel's conductor proof. It uses the Library's implementations of Jacquet,
Piatetski-Shapiro and Shalika, Rankin–Selberg Convolutions, (8.1)(i) and (9.4),
printed pp. 443 and 458.
