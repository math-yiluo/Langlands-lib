# Centralizer intersection of sums of conjugated filtration steps

`endUnitConjugation` is conjugation by an ambient automorphism on the
endomorphism algebra, bundled as a linear equivalence over the base
ring of integers. Its inverse is conjugation by the inverse unit.

`endFiltration_sup_conj_inf_centralizer` computes the intersection with
the centralizer for a nonarchimedean local field `F` and a field
`E = F[β]` acting on `V`. The units of `E` preserve the lattice chain
as a set. For integer depths `i` and `j` and an `E`-linear automorphism `g`,
the intersection of `P^i + gP^jg⁻¹` with the adjoint kernel is
`Q^i + gQ^jg⁻¹`, where `Q^k = P^k ∩ ker(a_β)`.

The proof uses a basis of the relative vector space that splits both the
relative lattice chain and its translated chain. On either chain,
extending the values of a map on this basis linearly over the relative
field preserves each filtration step. Indeed, for a scalar coefficient
in a basis expansion, its valuation shifts the membership test in the
source and target lattice by the same amount. This extension is an
additive projection to the relative endomorphisms. Since `β` generates
`E`, an endomorphism commuting with `β` is `E`-linear and the projection
fixes it. Applying the projection to such a sum produces the required
relative summands. The reverse inclusion follows from the inclusions
of relative steps and preservation of the centralizer under conjugation.

`inf_sup_eq_of_deep_kernel_split` concerns two ambient submodules `M`
and `N`, a common kernel `K`, and deeper submodules `D ≤ M` and `E ≤ N`.
Subtracting the representatives in `(M ∩ K) + D` and `(N ∩ K) + E`
gives a difference in the common kernel. When that difference splits
into summands in `D ∩ K` and `E ∩ K`, the correction gives a common term
in `D ∩ E` and leaves a common term in `M ∩ N ∩ K`.

The sources are Bushnell–Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), source ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`,
(1.3.16), printed pp. 34–35 (PDF pp. 46–47), and its application to the
intersection computation (3.3.15)–(3.3.16), printed pp. 111–112
(PDF pp. 123–124). The proof implements the needed sum identity directly
with a common splitting basis.
