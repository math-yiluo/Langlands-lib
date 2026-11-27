# Tame-corestriction congruence for equivalent simple strata

`Langlands.BushnellKutzko.simpleStratumCorestrictionCongruence` proves the
published `SimpleStratumCorestrictionCongruenceStatement`. This is
Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), registered as `bushnell-kutzko-1993-admissible-dual-gln`,
(2.4.1)(ii)(c), printed p. 65 (PDF p. 77). The proof uses the common chain,
common `r`, simplicity, and equivalence in that statement. It takes the
field witness for `E = F[S.b]` and the tame corestriction `s` as supplied; it
does not choose a particular corestriction or add a hypothesis on `E/F`.

## A scalar in an intertwined coset

`exists_algebraMap_sub_mem_of_coset_intertwined` implements the coset conclusion of (2.4.11)
(printed p. 72, with proof on pp. 77–78; PDF pp. 84, 89–90) in splitting-basis
coordinates. For a local field `K` and a lattice chain `C`, it assumes that
for every unit `g` of `End_K(V)` there are `p, q ∈ C.endFiltration m` with
`g b − b g = g p + q g`. It concludes that `b` is scalar modulo
`C.endFiltration m`, without requiring a depth bound on `b` itself.

In a basis splitting `C`, each diagonal projection belongs to step zero,
so composing with two such projections extracts an elementary entry of
any endomorphism at step `m`. For distinct indices `i, j`, take `g` to
scale basis vector `i` by a uniformizer `π` and fix all other basis
vectors. This `g` belongs to step zero (its inverse need not). Thus
`g b − b g` belongs to step `m`, and its elementary `(i,j)` entry is
`(π − 1)` times that of `b`. The factor `π − 1` is a unit of the ring of
integers and can be removed. For distinct `i, j`, the transposition
of basis vectors `i, j` gives the equality `bⱼⱼ − bᵢᵢ = pⱼⱼ + qᵢᵢ`
in entry `(i,j)`, without needing the transposition to preserve the
chain. The filtration criterion for a nonzero diagonal elementary
coefficient is independent of its index, and a zero coefficient is
already in the filtration. This puts the diagonal differences at
step `m` as well. The basis is nonempty by strictness of the chain.
Subtracting the scalar given by one diagonal coefficient and summing
all elementary entries proves the conclusion.

## Intertwining after corestriction

Let `a = S.b`, `b = T.b`, and let `P` be the common chain filtration.
Equivalence gives `a − b ∈ P⁻ʳ`. Any `E`-linear unit `x` restricts to an
`F`-linear unit `g` commuting with `a`. Hence `g` intertwines `T` with
itself, with `a` as the witness in `T`'s coset. The published
`simpleIntertwining` factors `g = u y v`, with `y` commuting with `b`
and `u, v` in `T`'s intertwining neighborhood.

For a neighborhood unit `w`, `neighborhood_bounds` proves
`w − 1, w⁻¹ − 1 ∈ P¹` and `[b,w] ∈ P⁻ʳ`, where `[b,w] = b w − w b`.
In the bottom critical-exponent case `w = 1`. For finite exponent `k`,
put `d = −(r + k)`, so `d ≥ 1`. The product defining the neighborhood
lies in `Pᵈ` and its commutator with `b` lies in `Pᵈ⁺ᵏ = P⁻ʳ`: the first
factor centralizes `b` and the commutator obeys the product rule.
The unit-filtration characterization then gives the bound for the inverse.

The implemented forward calculation, corresponding to the direction
needed from (2.4.8)–(2.4.10) (printed pp. 71–72; PDF pp. 83–84), is

`g(a − b) − (a − b)g = [b,g] = L g + g R`,

where `L = [b,u]u⁻¹` and `R = v⁻¹[b,v]`. The difference
`[b,w] − [a,w] = [b − a,w − 1]` lies in `P¹⁻ʳ`. Multiplying `[b,w]`
by `w⁻¹ − 1` on either side also lands in `P¹⁻ʳ`. Thus
`L − [a,u]` and `R − [a,v]` are in `P¹⁻ʳ`. The corestriction kills
`[a,−]` and satisfies both relative bimodule laws, so `s(L), s(R)` are
images of elements of `P¹⁻ʳ` and

`x s(a − b) − s(a − b)x = x s(R) + s(L)x`.

The proof equips `E` with its finite-extension local-field structure and
uses `relativeLatticeChain` on the common chain. The last clause of
`tameCorestriction` places the images of `P¹⁻ʳ` at step `1 − r` of this
relative chain: its lattices have the same carriers as the common
chain. Applying `exists_algebraMap_sub_mem_of_coset_intertwined` in `End_E(V)` produces
`δ : E`. Restricting scalars identifies its scalar action with
`subfieldEmbedding` and gives the required ambient congruence.

This proves only the congruence clause: it uses neither the aggregate
T7 proposition, the reverse direction of the derived intertwining
calculation, nor the character and determinant conclusion of (2.4.11).
