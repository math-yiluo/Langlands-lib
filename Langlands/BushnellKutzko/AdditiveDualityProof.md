# Additive duality for hereditary-order filtrations

`Langlands.BushnellKutzko.additiveDuality` proves `AdditiveDualityStatement` in the independent
universes of the field and the vector space. The target is Bushnell–Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), (1.1.4)–(1.1.6), printed p. 22 (PDF p. 34,
`bushnell-kutzko-1993-admissible-dual-gln`). Bushnell's trace-duality and quotient-pairing argument
appears in *Hereditary orders, Gauss sums and supercuspidal representations of GL_N* (1987),
(1.11)–(1.13), printed pp. 189–190 (PDF pp. 6–7,
`bushnell-1987-hereditary-orders-gauss-sums`). The proof below uses the conductor
`𝔭_F` fixed in the published statement.

## The character annihilator

An element `t ∈ F` belongs to `𝔭_F` exactly when `ψ_F(at) = 1` for every `a ∈ 𝔬_F`. Membership
implies the character equality by the ideal property. For the converse, choose `s ∈ 𝔬_F` with
`ψ_F(s) ≠ 1`. If `t` lies outside `𝔭_F`, its multiplicative valuation is at least `1`. Hence
`t ≠ 0` and `s/t ∈ 𝔬_F`, so the equality fails for `a = s/t`.

The published `LatticeChain.mem_endFiltration_iff_trace_mul` identifies `𝔓^{1-i}` by the
condition `tr(bx) ∈ 𝔭_F` for all `x ∈ 𝔓^i`. Since `𝔓^i` is an `𝔬_F`-submodule, testing the
character on `ax` tests every `𝔬_F`-multiple of `tr(bx)`. The scalar criterion therefore gives
the equality `(𝔓^i)^* = 𝔓^{1-i}`. The lattice chain supplies finite dimensionality for the trace
criterion. [CorestrictionLatticeDual](CorestrictionLatticeDual.md)

## The finite additive pairing

For `i ≤ j`, `𝔓^i/𝔓^j` is the quotient of `𝔓^i` by the pullback of `𝔓^j` along its inclusion into
`End_F(V)`. Multiplication by `𝔭_F` shifts the filtration by one period `e`. Repeating the
shift `j - i` times gives `𝔭_F^{j-i}𝔓^i ⊆ 𝔓^j` since `e ≥ 1`. The quotient is finitely
generated over the finite ring `𝔬_F/𝔭_F^{j-i}`, using `LatticeChain.fg_endFiltration` and the
finiteness of the residue field. [RadicalFiltrationProof](RadicalFiltrationProof.md)

The annihilator at `j` makes `x ↦ ψ_A(bx)` descend to `𝔓^i/𝔓^j` for `b ∈ 𝔓^{1-j}`. The
annihilator at `i` then gives an injective additive map from `𝔓^{1-j}/𝔓^{1-i}` into the complex
character group of `𝔓^i/𝔓^j`. Applying the same injection at `(1-j, 1-i)` gives the reverse
cardinality inequality, because `AddChar.card_eq` counts the complex characters of each finite
additive group. This proves surjectivity of the pairing.

## The characters of the positive unit filtration

For `r < n` and `⌊n/2⌋ ≤ r`, take `i = r + 1` and `j = n + 1`. The map from `U^i` to the additive
quotient `𝔓^i/𝔓^j` is `LatticeChain.unitFiltrationToQuotient`, which sends `g` to the class of
`g - 1`. It is a group homomorphism because the product term `(g - 1)(h - 1)` lies in
`𝔓^{2i} ⊆ 𝔓^j`. Every `x ∈ 𝔓^i` gives a unit `1 + x` in `U^i` by
`LatticeChain.exists_mem_unitFiltration`. Its kernel consists of the units in `U^j`.
[UnitFiltrationQuotient](UnitFiltrationQuotient.md)

Pulling the paired additive character back along this map and lifting its values to `ℂˣ`
gives `ψ_b` on `U^i` for each `b ∈ 𝔓^{-n}`. The character is trivial on `U^j`. Testing on the
units `1 + x` for all `x ∈ 𝔓^i` identifies triviality on `U^i` with membership in `𝔓^{-r}`.
Conversely, `MonoidHom.liftOfSurjective` descends any homomorphism trivial on `U^j` along the unit
map. Its values in `ℂ` define an additive character of `𝔓^i/𝔓^j`. Surjectivity of the finite
pairing supplies a class in `𝔓^{-n}/𝔓^{-r}`, and any representative `b` gives the required formula
for the original homomorphism.
