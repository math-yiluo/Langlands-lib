# Characters of subgroups of `U^{i+1}(𝔄)/U^{i+2}(𝔄)`

This module shows that a character of a subgroup of a positive unit filtration step, trivial
one step deeper, is the restriction of a function `ψ_b`. It supplies the element `b` in the
proof of Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (3.5.9), printed p. 121 (PDF p. 133): there `θψ_b` is the second character. The
literature ID is `bushnell-kutzko-1993-admissible-dual-gln`, with SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. The duality used is
(1.1.4)–(1.1.6) of the same source, printed p. 22 (PDF p. 34).

## Extension of characters of finite abelian groups

`AddChar.exists_extend_of_finite` states that every complex additive character of a
subgroup `M` of a finite abelian group `W` is the restriction of a character of `W`. Suppose
a character `ξ` of `M` is not a restriction. Then it has nonzero image in the quotient of the
character group of `M` by the restriction image. Mathlib's `AddChar.exists_apply_ne_zero`
gives a character `Ψ` of the character group of `M` that kills the restriction image and is
nontrivial at `ξ`. By the double-duality bijection `AddChar.doubleDualEmb_bijective`, `Ψ` is
evaluation at some `m ∈ M`. Every character of `W` is then trivial at `m`, so `m = 0` by
`AddChar.forall_apply_eq_zero`, and `Ψ` is trivial, a contradiction.

## The filtration quotient

`LatticeChain.finite_endFiltration_quotient` shows that `𝔓^i/𝔓^j` is finite for `i ≤ j`. A
power of the maximal ideal of `𝔬_F` maps `𝔓^i` into `𝔓^j`, so the quotient is a finitely
generated module over a finite quotient ring of `𝔬_F`. This argument also appears inside the
proof of `additiveDuality`.

## The main statement

`exists_elementCharacter_eq_of_trivial_on_succ` takes a nonarchimedean local field `F`, an
additive character `ψ_F` trivial on `𝔭_F` and nontrivial on `𝔬_F`, a lattice chain with
filtration `𝔓^k`, a natural number `i`, a subgroup `H ≤ U^{i+1}(𝔄)` and a homomorphism
`χ : H → ℂˣ` with `χ(h) = 1` for `h ∈ H ∩ U^{i+2}(𝔄)`. It gives `b ∈ 𝔓^{−(i+1)}` with
`χ(h) = ψ_b(h) = ψ_F(tr(b(h − 1)))` for all `h ∈ H`.

The map `g ↦ [g − 1]` (`LatticeChain.unitFiltrationToQuotient`) is a homomorphism from
`U^{i+1}(𝔄)` onto the finite group `W = 𝔓^{i+1}/𝔓^{i+2}`, with kernel `U^{i+2}(𝔄)`. Since `χ`
is trivial on the kernel of the restricted map, it descends to the image `M` of `H` in `W`.
The descended character extends to a character `Λ` of `W` by the extension statement above.
Then `Λ` composed with the quotient map is a character of `U^{i+1}(𝔄)` trivial on
`U^{i+2}(𝔄)`. The third clause of `additiveDuality`, at `n = i + 1` and `r = i`, writes it as
`ψ_b` with `b ∈ 𝔓^{−(i+1)}`. On `H` it agrees with `χ`.
