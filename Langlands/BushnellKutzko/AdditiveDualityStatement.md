# Additive duality for a hereditary order (Bushnell–Kutzko 1993, (1.1.4)–(1.1.6), p. 22)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
(1.1.4)–(1.1.6), printed p. 22 (PDF p. 34; PDF page = printed page + 12), with the choice of
`ψ_F` and `ψ_A` from the notation list on printed pp. 19–20. For `(𝔓^n)^* = 𝔓^{1-n}`, BK93
cites Bushnell 1987 [Bu1] p. 190 (`bushnell-1987-hereditary-orders-gauss-sums`).

`AdditiveDualityStatement : Prop` is an unproved statement. A later `lean.proof@1` task will
prove it. It uses `Langlands.BushnellKutzko.LatticeChain`, `...UnitFiltration` and
`...AdditiveDual`.

## Quantifiers and hypotheses

For every nonarchimedean local field `F : Type u`, every `F`-vector space `V : Type v`, every
`𝔬_F`-lattice chain `𝓛 : LatticeChain 𝒪[F] F V`, and every additive character
`ψF : AddChar F ℂ` such that

- `ψF a = 1` for all `a ∈ 𝔭_F = 𝓂[F]`, and
- `ψF a ≠ 1` for some `a ∈ 𝔬_F = 𝒪[F]`.

These two hypotheses are BK93's "conductor `𝔭_F`" (p. 19: "`ψ_F` is null on `𝔭_F` but not on
`𝔬_F`"). BK93 also requires `ψ_F` to be continuous. That is automatic, because `ψF` is trivial
on the open subgroup `𝔭_F`, so it is not assumed. As in the other statements, the existence of
`𝓛` forces `V` to be finite-dimensional and nonzero.

Notation: `A = Module.End F V`, `ψ_A = traceCharacter ψF` (so `ψ_A(x) = ψF(tr x)`),
`𝔓^n = 𝓛.endFiltration n`, `U^n(𝔄) = 𝓛.unitFiltration n`, `S^* = additiveDual ψ_A S`, and
`ψ_b = elementCharacter ψ_A b`, the function `g ↦ ψ_A(b(g - 1))` on `G`.

## Conclusions

1. **`(𝔓^n)^* = 𝔓^{1-n}` for every `n ∈ ℤ`** (BK93 p. 22), as an equality of subsets of `A`.
2. **The isomorphism (1.1.5)–(1.1.6).** For natural numbers `n, r` with `r < n` and
   `n / 2 ≤ r` (natural-number division, so `n / 2 = ⌊n/2⌋`), that is, BK93's condition
   `n > r ≥ ⌊n/2⌋ ≥ 0`, the following hold.
   - (a) For every `b ∈ 𝔓^{-n}` there is a group homomorphism `χ : U^{r+1}(𝔄) →* ℂˣ` whose
     values (in `ℂ`) are `ψ_b(g)` and which is trivial on `U^{n+1}(𝔄)`. So `ψ_b` restricts to a
     character of `U^{r+1}(𝔄)/U^{n+1}(𝔄)`.
   - (b) For `b ∈ 𝔓^{-n}`: `ψ_b(g) = 1` for all `g ∈ U^{r+1}(𝔄)` if and only if `b ∈ 𝔓^{-r}`.
   - (c) Every homomorphism `χ : U^{r+1}(𝔄) →* ℂˣ` that is trivial on `U^{n+1}(𝔄)` has the
     form `χ(g) = ψ_b(g)` for some `b ∈ 𝔓^{-n}`.

## Why (a)–(c) express BK93's isomorphism

BK93 (1.1.5) asserts an isomorphism `(U^{r+1}(𝔄)/U^{n+1}(𝔄))^ ≅ 𝔓^{-n}/𝔓^{-r}`, given
explicitly by (1.1.6), `b + 𝔓^{-r} ↦ ψ_b` with `ψ_b(1 + x) = ψ_A(bx)` for `x ∈ 𝔓^{r+1}`. The
map `b ↦ ψ_b` is additive, because `ψ_A` is an additive character:
`ψ_{b+b'}(g) = ψ_b(g) ψ_{b'}(g)`. With this:

- (a) says the map is well defined from `𝔓^{-n}` to the character group of
  `U^{r+1}(𝔄)/U^{n+1}(𝔄)`;
- (b) says its kernel is exactly `𝔓^{-r}`, so it is injective on `𝔓^{-n}/𝔓^{-r}`;
- (c) says it is surjective.

The quotient `U^{r+1}(𝔄)/U^{n+1}(𝔄)` is finite. So every homomorphism to `ℂˣ` takes values in
roots of unity, which lie on the unit circle, and it is continuous. The group of homomorphisms
`U^{r+1}(𝔄) →* ℂˣ` trivial on `U^{n+1}(𝔄)` is therefore BK93's Pontryagin dual. Characters are
stated on `U^{r+1}(𝔄)` with a triviality condition rather than on a quotient group, so no
quotient construction or normality proof is needed in the statement. The intermediate
isomorphism `U^{r+1}(𝔄)/U^{n+1}(𝔄) ≅ 𝔓^{r+1}/𝔓^{n+1}`, `x ↦ x - 1`, which BK93 uses to derive
(1.1.5), is not stated separately.
