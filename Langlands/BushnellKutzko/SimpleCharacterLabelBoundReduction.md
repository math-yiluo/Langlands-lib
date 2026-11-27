# Reduction of the label bound for simple characters (BK94 (2.5))

Source: C. J. Bushnell and P. C. Kutzko, *Simple types in GL(N): computing conjugacy
classes* (1994), `bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa` (cited as BK94; PDF
page of the proceedings volume = printed page + 13): Corollary (2.5), printed p. 120
(PDF p. 133), whose proof reads "This follows from (2.3), (1.4) and (1.14)"; Theorem
(2.3), printed p. 119; Proposition (1.14), printed p. 116. Also C. J. Bushnell and
P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73` (cited as BK93):
(3.5.1), printed p. 117 (PDF p. 129).

## The reduction statement

`SimpleCharacterLabelBoundReductionStatement` is the proposition

`C → Λ → Γ → I → B`,

with universe parameters `uF, uV` (the universes of the field `F` and of the space `V`)
in all five propositions. Here:

- `C` is `SimpleCharacterClassCoverStatement` (the existence part of BK94 (2.3)): for a
  lattice chain `L` and levels `0 ≤ m < n` there is an assignment `Φ` of a pair
  `Φ(S) ∈ Ĉ(𝔄,m,β)` to every simple stratum `S = [𝔄,n,m,β]` on `L`, such that strata
  whose parameters are `U(𝔄)`-conjugate modulo `𝔓^{-m}` receive `U(𝔄)`-conjugate pairs,
  and every pair of `S^m_n(𝔄)` is `U(𝔄)`-conjugate to some `Φ(S)`.
- `Λ` is `SimpleStratumLabelStatement` (the upper-bound half of BK94 (1.14)): for a
  principal order in dimension `N ≥ 1` there is a map `ρ` from the simple strata on `L`
  at levels `m < n` to `labelSet m n e(𝔄) (N/e(𝔄)) q_F`; equal labels give strata that
  are `U(𝔄)`-conjugate up to equivalence, and `d(ρ S) = f(F[β]|F)`,
  `e(F[β]|F) · e(ρ S) = e(𝔄)`.
- `Γ` is `SimpleCharacterConjugationStatement`: conjugating a simple stratum and its
  lattice chain by `g ∈ GL(V)` gives a simple stratum on the transported chain, with
  generated-field parameter `g β g⁻¹`, character set equal to the image of `Ĉ(𝔄,m,β)`
  under `CharacterPair.conj g⁻¹`, and the same ramification index and residue degree.
- `I` is `SimpleCharacterInvariantsStatement` (BK93 (3.5.1)): two simple strata on the same
  chain and levels with a common simple character pair have the same critical exponent,
  ramification index and residue degree.
- `B` is `SimpleCharacterLabelBoundStatement`, the label bound of BK94 (2.5).

The five propositions are Library statements in their own modules. This module proves the
implication `simpleCharacterLabelBoundReduction`; it does not prove the four premises.
Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

The printed proof of (2.5) cites (1.4), (1.14) and (2.3); the reduction has no separate
premise for (1.4). Corollary (2.5) gives both `f(F[β]|F) = d(s[θ])` and
`e(F[β]|F) = e(𝔄)/(℘(𝔄) e(s[θ]))`. A principal order has `℘(𝔄) = 1`, so the second
formula takes the multiplicative form `e(F[β]|F) · e(σ θ) = e(𝔄)` of `B`. The Lean proof
takes the corresponding stratum identities from `Λ` and uses `Γ` and `I` to transfer the
field invariants to every simple stratum carrying the character.

## How the proof goes

Fix `F`, `V` with `N = dim_F V ≥ 1`, an admissible `ψ_F`, a principal lattice chain `L`
and levels `0 ≤ m < n`. Apply `C` to `L, n, m` and `Λ` to `L` with the integer levels
`m, n`. The label set of `Λ` is `labelSet (m : ℤ).toNat n.toNat ...`, which is the label
set of `B` because `(m : ℤ).toNat = m`.

**The map.** For each pair `θ ∈ S^m_n(𝔄)` choose (by `C`) a simple stratum `S_θ` with
`Φ(S_θ)` `U(𝔄)`-conjugate to `θ`, and put `σ(θ) = ρ(S_θ)`.

**Fibres.** If `σ(θ₁) = σ(θ₂)` then `ρ(S_{θ₁}) = ρ(S_{θ₂})`, so `Λ` gives `u ∈ U(𝔄)`
with `u⁻¹ β₁ u ∈ β₂ + 𝔓^{-m}`, i.e. `β₂ − u⁻¹ β₁ u ∈ 𝔓^{-m}`. By `C`, `Φ(S_{θ₁})` and
`Φ(S_{θ₂})` are `U(𝔄)`-conjugate. Hence `θ₁` and `θ₂` are `U(𝔄)`-conjugate, since
`U(𝔄)`-conjugacy of pairs is symmetric and transitive.

**Invariants.** Let `T` be a simple stratum on `L` at levels `n, m` with `θ ∈ Ĉ(T)`, and
write `θ = Φ(S)^x` with `S = S_θ` and `x ∈ U(𝔄)`. Apply `Γ` to `S` and `g = x⁻¹`. The transported chain is `L` itself, because a unit of `𝔄(L)` maps each
lattice `L_i` onto itself. So the premise yields a simple stratum `S'` on `L` at the same
levels, with `Ĉ(S') = {ϑ^x : ϑ ∈ Ĉ(S)} ∋ θ` and with the ramification index and residue
degree of `S`. Now `θ ∈ Ĉ(S') ∩ Ĉ(T)`, and `I` gives that `S'` and `T` have the same
invariants. With `Λ` for `S`:
`d(σ θ) = d(ρ S) = f(F[β_S]|F) = f(F[β_T]|F)` and
`e(F[β_T]|F) · e(σ θ) = e(F[β_S]|F) · e(ρ S) = e(𝔄)`.

## Auxiliary lemmas (private)

`CharacterPair.conj x` sends `(H, θ)` to `(x⁻¹ H x, θ^x)` with `θ^x(h) = θ(x h x⁻¹)`
(`Langlands.BushnellKutzko.CharacterPairConjugation`). The module proves:

- pairs with equal subgroups and pointwise equal characters are equal;
- `(θ^y)^x = θ^{yx}` and `θ^1 = θ`, hence `CharacterPair.AreConjugateBy U` is symmetric
  and transitive for a subgroup `U`;
- lattice chains with the same lattices are equal, and
  `L.linearEquivMap (LinearMap.GeneralLinearGroup.toLinearEquiv g) = L` for every
  `g ∈ U(𝔄) = L.unitFiltration 0`.
