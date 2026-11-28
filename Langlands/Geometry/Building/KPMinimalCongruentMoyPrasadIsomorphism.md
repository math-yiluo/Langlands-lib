# KP Theorem 13.5.1 (1) for the constructed groups `P_{x,r}` and lattices `𝔤_{x,r}`

## Setting

`F` is a nonarchimedean local field of either characteristic, `K = inertiaFixedField F` its
maximal unramified extension inside `F^sep`, `𝒪[F]` its valuation ring with maximal ideal `𝔪`,
and `G` an affine group over `F` with `P : ParahoricBuildingData G`. The statements use the
Library's constructions unchanged:

- `P_{x,r} = P.minimalCongruentMoyPrasad h x r`, the Moy–Prasad group of KP Definition 13.2.1
  for the minimal congruent filtration `P.minimalCongruentCentralizerFiltration h` of
  `Z(F)_r = P.minimalCongruentCentralizerPoints r` (`KPMinimalCongruentCentralizer`), where
  `h : P.MinimalCongruentCentralizerOrder`. KP §13.5 equips the category of tori with the
  minimal congruent filtration for this theorem.
- `𝔤_{x,r} = P.moyPrasadLie hG hP h x r`, the Lie lattice of the smooth model
  `𝒢_{x,r} = P.moyPrasadModel hG hP h x r` chosen from `hG : MoyPrasadModelStatement`, and
  `𝔷_r = P.centralizerModelLie hZ r = Lie(𝒵_r)` for the centralizer models chosen from
  `hZ : CentralizerModelStatement`; `hP : P.SatisfiesApartmentAxioms`.
- `P.lieFiltrationData hZ hU hOrder hP`, the `LieFiltrationData` with `z_r = Lie(𝒵_r)` and
  `u_ψ = Lie(𝒰_ψ)` (`hU : AffineRootGroupModelStatement`,
  `hOrder : MinimalCongruentOrderStatement`), and its root lattices
  `rootBlockLie x a r = u_{a,x,r} + u_{2a,x,r}` (`KPMoyPrasadLieLattices`,
  `KPMoyPrasadIsomorphismStatement`).
- Over `K`: for the chosen apartment lift `L = P.unramifiedApartmentLift.2`,
  `G(K)_{x,t} = L.buildingData.minimalCongruentMoyPrasad L.centralizer_isTorus (L.e x) t`, and
  `𝔤(K)_{x,t}` is the Lie lattice of `(P.moyPrasadModel hG hP h x t).baseChangeUnramified`, the
  base change of `𝒢_{x,t}` to the integers `fixedFieldIntegers F` of `K`. By
  `moyPrasadModel_unramifiedIntegralPoints` the integral points of this base change are
  `G(K)_{x,t}`.

The existence statements `hG`, `hZ`, `hU`, `hOrder` enter only as the arguments of these
constructions. KP's three alternatives (KP §13.5, printed p. 474) are `MoyPrasadAlternative F G r s`
for `0 < r ≤ s`:

1. the maximally split maximal torus of `G_K` is weakly induced (KP Definition B.6.2) and
   `s ≤ 2r`;
2. `r = r₀ + n` with `0 ≤ r₀ < 1`, `n` a positive integer, and `s ≤ r₀ + 2n`;
3. `s ≤ 2r ≤ r + 1`.

`HasMoyPrasadQuotientIso H₁ H₂ g₁ g₂` says that some surjective homomorphism
`H₁ → g₁/g₂` has kernel `H₂`, that is `H₁/H₂ ≅ g₁/g₂` as abstract groups.

## Statements

### Theorem 13.5.1 (1)

`MinimalCongruentMoyPrasadIsomorphismStatement`: for `0 < r ≤ s` satisfying one of the three
alternatives, `P_{x,r}/P_{x,s} ≅ 𝔤_{x,r}/𝔤_{x,s}`.

### Compatibility with the maximal unramified extension

`MinimalCongruentMoyPrasadUnramifiedIsomorphismStatement`: under the same hypotheses,

- for every `t ≥ 0`, `g ↦ g_K = rationalExtend F K G g` maps `P_{x,t}` into `G(K)_{x,t}`, and
  the base change map `GenericLie.baseChangeMap : Lie(G) → Lie(G_K)`
  (`IntegralModel.LieLatticeBaseChange`) maps `𝔤_{x,t}` into `𝔤(K)_{x,t}`;
- there are a surjective `φ_K : G(K)_{x,r} → 𝔤(K)_{x,r}/𝔤(K)_{x,s}` with kernel `G(K)_{x,s}` and a
  surjective `φ : P_{x,r} → 𝔤_{x,r}/𝔤_{x,s}` with kernel `P_{x,s}` such that, for
  `g ∈ P_{x,r}` and `X ∈ 𝔤_{x,r}` with `φ(g)` the class of `X`, `φ_K(g_K)` is the class of the
  base change of `X`.

The two inclusions are the maps "induced by `G(F) → G(K)` and by `Lie(G) → Lie(G_K)`"; the
first follows from `moyPrasadModel_integralPoints`, `moyPrasadModel_unramifiedIntegralPoints` and
`IntegralModel.mem_integralPoints_rationalExtend_iff_unramified`, the second is
`IntegralModel.baseChangeMap_mem_lieLattice_baseChangeUnramified`. The compatibility is stated
for elements `g' ∈ G(K)_{x,r}` and `Y ∈ 𝔤(K)_{x,r}` equal to `g_K` and to the base change of
`X`, so that no membership proof appears inside the statement; by the two inclusions such `g'`
and `Y` always exist. The `φ` part is `MinimalCongruentMoyPrasadIsomorphismStatement`.

KP's isomorphism is also compatible with finite unramified extensions `F'/F`. Stating this needs
building data over `F'`, and it is not stated here.

### The centralizer component

`MinimalCongruentCentralizerIsomorphismStatement`: for `0 < r ≤ s` satisfying one of the three
alternatives, `Z(F)_r/Z(F)_s ≅ 𝔷_r/𝔷_s`, with `Z = Z_G(S)` the centralizer of the maximal split
torus of `P`.

When `G` is quasi-split, `Z` is a torus, `Z(K)_{x₀,r}` is the minimal congruent filtration of the
`K`-torus `Z_K`, and the statement descends from the isomorphism over `K` given by Proposition
B.6.9 (with Corollary B.10.13, `T(K)^mc_r = T(K)^std_r` for weakly induced `T`) under (1), by the
functorial isomorphism of Proposition B.10.16 under (2), and by Proposition B.10.17 (for `r < s`;
the case `r = s` is trivial) under (3), which is compatible with unramified extensions. The
descent uses `T(F)^mc_r = T(K)^mc_r ∩ T(F)` (corrected Definition B.10.8(4)) and the vanishing of
Corollary B.10.14. Alternative (1) is a condition on `G_K`; a maximally split maximal torus `T`
of `G_K` lies in `Z_K` and is a maximally split maximal torus of `Z_K`, so the condition is the
same for `Z`.

In general `Z` is not a torus: `Z(F)_r` is the Moy–Prasad filtration of KP §9.8 at the unique point
of the building of `Z`, computed in `Z(K)` (the group `minimalCongruentCentralizerPointsOfLift`),
and over `K` it involves the root groups of the quasi-split group `Z_K`. The statement is then
Theorem 13.5.1 (1) for `Z` at that point.

### The root-block component

`MoyPrasadRootBlockIsomorphismStatement`: let `a` be a relative root of `P` that is not twice a
relative root, and `0 < r ≤ s`. If `2a` is not a relative root, or if `s ≤ 2r`, then

`U_{a,x,r}U_{2a,x,r} / U_{a,x,s}U_{2a,x,s} ≅ (u_{a,x,r} + u_{2a,x,r}) / (u_{a,x,s} + u_{2a,x,s})`,

the groups being `Subgroup.closure (filtrationBlock x r a)` (the block of KP Definition 7.3.3(1)
at the constant function `r`) and the lattices `rootBlockLie` of the constructed
`LieFiltrationData`. This is the form of the hypothesis on root blocks in the supplied-data
`MoyPrasadIsomorphismStatement`. Each of the three alternatives implies `s ≤ 2r` (under (2),
`s ≤ r₀ + 2n ≤ 2(r₀ + n)`), so the statement supplies that hypothesis for every non-divisible
root under each alternative. For a multipliable root and `s > 2r` the block quotient is in
general not abelian (commutators of the block at depth `r` lie at depth `2r` in `U_{2a}`), while
the lattice quotient is, so the condition `s ≤ 2r` cannot be dropped there.

The statement rests on the following arguments; this file does not carry them out.

- *Non-multipliable `a`* (KP Propositions C.5.1 and A.5.19). Proposition A.5.19(3) gives, for a
  smooth affine `𝒪`-group `𝒰` and integers `0 < n ≤ m ≤ 2n`, an isomorphism
  `𝒰(𝔪ⁿ)/𝒰(𝔪ᵐ) ≅ Lie(𝒰)⊗𝔪ⁿ / Lie(𝒰)⊗𝔪ᵐ`, functorial in `𝒰`. No `K`-root over a non-multipliable
  `a` is multipliable, and by Proposition C.5.1 the root models satisfy `(𝒰_{b,x,ρ})_n = 𝒰_{b,x,ρ+n}`
  for every real `ρ`. Applying A.5.19(3) to the model at depth `ρ = r − n` with `n ≥ s − r`, and
  its functoriality for the inclusion of the model at depth `s − n` (as in KP's proof of
  Theorem 13.5.1 under (2)), gives the isomorphism for all `0 < r ≤ s`.
- *Multipliable `a`, alternative (2)*. Proposition C.5.1 gives the congruence property for the
  block models `𝒰_{b,x,ρ,σ}` with `σ ≤ 2ρ`, in particular for the equal-parameter models with
  `ρ ≥ 0`, and the same argument applied to the model at depth `r₀` gives the isomorphism when
  `r = r₀ + n`, `n ≥ 1`, `s ≤ r₀ + 2n`. Mixed starting models `𝒰_{b,x,ρ,σ}` cover further pairs,
  depending on the jumps of the filtrations.
- *Multipliable `a`, `s ≤ 2r`* (KP §C.4). After the reductions of §C.1 (passage to the simply
  connected cover, `K`-simple factors and restriction of scalars, which do not change the
  abstract groups) the block of a multipliable `K`-root is `X(K)_ρ · Z(K)_σ` in `U_{L/K}`, with
  `(ρ, σ) = (r + c, r + 2c)` for a shift `c` given by the apartment point and the normalization
  `μ` (KP Lemma 6.1.6). The coordinates `(u, v) ↦ (u, v − u ū λ)` of (C.4.1), for
  `λ ∈ L^{tr=1,max}`, identify `X(K)_ρ · Z(K)_σ` with the product of lattices `Y_{ρ'} × Z_{σ'}`,
  where `ρ'` and `σ'` are the jumps of Lemma C.4.1 (`ρ'` the least jump of `X(K)/Z(K)` that is
  `≥ ρ`, `σ'` the least jump of `Z(K)` that is `≥ min(2ρ, σ) = σ`) (Lemmas C.4.1 and C.4.2), and
  likewise the block at depth `s` with `Y_{ρ''} × Z_{σ''}`; the group law becomes addition
  corrected by `z − z̄`, `z = λ ū u'`, of valuation at least `2ρ' + μ + 1/2` (proof of Lemma
  C.4.2). Since
  `2ρ' + 1/2` is a jump of the filtration of `Z(K)` (`2J_{a/2a} + 1/2 ⊂ J_{2a}`, proof of Lemma
  C.4.1) and is at least `2r + 2c ≥ s + 2c`, it is at least `σ''` when `s ≤ 2r`; so the correction
  lies in `Z_{σ''}` and `(u, x) ↦ (u, x)` induces an isomorphism of the block quotient onto
  `(Y_{ρ'} × Z_{σ'}) / (Y_{ρ''} × Z_{σ''})`, which is the quotient of the Lie lattices by §C.4.5 (the differential of (C.4.1) is the identity of
  `L ⊕ L⁰`). Changing `λ` within `L^{tr=1,max}` changes the second coordinate by `u ū δ` with
  `δ ∈ L⁰`, `ω(δ) ≥ μ`, which lies in the block at depth `s`; the induced isomorphism is therefore
  independent of `λ`. The block of the `F`-root `a` over `K` is, modulo its block at depth `s`, the
  product of the blocks of the `K`-roots restricting to `a` and `2a`, since their commutators lie
  at depth `2r ≥ s`. The resulting isomorphism over `K` is `Gal(K/F)`-equivariant, and the
  statement over `F` follows by taking invariants as in KP's proof of Theorem 13.5.1 (vanishing
  of `H¹` of the depth-`s` groups and lattices).

KP's proof of Theorem 13.5.1 under alternatives (1) and (3) applies Proposition A.5.19 to
`𝒰_{a,x,r−n}` using `(𝒰_{a,x,r})_n = 𝒰_{a,x,r+n}` for every root. Proposition C.5.1 states this for
non-multipliable roots and warns that it fails for the model `𝒰_{a,x,r}` of a multipliable root,
whose congruence subgroups are `𝒰_{a,x,r+n,2r+n}`. For multipliable roots the statement here is
supported by the coordinates of §C.4 as above.

### Reduction to the supplied-data theorem

`MinimalCongruentMoyPrasadIsomorphismReductionStatement`: `MoyPrasadIsomorphismStatement`,
`MinimalCongruentCentralizerAxiomsStatement`, `MinimalCongruentCentralizerDoubleRootStatement`,
`MoyPrasadLieSpanStatement`, `MinimalCongruentCentralizerIsomorphismStatement` and
`MoyPrasadRootBlockIsomorphismStatement`, together with the model statements
`CentralizerModelStatement`, `AffineRootGroupModelStatement` and `MinimalCongruentOrderStatement`
from which the `LieFiltrationData` is built, imply `MinimalCongruentMoyPrasadIsomorphismStatement`.

The reduction applies `MoyPrasadIsomorphismStatement` to the filtration
`P.minimalCongruentCentralizerFiltration h` (whose filtration axioms and double-root condition are
the two centralizer statements) and to `P.lieFiltrationData hZ hU hOrder hP` (whose
`centralizerLie` is `𝔷_r`). Its centralizer hypothesis is
`MinimalCongruentCentralizerIsomorphismStatement`, its root-block hypothesis is
`MoyPrasadRootBlockIsomorphismStatement` with `s ≤ 2r` from the alternative, and
`MoyPrasadLieSpanStatement` identifies its `lieFiltration x r` with `𝔤_{x,r}`.

This file states these results and does not prove them.

## Not stated

- Parts (2) and (3) of Theorem 13.5.1 (equivariance under `F`-rational automorphisms under
  alternatives (1) or (2); agreement of the two isomorphisms when both hold) concern the
  particular isomorphisms built from Propositions A.5.19 and B.6.9, which this file does not
  construct; they are not stated.
- Compatibility with finite unramified extensions `F'/F` is not stated.
- The isomorphisms are asserted to exist; no particular isomorphism is constructed or named.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (printed page = PDF
  page − 31): Definition 13.2.1 and Proposition 13.2.5 (pp. 468–469); §13.5, the three conditions
  and Theorem 13.5.1 (p. 474) and its proof (pp. 475–476); Proposition A.5.19 (pp. 641–642);
  Definition B.6.2 (p. 669); Proposition B.6.9 (p. 673); Definition B.10.8 (p. 690); Corollaries
  B.10.13–B.10.14 (p. 692); Propositions B.10.16 and B.10.17 (pp. 694–695); §C.1, Lemmas C.4.1 and
  C.4.2 and §C.4.5 (pp. 696–702); Proposition C.5.1 (pp. 703–704); Lemma 6.1.6 (p. 200).
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024,
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`: no entry on §13.5 or
  Theorem 13.5.1 (the Chapter 13 entries, PDF p. 49, concern Proposition 13.5.2(1), 13.6.2 and
  Theorem 13.8.5); the Appendix B entries (PDF p. 50) on Definition B.10.8, Corollary B.10.14 and
  the added Remark B.10.15 (descent of the models `T^mc_r` to `𝒪`) concern the minimal congruent
  filtration used here.
