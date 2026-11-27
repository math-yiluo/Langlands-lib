# Covering simple-character classes: characters of a fibre of restriction

* `finite_endFiltrationQuotient` in `AdditiveDualityProof`: the additive quotients `𝔓^i/𝔓^j`, `i ≤ j`, of
  a lattice chain over a nonarchimedean local field are finite (they are finitely generated modules
  over the finite ring `𝔬_F/𝔭_F^{j-i}`).
* `exists_elementCharacter_of_trivial_succ`: fix an additive character `ψ_F` of `F` that is trivial
  on `𝔭_F` and nontrivial on `𝔬_F` (`IsBKAdditiveCharacter`), and write
  `ψ_e(g) = ψ_F(tr(e(g - 1)))`. Then a character `χ` of a subgroup `H ≤ U^{k+1}(𝔄)` that is trivial
  on `H ∩ U^{k+2}(𝔄)` is `ψ_e` on `H` for some `e ∈ 𝔓^{-(k+1)}`. The condition on `ψ_F` is
  essential: for trivial `ψ_F` every `ψ_e` is trivial. The map `g ↦ g - 1` identifies
  `U^{k+1}(𝔄)/U^{k+2}(𝔄)` with the finite group `𝔓^{k+1}/𝔓^{k+2}`
  (`LatticeChain.unitFiltrationToQuotient`); `χ` descends to the image of `H`, extends to the whole
  quotient (`MonoidHom.domRestrict_surjective`, duality of finite abelian groups), and the extension
  is `ψ_e` by `additiveDuality` (Bushnell and Kutzko, *The admissible dual of GL(N) via compact open
  subgroups* (1993), (1.1.5)–(1.1.6)).

This is the first step of the statement on p. 120 of Bushnell and Kutzko, *Simple types in
GL(N): computing conjugacy classes* (1994): two simple characters with the same restriction
differ by some `ψ_c`.
