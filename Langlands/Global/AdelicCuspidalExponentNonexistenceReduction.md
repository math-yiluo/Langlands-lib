# The lemma of Bernstein–Lapid §6.4 from the boundedness of Mœglin–Waldspurger I.4.1

Module `Langlands.Global.AdelicCuspidalExponentNonexistenceReduction`.

This module proves the lemma of §6.4 of Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, J. Amer. Math. Soc. 37 (2024), pp. 203–204
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), in the form
`CuspidalExponentNonexistenceStatement`, from three propositions of the Library:

- `CuspidalExponentBoundednessStatement` (`Langlands.Global.AdelicCuspidalExponentBoundednessStatement`):
  under the hypotheses of the lemma, every right translate of every constant term `C_Q f`,
  `Q ⊆ R`, is bounded on `M_R(𝔸)^1` (the source's consequence of Mœglin–Waldspurger I.4.1);
- `ParabolicCuspidalVanishingStatement` (`Langlands.Global.AdelicCuspidalAnnihilator`): the
  vanishing criterion (8.1);
- `ConstantTermAutomorphyStatement` (`Langlands.Global.AdelicConstantTermAutomorphyStatement`).

It also composes this with `Langlands.Global.cuspidalExponentAscentReduction`
(`Langlands.Global.AdelicCuspidalExponentAscentReduction`). The module does not prove the three
propositions.

## Statements

- `Langlands.Global.CuspidalExponentNonexistenceReductionStatement` is the implication
  `CuspidalExponentBoundednessStatement → ParabolicCuspidalVanishingStatement →
  ConstantTermAutomorphyStatement → CuspidalExponentNonexistenceStatement` at universe `u`;
  `Langlands.Global.cuspidalExponentNonexistenceReduction` proves it.
- `Langlands.Global.cuspidalExponentAscent_of_boundedness`: the same three propositions imply
  `CuspidalExponentAscentStatement` (Corollary 6.4).

## Auxiliary results

- `leviCharacter_mem_corootAnnihilator` and `realExponent_mem_corootAnnihilator_of_le`: the
  restrictions to the maximal split torus of characters of `M_J`, and the real exponents of
  parameters of `P_J`, are annihilated by the coroots of `J` (`standardLeviCharacterAnnihilator`).
- `exists_coroot_projection`: for `Q ⊆ R` and a simple root `β` of `R`, the projection `w` of
  `β^∨` to `𝔞_Q` along the coroots of `Q` (the decomposition `𝔞_∅ = 𝔞_Q ⊕ span Q^∨` of
  `standardLeviRealDecomposition`) lies in the span of the coroots of `R`. So `w` is annihilated
  by `𝔞_R^*`, and it pairs with every element of `𝔞_Q^*` as `β^∨` does.
- `map_torus_mem_normOneSubgroup`: a positive torus point whose logarithm is annihilated by the
  restricted characters of `M_R` maps into `M_R(𝔸)^1`. `eq_map_torus_of_map_eq`: a point of
  `P_Q(𝔸)` with the image in `G(𝔸)` of a torus point `t` is the image of `t`.
  `re_complexParameterPairing_cocharacterFunctional` computes `Re ⟨μ, H⟩` at such a point.
- `eq_zero_of_bounded_of_maximal`: let `R = Q ∪ {β}` with `β ∉ Q`, and let `ψ = ∑_{μ ∈ s} c μ`
  be a finite sum of functions with generalized exponents `μ` along `Q`, every nonzero `c μ` with
  `⟨Re μ, β^∨⟩ < 0`. If every right translate of `ψ` is bounded on `M_R(𝔸)^1`, then `ψ = 0`.
  For fixed `g`, take for each `t ∈ ℝ` a positive torus point with logarithm `t w`. Its image
  lies in the positive split component `𝔄_Q` (`exists_positiveSplitComponent_torus_log`) and in
  `M_R(𝔸)^1`. Along these points `ψ` is the exponential polynomial `∑ e^{t ⟨μ, H₀⟩} q_μ(t)`, with
  `H₀` the logarithm of the point at `t = 1`, `q_μ` polynomials
  (`Langlands.Analysis.exists_polynomial_eval_smul`), and
  `Re ⟨μ, H₀⟩ = ⟨Re μ, w⟩ = ⟨Re μ, β^∨⟩ < 0`. It is bounded, hence zero
  (`Langlands.Analysis.expPolynomial_eq_zero_of_bounded`); its value at `t = 0` is `ψ(g)`. This
  is the source's argument on `𝔄_P^G`, restricted to one line, and needs only one sign.

## The proof

Fix the data of the lemma. Call `Q ⊆ R` *maximal* if `R = Q ∪ {β}` for some `β ∉ Q`.

1. Along a non-maximal `Q`, including `Q = R`, every component `c Q μ` vanishes by hypothesis,
   so `φc Q = 0`. Then `C_Q f` lies in the cuspidal annihilator along `Q`, since its pairings
   equal those of `φc Q`.
2. For `N = 0` the group `G(𝔸)` has one point. Then `f = C_R f` has cuspidal projection
   `φc R = 0`, and the pairing with the constant cusp form `1` gives `f = 0`. This uses private
   lemmas of the module: subsingleton points of closed subgroups of the general linear group of
   rank zero, and the cusp form `1`. From now on `N > 0`.
3. Let `Q` be maximal and `Q' ⊊ Q`. No `Q'' ⊆ Q'` is maximal (a cardinality count), so all
   projections along `Q'' ⊆ Q'` vanish. `C_{Q'} f` is automorphic (`ConstantTermAutomorphyStatement`),
   and its constant terms along `Q'' ⊆ Q'` are `C_{Q''} f`
   (`constantTerm_constantTerm_of_parabolicQuotient` of
   `Langlands.Global.AdelicParabolicConstantTermTransitivity`), which lie in the cuspidal
   annihilators. The vanishing criterion gives `C_{Q'} f = 0` (the source's use of
   Proposition 6.2 for non-maximal parabolics).
4. Hence for maximal `Q` the constant term `C_Q f` is cuspidal along `Q`. It is therefore a
   cuspidal projection of itself, and `C_Q f - φc Q` is a cuspidal projection of `0`, so
   `C_Q f = φc Q` (`eq_zero_of_isCuspidalProjection_zero`). By
   `CuspidalExponentBoundednessStatement` its right translates are bounded on `M_R(𝔸)^1`. The
   simple root of the hypothesis for each nonzero component is the unique `β` with
   `R = Q ∪ {β}`, so `eq_zero_of_bounded_of_maximal` gives `φc Q = 0`.
5. All projections vanish, so every `C_Q f`, `Q ⊆ R`, lies in the cuspidal annihilator along `Q`,
   and the vanishing criterion gives `f = 0` (the source: `φ` is cuspidal without cuspidal
   exponent along `G`).

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024): §6.1 (the decompositions of `𝔞_0^*` and `𝔞_0`, pp. 199–200), §6.2
  (constant terms and cuspidal projections, pp. 201–202), the lemma of §6.4 and its proof
  (pp. 203–204), (8.1) (p. 221).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995): I.3.4
  and I.3.5 (pp. 45–48), I.4.1 (p. 49).
