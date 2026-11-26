# The exponent ascent of Bernstein–Lapid, Corollary 6.4, from the lemma of §6.4

Module `Langlands.Global.AdelicCuspidalExponentAscentReduction`.

This module proves that the corollary of §6.4 of Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), p. 204
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), in the form
`CuspidalExponentAscentStatement` of `Langlands.Global.AdelicCuspidalExponentAscentStatement`,
follows from three propositions of the Library:

- `CuspidalExponentNonexistenceStatement` (`Langlands.Global.AdelicCuspidalExponentNonexistenceStatement`):
  the lemma of §6.4 for automorphic functions on `U_R(𝔸) M_R(F) \ G(𝔸)`;
- `ParabolicCuspidalVanishingStatement` (`Langlands.Global.AdelicCuspidalAnnihilator`): the
  vanishing criterion (8.1) of the source, used here only for the uniqueness of cuspidal
  projections;
- `ConstantTermAutomorphyStatement` (`Langlands.Global.AdelicConstantTermAutomorphyStatement`):
  the constant term along `R` of an automorphic function on `G(F) \ G(𝔸)` is automorphic on
  `U_R(𝔸) M_R(F) \ G(𝔸)`.

The module does not prove these three propositions.

## Statements

- `Langlands.Global.CuspidalExponentAscentReductionStatement` is the implication
  `CuspidalExponentNonexistenceStatement → ParabolicCuspidalVanishingStatement →
  ConstantTermAutomorphyStatement → CuspidalExponentAscentStatement`, all at universe `u`.
- `Langlands.Global.cuspidalExponentAscentReduction` proves it, for closed matrix embeddings of
  every size `N`, including `N = 0`.
- `StandardParabolicFamily.exists_cuspidalExponent_ascent` is the same result for one family
  `𝓕`. It does not use the hypothesis `⟨Re λ, α^∨⟩ < 0` of the corollary, which is therefore
  omitted from its hypotheses: when `⟨Re λ, α^∨⟩ ≥ 0` the triple `(P, α, λ)` itself satisfies
  the conclusion, and the proof below does not distinguish the two cases.

## The proof

Fix the data of `CuspidalExponentAscentStatement`: an automorphic `φ` on `G(F) \ G(𝔸)`, a family
`(φc, s, c)` of cuspidal projections and exponent decompositions of its constant terms, `λ ∈ s P`
with `c P λ ≠ 0`, the minimality of the rank of `P`, and a simple root `α ∉ P`. Let `R` be the
index `P ∪ {α}` (the source's `P_α`). Suppose that no `(Q, β, μ)` as in the conclusion exists.

1. *Negated conclusion.* Every nonzero component `c Q μ` with `β ∉ Q`, `Q ∪ {β} = R` and
   `Re λ - Re μ` in the real span of `R` has `⟨Re μ, β^∨⟩ < 0`.
2. *Ranks* (`exists_root_insert_eq`). If `Q ⊊ R` carries a nonzero component, minimality gives
   `|Q| ≥ |P| = |R| - 1`, so `R = Q ∪ {β}` for a simple root `β ∉ Q`.
3. *Subtracting the cuspidal projection along `R`.* By `ConstantTermAutomorphyStatement` the
   function `f₀ = C_R φ - φc R` is automorphic on `U_R(𝔸) M_R(F) \ G(𝔸)`. For `Q ⊊ R`,
   `C_Q f₀ = C_Q φ` by transitivity of constant terms (`constantTerm_constantTerm_of_le`) and
   cuspidality of `φc R`, so `φc Q` is a cuspidal projection of `C_Q f₀` with decomposition
   `(s Q, c Q)`. Along `R` itself, `C_R f₀ = f₀` has cuspidal projection `0`
   (the difference of the projections `φc R` of `C_R φ` and of `φc R`), with the empty
   decomposition. This is the source's step "upon subtracting the cuspidal projection".
4. *Filtering by the action of `𝔄_R`* (`Langlands.Global.AdelicSplitComponentShifts`). Call a
   label `(Q, μ)` with `Q ⊆ R` and `μ ∈ s Q` *bad* if `‖a^μ‖ ≠ ‖a^λ‖` for some `a ∈ 𝔄_R` (both
   evaluated at the lifts of `a` to `𝔄_Q` and `𝔄_P`). For each bad label choose such an `a`,
   put `z = a^μ` and take the factor `(a - z)^{k+1}`, `k` a degree bound of the polynomial
   orbits of `c Q μ`; let `D` be the product of these factors in the group algebra of `𝔄_R`.
   Then `D` kills every bad component (`shiftAlgHom_factor_eq_zero`), is injective on every
   component that is not bad (`eq_zero_of_shiftAlgHom_prod_eq_zero`, since then `z ≠ a^μ'`),
   preserves automorphy, cuspidality and exponents, commutes with the constant terms along
   `Q ⊆ R`, and maps cuspidal projections to cuspidal projections. So `D f₀` is automorphic on
   `U_R(𝔸) M_R(F) \ G(𝔸)`, and `(D φc Q, s Q, D c Q)` (empty along `R`) is a family of cuspidal
   projections and exponent decompositions of its constant terms. This replaces the source's
   decomposition of `φ'_k` according to the action of `𝔄_{P_α}`.
5. *Real central characters* (`realExponent_sub_mem_rootSpanReal`). If `(Q, μ)` is not bad,
   then `Re λ - Re μ` lies in the real span of the simple roots of `R`. Every real cocharacter
   `v` of `T` annihilated by the roots of `R` is the logarithm of a positive point `t` of `T`
   whose image in `G(𝔸)` lies in `𝔄_R`: it is the image of a real cocharacter of the split
   component `A_R` (`standardLeviCentralDirections`), hence the logarithm of a positive point of
   `A_R` (`PositiveRealTorus.exists_characterLog_eq`). The lifts of that point to `𝔄_Q` and
   `𝔄_P` are the images of `t` (`splitLift_eq_map_torus`), so
   `‖a^μ‖ = exp ⟨Re μ, v⟩` and `‖a^λ‖ = exp ⟨Re λ, v⟩` (`norm_parameterPower_map_torus`).
   Hence `Re λ - Re μ` annihilates the annihilator of the roots of `R`, which is their real span
   (`characterAnnihilator_cocharacterAnnihilator`, `rootAnnihilator_eq_cocharacterAnnihilator`).
   This is the source's equality `μ_{P_α} = λ_{P_α}`, in its real-part form.
6. *The lemma.* Every nonzero component `D c Q μ` of the filtered family has `Q ⊊ R` and is not
   bad, so `c Q μ ≠ 0`, `Re λ - Re μ` lies in the span of `R` (step 5), `R = Q ∪ {β}` (step 2)
   and `⟨Re μ, β^∨⟩ < 0` (step 1). `CuspidalExponentNonexistenceStatement` gives `D f₀ = 0`.
7. *Conclusion.* Then `C_P (D f₀) = 0`, so `D φc P` is a cuspidal projection of `0`, hence
   `D φc P = 0` (`eq_zero_of_isCuspidalProjection_zero`: the vanishing criterion for `N > 0`;
   for `N = 0` the group `G(𝔸)` and all Levis have one point, the constant `1` is a Levi cusp
   form, and the pairing with it detects the value). By directness of the exponent
   decomposition (`eq_zero_of_sum_eq_zero_of_hasUnnormalizedExponent`) `D c P λ = 0`. The label
   `(P, λ)` is not bad, so injectivity of `D` gives `c P λ = 0`, a contradiction.

The rank-zero case uses private lemmas of this module: a closed subgroup of the general linear
group of rank zero has at most one point over every base, and for such an embedding the constant
function `1` is a cusp form on every standard Levi.

## Correspondence with the source proof

The source proves the corollary on p. 204 by passing to `φ'_k = C_{G,P_α} φ(· k)` on
`M_{P_α}`, subtracting its cuspidal projection, decomposing according to the action of
`𝔄_{P_α}` and applying the lemma. Here the lemma is used in its relative form on
`U_R(𝔸) M_R(F) \ G(𝔸)`, which removes the passage to the Levi; the decomposition is replaced by
the explicit difference operator `D`, which keeps the cuspidal projections of the filtered
function explicit; and the equality of central characters is used only through real parts,
which is all the conclusion of `CuspidalExponentAscentStatement` records.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024): §6.1–6.2 (the decomposition of `𝔞_0^*`, `Re λ_P = (Re λ)_P`,
  pp. 199–202), (6.10) (p. 203), §6.4 (the lemma, pp. 203–204, and the corollary with its proof,
  p. 204), (8.1) (p. 221).
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995):
  I.2.6 and I.2.17 (constant terms of automorphic forms), I.3.4 and I.3.5 (uniqueness of the
  cuspidal projection).
