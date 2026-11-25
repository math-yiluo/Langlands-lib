# Proof of `ComplexStandardHolomorphicGrowthStatement`

## Statement proved

`Langlands.Archimedean.HolomorphicGrowth.complexStandardHolomorphicGrowth :
ComplexStandardHolomorphicGrowthStatement` (statement in the Library module
`ComplexLinkedLanglandsQuotientGrowth`): for every `n` and every list `ds` of complex characters
there is a real `c > 0` such that for every `d`,
`c (d + 1)^{n(n-1)} ≤ finrank ((holFiltration n d).map (envelopingAction (complexStandardLie n ds)))`.

## Proof

Let `χ` be the position characters of `ds`, so that `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}` with
`l = posWeight ds`, `t = posExponent ds` (`complexPositionCharacter_eq_phase`). Let
`M = |Lw n ⊕ Lw n| = n(n-1)` (`card_Lw_mul_two`).

1. **Level data.** `eL`, `hL`, `bL`, `tauL`, `dtL`: the level data of `χ`
   (`h_m - b_m = l_m - l_{m-1}`, `dτ_m = τ_m - τ_{m-1}` with `τ_k = t_k + (n-1)/2 - k`); they
   telescope to `χ` (`hl_L`, `hτ_L`). Their Gram exponents `σ = gramExp hL bL dtL` are used for
   the jets.
2. **Words.** For `α : Lw n ⊕ Lw n → ℕ`, `wordOf α` is the list with `α_i` copies of `symbMat i`,
   `uWord` the product of the corresponding `ι(hol X)` (in `holFiltration n d` when the word has
   length `≤ d`: `uWord_mem_holFiltration`), acting by `holWord` (`coe_envelopingAction_uWord`,
   `coe_principalSeriesLie_hol`). By `hasJet_holDeriv`, `hasJet_holWord`: a principal-series
   function with jet `Q` is sent to a function with jet `evalWord (wordOf α ↦ opDataH) Q`.
3. **Independence** (`coeff_eq_zero_wordOp`). Suppose `Σ_{i ∈ s} c_i holWord (wordOf (A i))`
   vanishes on all `U(n)`-finite functions, `A` injective. Applied to the test functions
   (`testFun_mem_kFiniteFunctions`, `hasJet_testFun`), the jets give
   `Σ_i c_i evalWord (w_i) (ιP (testPoly γ)) = 0` for all `γ` (`HasJet.unique`), hence for all
   polynomials in `v` (`testPoly_eq`: the `testPoly γ` are the monomials), hence on all of
   `Pol n` (`eq_zero_of_kills_rename`). If some `c_i ≠ 0`, take the longest words among them; by
   `sum_prod_sym_eq_zero` and `prod_sym_wordOf` the products `prodSymb (A i)` of these words would
   satisfy a nontrivial linear relation, contradicting `linearIndependent_prodSymb`.
4. **Count.** With `q = d / (M + 1)` and `α` ranging over `Lw n ⊕ Lw n → Fin (q + 1)` (words of
   length `≤ M q ≤ d`), the linear map `c ↦ Σ_α c_α · (action of uWord (wordOf α))` into the image
   of `holFiltration n d` is injective by step 3, so the finrank is at least `(q + 1)^M`. Since
   `d + 1 ≤ (M + 1)(q + 1)`, this is at least `(d + 1)^{n(n-1)} / (M + 1)^M`; take
   `c = 1 / (M + 1)^M`.

## Supporting modules

`ComplexMomentSymbols` (leading monomials), `ComplexOperatorSymbols` (top symbols of words),
`ComplexHolomorphicFormal` (the operators and their symbols), `FormalRealPolynomials`,
`WeightedWirtinger`, `ComplexHolomorphicJets` (jets), `ComplexHolomorphicIntertwining`
(`hasJet_holDeriv`), `ComplexHolomorphicTestFunctions`. They build on the infrastructure
of the growth bound `ComplexLinkedSmallGrowthStatement` (`ComplexNoncompactPicture`, `ComplexNoncompactFiltration`, `ComplexTorusDerivative`,
`ComplexLevelSpan`, `ComplexLinkedSmallGrowthAdjacent`, `ComplexLinkedSmallGrowthProof`, …).

## Provenance

Internal proof of a statement already in the Library, by an elementary route: the
holomorphic factor acts on holomorphic jets of principal-series functions in the noncompact
picture through polynomial differential operators, whose top symbols are entries of the moment map
`Φ = nb⁻¹ (nb Ξᵀ)_{strictly upper} nb`; it does not use Kostant's or Duflo's theorem.
