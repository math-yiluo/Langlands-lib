# Iterated normalized periods over split lattices in semidirect products

Module `Langlands.Global.RankinSelberg.ProjectionPeriod`, namespace
`Langlands.Global.LeftCosetSpace.Semidirect`. It is internal measure theory for the column
induction of `ProjectionExpansion`. It extends the Library module
`Langlands.Global.LeftCosetSemidirectPeriod`, whose vanishing result
`integral_fundamentalDomain_eq_zero_of_bounded` it turns into an equality. No literature source
is cited for it.

## Setting

The hypotheses are those of `LeftCosetSemidirectPeriod`. `N`, `M` and `H` are locally compact,
second-countable Borel topological groups. `i : N →* H` is an embedding, `j : M →* H` and
`p : H →* M` are continuous, `p ∘ j = id`, `p ∘ i = 1`, and every element of `ker p` lies in the
image of `i`. `Γ ≤ H` and `ΓM ≤ M` are discrete, `j(ΓM) ⊆ Γ` and `p(Γ) ⊆ ΓM`. For a subgroup
`Λ`, `fundamentalDomain Λ _` is the Library's chosen Borel fundamental domain, and all measures
are `Measure.haar`.

## Results

- `normalizedPeriod_eq_iterated`: assume the normal lattice `Γ.comap i` and `ΓM` have finite
  Haar covolume. Let `φ : H → ℂ` be bounded, continuous and left `Γ`-invariant. Then
  `|E_H|⁻¹ ∫_{E_H} φ = |E_M|⁻¹ ∫_{m ∈ E_M} |E_N|⁻¹ ∫_{n ∈ E_N} φ(i n · j m)`. Here `E_H`, `E_M`
  and `E_N` are the chosen fundamental domains of `Γ`, `ΓM` and `Γ.comap i`, and `|E|` is the
  real Haar mass. The proof follows the Library vanishing proof. The Library theorem
  `exists_haar_eq_smul_map_prod` gives `Haar_H = c • (Haar_N ⊗ Haar_M).map Φ` for
  `Φ(n, m) = i n · j m`. The period is moved to the product domain `Φ(E_N × E_M)`
  (`isFundamentalDomain_product`), and Fubini (`integral_prod_symm`) is applied. The same
  formula gives `|E_H| = c · |E_N| · |E_M|`. The masses are finite and nonzero
  (`haar_fundamentalDomain_ne_top`, `haar_fundamentalDomain_ne_zero`), so `c ≠ 0` and `c`
  cancels.
- `normalizedPeriod_eq_iterated_of_compact` is the same identity with a separately named normal
  lattice `ΓN` (with `i n ∈ Γ ↔ n ∈ ΓN`), assuming compactness of the three quotients. Compactness
  gives the finite covolumes and the bound on `φ`, as in the Library's
  `integral_fundamentalDomain_eq_zero`.
- `setIntegral_fundamentalDomain_character_eq_zero`: on a group `M` with right-invariant Haar
  measure, let `θ : M → ℂ` be multiplicative and trivial on a discrete subgroup `ΓM`, with
  `θ(m₀) ≠ 1` for some `m₀`. Then `∫_{E_M} θ = 0`. The right translate of `E_M` by `m₀` is again
  a fundamental domain. `θ` is `ΓM`-invariant, so its integral over either domain is the same.
  Right translation multiplies the integral by `θ(m₀)`, so `(θ(m₀) - 1) ∫_{E_M} θ = 0`.
