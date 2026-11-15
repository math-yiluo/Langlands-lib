# Proof: desingularization along a strictly standard element

`Langlands.CommutativeAlgebra.Popescu.Desing.strictlyStandardDesingularization :
StrictlyStandardDesingularizationStatement.{u}` proves the statement
`Langlands.CommutativeAlgebra.Popescu.StrictlyStandardDesingularizationStatement`
(Stacks Project, *Smoothing Ring Maps*, Lemma 7.3, Tag 07F0) for every universe `u`. It uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Source

Stacks Project, Chapter 16 *Smoothing Ring Maps* (`smoothing.pdf` in literature
`stacks-artin-axioms-approximation-2026-11-06`):

| Result | Tag | Printed pages |
| --- | --- | --- |
| Lemma 16.2.2 (local structure at a smooth point) | 07C6 | 2–3 |
| Definition 16.2.3 (strictly standard elements, (2.3.3), (2.3.4)) | 07C7 | 3 |
| Lemma 16.2.5 (Elkik: strictly standard elements and `H_{A/R}`) | 07CA | 4 |
| Lemma 16.6.1 (the lifting lemma) | 07CP | 15–18 |
| Lemma 16.7.1 (desingularization over `R`, (7.1.1)) | 07CR | 18–19 |
| Lemma 16.7.2 (desingularization over a base `D`) | 07CT | 19–20 |
| Lemma 16.7.3 (the target) | 07F0 | 20 |

The Markdown of the auxiliary modules uses the chapter-internal numbering of `smoothing.pdf`
(Lemma 6.1, Lemma 7.1, …). The proof of Lemma 16.7.3 in Stacks applies Lemma 6.1 with `π⁴` in
place of `π`, then Lemma 7.2, and omits the final verification. The Lean proof follows this route.
Its implementations of Lemmas 6.1, 7.1 and 7.2 differ in places from Stacks. Each module's
Markdown describes those differences.

## Proof

The proof combines three auxiliary results, each in its own module:

- `exists_lift_D` (module `DesingD`, Stacks 6.1, Tag 07CP). It is applied with `ϖ = π⁴` and
  `ε = π⁸`. It gives a finitely presented `R`-algebra `D`, maps `ψ : D → Λ` and
  `τ : C → D ⧸ π⁴D` compatible with `v` modulo `π⁴`, such that `D` is smooth over `R` away from
  `π⁴`. Moreover, if `y` lies in the singular ideal of `C` over `R ⧸ π⁸` and `l ∈ Λ` lifts `v(y)`,
  then `D` is smooth over `R` at `ψ⁻¹(𝔭)` for every prime `𝔭` of `Λ` with `π⁴ ∈ 𝔭` and
  `l ∉ 𝔭`.
- `exists_desing_lift` (module `DesingLifting`, Stacks 7.1 and 7.2, Tags 07CR and 07CT). It is
  applied to `f`, `ψ` and `σ = τ ∘ u : A → D ⧸ π⁴D`. Compatibility of `σ` with `f` and `ψ`
  modulo `π⁴` follows from `v ∘ u = (mod π⁸) ∘ f` and the compatibility of `τ`. It gives a
  finitely presented `B`, maps `g : A → B` and `h : B → Λ` with `h ∘ g = f`, such that `B_π` is
  smooth over `R` (since `D_π` is), and such that `B` is smooth over `R` at `h⁻¹(𝔭)` whenever
  `π ∈ 𝔭` and `D` is smooth over `R` at `ψ⁻¹(𝔭)`.
- The hypotheses `Ann_R(π) = Ann_R(π²)` and `Ann_Λ(π) = Ann_Λ(π²)` give the corresponding
  statements for `π⁴`, via `smul_eq_zero_of_pow_smul_eq_zero` (module `DesingTools`).

## The verification (left to the reader in Stacks)

It remains to show `(H_{C/(R/π⁸)}).map v ≤ (√(H_{B/R} Λ)).map (mod π⁸Λ)`. Let `y ∈ H_{C/(R/π⁸)}`
and choose `l ∈ Λ` with `v y = l mod π⁸`. It suffices to show `l ∈ √(H_{B/R} Λ)`. This radical
is the intersection of the primes `𝔭` containing `H_{B/R} Λ` (`Ideal.radical_eq_sInf`). Suppose
such a `𝔭` does not contain `l`.

- `π ∈ H_{B/R}`: every prime of `B` outside the smooth locus contains `π`, because `B_π` is
  smooth (`Algebra.basicOpen_subset_smoothLocus_iff_smooth`). Hence `π ∈ 𝔭`, and so `π⁴ ∈ 𝔭`.
- By the conclusion of `exists_lift_D`, `D` is smooth over `R` at `ψ⁻¹(𝔭)`. By the conclusion
  of `exists_desing_lift`, `B` is smooth over `R` at `h⁻¹(𝔭)`.
- The smooth locus of the finitely presented `B` is open (`Algebra.isOpen_smoothLocus`), so its
  complement is closed and equals the zero locus of its vanishing ideal `H_{B/R}`
  (`PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`). Since `h⁻¹(𝔭)` is in the smooth locus,
  `H_{B/R} ⊄ h⁻¹(𝔭)`. This contradicts `h(H_{B/R}) ⊆ 𝔭`.

## Module structure

`StrictlyStandardDesingularizationProof` imports `DesingD`, which imports `DesingLifting` and
`DesingChart`, which import `DesingTools`. Their Markdown files describe the auxiliary
declarations. These declarations are internal to this proof and are not claimed as Library
results.
