# Necessary upper Jacquet bounds for an analytically tempered product Levi

Authors: Worker 819 and Worker 219. Worker 219 wrote `ProductLeviNecessityTest`;
Worker 819 wrote the other modules.

This module proves the published proposition
`Langlands.GLProductLeviTemperedExponentNecessityStatement`
(see [`ProductLeviTemperedExponentNecessityStatement`](ProductLeviTemperedExponentNecessityStatement.md))
as the theorem

`Langlands.glProductLeviTemperedExponentNecessity :
  GLProductLeviTemperedExponentNecessityStatement.{uF, uV}`.

Take a product Levi `M = C.Levi F.Carrier` and a Borel Haar measure `μ` on
`M ⧸ Z(M)`. Let `σ` be irreducible and analytically tempered for `μ`. Let `ψ` be a
generalized eigencharacter, with open kernel, of the upper normalized refined
Jacquet module, pulled back to the flattened block-scalar tuples. Then
`‖ψ a‖ ≤ 1` for every tuple `a` whose normalized absolute values increase
separately inside each outer block. Irreducibility is not used in the proof.

This is the necessity direction of the tempered exponent criterion. The
statement's Markdown cites the source: J.-L. Waldspurger, *La formule de
Plancherel pour les groupes p-adiques, d'après Harish-Chandra* (literature ID
`waldspurger-2003-plancherel`), Proposition III.2.2. That source defines
temperedness by a `Ξ`-bound, while the input here is `L ^ (2 + ε)` on the
full-centre quotient. The Lean proof is therefore a direct derived argument
and does not follow the source. It uses explicit compression eigenvectors and
explicit cell counting, described below.

## Helper modules

- `ProductLeviNecessityCombinatorics` defines the test tuples
  `testScalars T C D j k e` and proves `norm_le_one_of_test`. If `‖ψ‖ ≤ 1` on
  every `testScalars j k 1` with `0 < k ≤ (D j).length` and on every central
  `testScalars j (D j).length (-1)`, then `‖ψ a‖ ≤ 1` on the whole chamber.
- `ProductLeviNecessityTest` contains the facts about one test tuple: it is
  weakly contracting; its `j`-th block scalar is the diagonal matrix with the
  uniformizer on the set `testSet C D j k` and `1` elsewhere; its refined
  modulus is `q ^ (-|S| |Sᶜ|)`; and the full tuples are central with modulus `1`.
- `ProductLeviNecessityEigen` proves `exists_eigen_coefficient`. A weakly
  contracting tuple `c` with block-scalar element `g` has a vector `x`, a smooth
  functional `ℓ` and a compact open subgroup `K` inside any given neighbourhood
  of `1`, such that `ℓ (σ (g ^ m) x) = λ ^ m ℓ x` with
  `λ = √δ(c) ψ(c)`, and `x` and `ℓ` are `K`-invariant.
- `ProductLeviNecessityCells` proves `cells_lower_bound`. If `f` takes the value
  `F0 M` on `mk (u g ^ M k)` for all `u, k` in an open subgroup inside the
  integral Levi, then for some `t` and every `m`,
  `q ^ (m |S| |Sᶜ|) (F0 (m + t) μ(mk '' K)) ≤ ∫⁻ f ∂μ`.

## Lemmas of this module

All lemmas are in the namespace `Langlands.ProductLeviNecessity`.

- `nonpos_of_forall_mul_le`: if `0 ≤ B` and `(2 + ε) y ≤ ε B` for every
  `ε > 0`, then `y ≤ 0`. Take `ε = y / (B + 1)`.
- `le_one_of_forall_pow_mul_le`: if `C0 > 0` and `R ^ m C0 ≤ I` for every `m`,
  then `R ≤ 1` (`pow_unbounded_of_one_lt`).
- `norm_le_one_of_diagonal`: let `σ` be analytically tempered and let `c` be
  weakly contracting. Suppose the `j`-th block scalar of `c` is the diagonal
  matrix with `T.uniformizer` on `S` and `1` elsewhere, and the refined modulus
  of `c` is `q ^ (-|S| |Sᶜ|)`. Then `‖ψ(flatScalars c)‖ ≤ 1`.
- `norm_le_one_of_mem_center`: let `σ` be analytically tempered and let `c` be
  weakly contracting with central block scalars and refined modulus `1`. Then
  `‖ψ(flatScalars c)‖ ≤ 1`.

## Proof of `norm_le_one_of_diagonal`

Let `χ` be the unitary central character from `IsTemperedModCenter`. Apply
`exists_eigen_coefficient` with the integral Levi as the neighbourhood. This
gives `K`, `x` and `ℓ` with `ℓ x ≠ 0`. Invariance of `x` and `ℓ` gives
`ℓ (σ (u g ^ M k) x) = λ ^ M ℓ x` for `u, k ∈ K`. Fix `ε > 0` and let
`f = ‖coefficient‖ₑ ^ (2 + ε)` on the central quotient. Then `∫⁻ f ∂μ < ⊤`,
because the coefficient is in `L ^ (2 + ε)`. By `cells_lower_bound` with
`F0 M = ‖λ ^ M ℓ x‖ ^ (2 + ε)`, for every `m`

`(q ^ P ‖λ‖ ^ (2 + ε)) ^ m · ‖λ‖ ^ ((2 + ε) t) ‖ℓ x‖ ^ (2 + ε) μ(mk '' K) ≤ ∫⁻ f ∂μ`,

where `P = |S| |Sᶜ|`. `μ(mk '' K)` is positive because the image is open, and
finite because `K` lies in the integral Levi. So
`le_one_of_forall_pow_mul_le` gives `q ^ P ‖λ‖ ^ (2 + ε) ≤ 1`. Since
`‖λ‖ = q ^ (-P / 2) ‖ψ(c)‖`, taking logarithms gives
`(2 + ε) log ‖ψ(c)‖ ≤ ε P log q / 2` for every `ε > 0`.
`nonpos_of_forall_mul_le` then gives `log ‖ψ(c)‖ ≤ 0`, that is,
`‖ψ(c)‖ ≤ 1`.

## Proof of `norm_le_one_of_mem_center`

`exists_eigen_coefficient` with `m = 1` gives `ℓ (σ g x) = λ ℓ x`. Since `g` is
central, `σ g x = χ(g) x`, so `λ = χ(g)` and `|λ| = 1`. The modulus is `1`, so
`λ = ψ(c)` and `‖ψ(c)‖ = 1`.

## Proof of the main theorem

Introduce the data of the statement and apply `norm_le_one_of_test`. Its
hypothesis for `testScalars j k 1` follows from `norm_le_one_of_diagonal` with
`S = testSet C D j k`. Its hypothesis for `testScalars j (D j).length (-1)`
follows from `norm_le_one_of_mem_center`. The facts these two lemmas need come
from `ProductLeviNecessityTest`.
