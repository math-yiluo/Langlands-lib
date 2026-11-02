# Square integrability of `Ξ` against a power of `1 + σ` (Lemma II.1.5)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrability`,
namespace `Langlands.HarishChandraSchwartz`. It imports only Mathlib.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082.

- I.1 (printed p. 241, PDF p. 7): `M₀¹` is compact, and `G` is the disjoint union of
  the double cosets `K m K` for `m ∈ M̄₀⁺ / M₀¹` (formula (4)). There are
  `C₁, C₂ > 0` with `C₁ δ₀(m)⁻¹ ≤ mes(K m K) ≤ C₂ δ₀(m)⁻¹` for `m ∈ M̄₀⁺`, where
  `δ₀ = δ_{P₀}` (formula (5)).
- I.1 (printed p. 242, PDF p. 8): with a Euclidean norm `|·|` on `a₀`, there are
  `C₁, C₂ > 0` with `C₁ (1 + |H₀(m)|) ≤ 1 + σ(m) ≤ C₂ (1 + |H₀(m)|)` for `m ∈ M₀`
  (formula (6)).
- Lemma II.1.1 (printed p. 251, PDF p. 17): `Ξ` is bi-`K`-invariant, and there are
  `C₁, C₂ > 0` and `d ∈ ℕ` with
  `C₁ δ₀(m)^{1/2} ≤ Ξ(m) ≤ C₂ δ₀(m)^{1/2} (1 + σ(m))^d` for `m ∈ M̄₀⁺`.
- Lemma II.1.5 (printed p. 252, PDF p. 18): there is `d ∈ ℕ` such that
  `∫_G Ξ(g)² (1 + σ(g))^{-d} dg` converges. Waldspurger's proof: by (4) it suffices
  that `∑_{m ∈ M̄₀⁺/M₀¹} mes(KmK) Ξ(m)² (1 + σ(m))^{-d}` converges. By (5) and
  Lemma II.1.1 it suffices that `∑_m (1 + σ(m))^{-d}` converges for `d` large. By (6)
  this follows from the convergence of `∑_{H ∈ H₀(M̄₀⁺)} (1 + |H|)^{-d}`, which is
  clear because `H₀(M₀)` is a lattice in `a₀`.

## Scope: abstract cells and explicit inputs

The reductive group, `K`, `M̄₀⁺`, `δ₀` and `H₀` are not constructed in this module.
The proof is carried out for abstract data, and every input of Waldspurger's proof is
an explicit hypothesis, collected in `CartanSquareBound`:

| Field | Source input | Status for Waldspurger's data |
|---|---|---|
| `countable`, `iUnion_cell` | I.1 (4): `G = ⋃ K m K`; the index set `M̄₀⁺/M₀¹` is countable because `H₀` embeds it in a lattice | structural fact of I.1, to be realized |
| `sigma_nonneg` | `σ = log‖·‖ ≥ 0` (I.1) | proved by `height_nonneg` in the published module `Height` |
| `delta_pos` | `δ₀ > 0` | holds for a modulus character |
| `measure_cell_le` | the upper bound of I.1 (5) | structural fact of I.1, to be realized |
| `abs_xi_le` | the upper bound of Lemma II.1.1, on the double coset | **open proof obligation** (Waldspurger proves it from Casselman's Proposition I.4.3) |
| `one_add_norm_le`, `injective` | the lower bound `C₁ (1 + |H₀(m)|) ≤ 1 + σ(m)` of I.1 (6), and injectivity of `m ↦ H₀(m)` on `M₀/M₀¹` | structural facts of I.1, to be realized |

The proof uses the upper bound of I.1 (5), the upper bound of Lemma II.1.1 and the
lower bound `C₁ (1 + |H₀(m)|) ≤ 1 + σ(m)` of I.1 (6) (in `one_add_norm_le`, with the
constant `C = C₁⁻¹`). The lower bounds of I.1 (5) and Lemma II.1.1 and the upper bound
of I.1 (6) are not used. Disjointness of the cells is not used either. Covering is
enough because the integral over `G` is bounded by the sum of the integrals over the
cells.

The upper bound of Lemma II.1.1 is a theorem of the source, not structural input. A
consumer must prove it for Waldspurger's `Ξ`; it cannot be assumed.

## Definitions

- `SquareIntegrableWeight μ Ξ σ : Prop`: there is `d : ℕ` with
  `∫⁻ g, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ))) ∂μ < ⊤`. This is the
  conclusion of Lemma II.1.5 for a measure `μ` and weights `Ξ σ : G → ℝ`, with the
  integral written as a lower Lebesgue integral of a nonnegative function.
- `CartanSquareBound μ Ξ σ cell L H δ : Prop`: the structure in the table above, for a
  measurable space `G`, a measure `μ`, `Ξ σ : G → ℝ`, an index type `ι`,
  `cell : ι → Set G`, a `ℤ`-submodule `L` of a real normed space `E`, `H : ι → L` and
  `δ : ι → ℝ`. Its fields are:
  - `countable : Countable ι` and `iUnion_cell : ⋃ i, cell i = univ`;
  - `sigma_nonneg : ∀ g, 0 ≤ σ g` and `delta_pos : ∀ i, 0 < δ i`;
  - `measure_cell_le`: there is `C : ℝ≥0` with `μ (cell i) ≤ C * ENNReal.ofReal (δ i)⁻¹`
    for all `i`;
  - `abs_xi_le`: there are real `C` and `d` with
    `|Ξ g| ≤ C * √(δ i) * (1 + σ g) ^ d` for all `i` and `g ∈ cell i`;
  - `one_add_norm_le`: there is `C > 0` with `1 + ‖H i‖ ≤ C * (1 + σ g)` for all `i`
    and `g ∈ cell i`;
  - `injective : Function.Injective H`.

  For Waldspurger's data, `ι = M̄₀⁺/M₀¹`, `cell i = K m K`, `E = a₀` with a Euclidean
  norm, `L = H₀(M₀)`, `H(m) = H₀(m)` and `δ(m) = δ₀(m)`. Since `Ξ` and `σ` are
  bi-`K`-invariant, the bounds on `K m K` are the bounds at `m`.

## Results

- `CartanSquareBound.of_representatives m hcount hcover hσ hδ hconst hmeas hxi hnorm hinj`:
  if `Ξ` and `σ` are constant on each cell, with the value at a point `m i` (hypothesis
  `hconst : ∀ i, ∀ g ∈ cell i, Ξ g = Ξ (m i) ∧ σ g = σ (m i)`), then the bounds of
  `CartanSquareBound` only need to be checked at the points `m i`. This is the form
  of I.1 (5), I.1 (6) and Lemma II.1.1 in the source. The module does not require
  `m i ∈ cell i`; only `hconst` is used.
- `summable_one_add_norm_rpow_neg L hs` (`E` finite-dimensional, `L` discrete, i.e.
  `[DiscreteTopology L]`): if `s > rank L`, then `∑_{z ∈ L} (1 + ‖z‖)^{-s}` converges.
  This is the last step of Waldspurger's proof.
- `CartanSquareBound.squareIntegrableWeight h` (`E` finite-dimensional, `L` discrete):
  `CartanSquareBound μ Ξ σ cell L H δ` implies `SquareIntegrableWeight μ Ξ σ`.
  This is Lemma II.1.5, from the inputs in the table. The exponent is
  `d = ⌈2 d' + rank L + 1⌉₊`, where `d'` is the exponent in `abs_xi_le`.

## Proof notes

The Lean proof follows Waldspurger's.

1. `summable_one_add_norm_rpow_neg`: for `z ≠ 0`, `(1 + ‖z‖)^{-s} ≤ ‖z‖^{-s}`.
   Mathlib's `ZLattice.summable_norm_rpow` gives the convergence of
   `∑_{z ∈ L} ‖z‖^{-s}` for `s > rank L`. The single term `z = 0` does not affect
   summability (`Summable.of_norm_bounded_eventually` with the cofinite filter).
2. Pointwise bound. Put `s = d − 2 d'`; the choice of `d` gives `s > rank L`. For
   `g ∈ cell i`, `abs_xi_le` gives `Ξ(g)² ≤ C₂² δ(i) (1 + σ(g))^{2d'}`, so
   `Ξ(g)² (1 + σ(g))^{-d} ≤ C₂² δ(i) (1 + σ(g))^{-s}`. By `one_add_norm_le`,
   `1 + σ(g) ≥ (1 + ‖H(i)‖) / C₆`, and since `-s ≤ 0`,
   `(1 + σ(g))^{-s} ≤ C₆^s (1 + ‖H(i)‖)^{-s}`.
3. Sum over the cells. The integral over `G = ⋃ cell i` is at most the sum of the
   integrals over the cells (`lintegral_iUnion_le`, `ι` countable). On `cell i` the
   integrand is at most the constant `δ(i) A (1 + ‖H(i)‖)^{-s}` with `A = C₂² C₆^s`.
   With `μ(cell i) ≤ C₅ δ(i)⁻¹`, the factor `δ(i)` cancels. The integral is at most
   `C₅ ∑_i A (1 + ‖H(i)‖)^{-s}`. Since `H` is injective, this is at most
   `C₅ ∑_{z ∈ L} A (1 + ‖z‖)^{-s}` (`ENNReal.tsum_comp_le_tsum_of_injective`), which is
   finite by step 1.
