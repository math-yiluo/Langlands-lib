# Proof of the JPSS arbitrarily small lower-block Whittaker localization

Author: Worker 234.

The theorem `Langlands.Whittaker.lowerBlockWhittakerLocalization` proves
exactly the published proposition
`Langlands.Whittaker.LowerBlockWhittakerLocalizationStatement.{uF,uV}` from
`Langlands.Representation.Whittaker.LowerBlockLocalizationStatement`. The
statement module and every module it imports are unchanged. The theorem
keeps both independent universes `uF` and `uV`. It adds no hypothesis: no
irreducibility, no measure, no localization operator and no analytic
comparison. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

The proof is complete for every prime `p`, every `F : PadicField.{uF} p`
with the canonical topology, every unitary additive character `ψ`, all
block sizes `0 < a`, `0 < d`, `c = c₀ + 1`, and every Whittaker-type
representation. It also covers every coefficient `W` in the actual
`whittakerSet` and every pair of neighborhoods `Ux ∈ 𝓝 0`, `Uh ∈ 𝓝 1`.
The witnesses `Ω₁`, `Ω₂` and `W₀` are chosen after `W`, `Ux` and `Uh`,
and before the chart arguments `g`, `x`, `h`, as the statement requires.

## Relation to the source

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, Amer. J. Math. 105 (1983), section 9.2,
printed pages 454–455 (registered source `jpss-1983-rankin-selberg`). The
statement Markdown records the errata check for these pages. JPSS define
`W_μ` recursively, row by row:

```text
W_μ(g) = ∫ W_{μ-1}(g n(u,v)) φ_μ(u,v) du dv.
```

Here `n(u,v)` is the unipotent matrix whose only off-diagonal entries are
the column `(u, v)` just above the diagonal entry `μ+1`. The Fourier
transform `φ̂_μ` cuts the last row `(x, h)` of the chart down to a compact
open set. The "easy ascending induction" is left to the reader.

The Lean proof follows the same row-by-row scheme, with three changes.

* Each average is a **finite sum** of translates
  `∑ c_t • π(1 + t e_{l,ρ+1}) w`. The coefficients `c_t` come from
  character orthogonality on a finite quotient of two lattices. So every
  intermediate function, and the final `W₀`, is literally
  `g ↦ ℓ (π g w)` for the *same* functional `ℓ` as `W`. Hence `W₀` lies in
  the same `whittakerSet` with no closure or integration argument.
* The support of the averaged function is controlled pointwise by the
  smoothness of the averaged vector (the *support step* below). This
  replaces the Fourier-transform identity on printed page 455.
* The congruence precision of row `k` of the middle block is chosen after
  the vector of the previous rows is known, so it shrinks with `k`. The
  resulting `Ω₂` is a *row-graded* congruence subgroup of the lower
  triangular group. It is a subgroup because the precisions are all at
  most `-1` (lemmas `mul_rowBox` and `inv_rowBox`).

The induction runs over the `d` middle rows and is proved for arbitrary
matrices `M` of a fixed shape (statement `main_claim`), not only for chart
points.

## Notation

`T : F.TopologicalData` is a topological datum and
`L(k) = T.additiveLattice k` is `{x | v(x) ≤ exp k}`, that is
`ϖ^(-k) O` (`lattice_eq_image`). So `L(k) ⊆ L(k')` for `k ≤ k'`,
`L(A) L(B) ⊆ L(A + B)` (`lattice_mul`), and `L(-1) = ϖ O`. The integer
`n(ψ) = T.additiveConductor ψ` is the published conductor: `ψ` is trivial
on `L(n(ψ))` and nontrivial on `L(n(ψ)+1)`. The auxiliary results are
stated for a general `T` in namespace
`Langlands.Whittaker.LowerBlockLocalizationProof`. Where a topology is
needed they take `[τ : TopologicalSpace F.Carrier] (hτ : τ = T.topology)`
or install `T.topology` locally. The final theorem uses
`T = F.canonicalTopologicalData`. Decidability of the propositions in `if`
expressions is classical (`open Classical`).

## Implemented proof

### 1. Lattices

The published `PadicField.TopologicalData.isCompact_additiveLattice` and
`PadicField.TopologicalData.isOpen_additiveLattice` show that each `L(k)` is
compact and open. This proof reuses them from
`Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`.
`one_add_ne_zero` shows that `1 + x ≠ 0` for `x ∈ L(k)` with `k ≤ -1`.
`exists_mem_lattice` puts every element in some lattice.

### 2. Annihilators and finite character sums

* `annihilator_iff`: `ψ(s y) = 1` for all `s ∈ L(A)` if and only if
  `y ∈ L(n(ψ) − A)`. The forward direction uses the published
  `exists_nontrivial_at_conductor_succ`, rescaled by `y⁻¹`. The converse
  uses `lattice_mul` and the conductor property.
* `exists_character_sum`: for all `B`, `S` and `e`, there are a finite set
  `s` and coefficients `c : F → ℂ` with

  ```text
  ∑_{t ∈ s} c t · ψ(t y) = 1 if y − e ∈ L(S), and 0 otherwise,
  ```

  for every `y ∈ L(B)`. Put `B' = max(B, S, b)` with `e ∈ L(b)`,
  `A = L(n(ψ) − S)` and `A' = L(n(ψ) − B')`. The quotient `A ⧸ A'` is
  finite because `A` is compact and `A'` is open. The set `s` consists of
  representatives `r_q` of its classes, and `c_t = ψ(−t e)/|A ⧸ A'|`.
  The sum equals `|A ⧸ A'|⁻¹ ∑_q ψ(r_q (y − e))`. If `y − e ∈ L(S)`, every
  term is `1`. Otherwise `annihilator_iff` gives `t₀ ∈ A` with
  `ψ(t₀ (y − e)) ≠ 1`. Translating the classes by `t₀` multiplies the sum
  by that value. The translation is well defined because `y − e ∈ L(B')`
  and `ψ` is trivial on `A' · L(B') ⊆ L(n(ψ))`. Hence the sum is `0`.

### 3. Lattice boxes inside neighborhoods

* `exists_pi_box`: a neighborhood in a finite product contains a uniform
  box, given a monotone basis of boxes in each factor (`nhds_pi`,
  `Filter.mem_pi`).
* `exists_scalar_box` uses the published `exists_additiveLattice_subset`;
  `exists_matrix_box` applies the product lemma twice.
* `exists_unit_box`: every neighborhood of `1` in `GL_m` contains all `g`
  such that `g` and `g⁻¹` are entrywise congruent to `1` modulo one
  lattice. The proof describes the units topology through Mathlib's
  `Units.isInducing_embedProduct` and the product neighborhood filter.
* `exists_fixing_box`: by smoothness, a vector `w` is fixed by an open
  subgroup of `GL_m`, which contains such a box; so the box fixes `w`.

### 4. Row-graded congruences (Lemma D)

Let `g` be lower triangular with `g_{ij} − δ_{ij} ∈ L(R i)` and all
`R i ≤ −1`.

* `discreteValuation_det`: `det g` is the product of the diagonal entries.
  Each lies in `1 + ϖO`, so `v(det g) = 1`.
* `inv_rowBox`: the same row-graded congruence holds for `g⁻¹`. The
  adjugate of the integral matrix `g` is integral (`RingHom.map_adjugate`
  over `T.Integers`), and `det g` is a unit, so `g⁻¹` is integral. Then
  `g⁻¹ − 1 = −(g − 1) g⁻¹` puts row `i` of `g⁻¹ − 1` in
  `L(R i) · O ⊆ L(R i)`.
* `mul_rowBox` (section 8): such boxes are closed under products, by
  `AB − 1 = (A − 1)(B − 1) + (A − 1) + (B − 1)` and
  `L(R i) L(R l) ⊆ L(R i)`.

### 5. Elementary matrices and one averaging step

Work in `GL_{n+1}` with the standard character on the upper unipotent
group. Fix a row `ρ : Fin n`, viewed as `ρ.castSucc`, and a column
`l < ρ + 1`. Let `E(t) = elementary l (ρ+1) t` be the transvection
`1 + t e_{l,ρ+1}`.

* `conj_elementary_val` and `conj_elementary_mem`: if the rows of `M` from
  `ρ + 1` on are standard basis rows, then `M E(t) M⁻¹ = 1 + t (M e_l)
  e_{ρ+1}ᵀ`, and this matrix is upper unipotent.
* `superdiag_conj_elementary` and `coeff_elementary`: its superdiagonal sum
  is `t M_{ρ l}`. Hence, for every `ℓ` in the Whittaker functional space
  `glFunctionals`,
  `ℓ(π(M) π(E(t)) w) = ψ(t M_{ρ l}) ℓ(π(M) w)`.
* `column_step` (support step and cut): for all `e` and `P` there is `w'`
  such that, for every such `M`,
  `ℓ(π(M) w') = [M_{ρ l} − e ∈ L(P)] · ℓ(π(M) w)`. Take `S₁` from
  `exists_fixing_box` for `w`, apply `exists_character_sum` with
  `B = n(ψ) − S₁`, and put `w' = ∑ c_t • π(E(t)) w`. If
  `ℓ(π(M) w) ≠ 0`, then `E(t)` fixes `w` for `t ∈ L(S₁)` (`elementary_box`).
  Hence `ψ(t M_{ρ l}) = 1` on `L(S₁)`, and `annihilator_iff` gives
  `M_{ρ l} ∈ L(B)`. There the character sum is the indicator. If
  `ℓ(π(M) w) = 0`, both sides vanish.
* `row_step`: induction over a finite set of columns `l < ρ + 1` applies
  `column_step` repeatedly. It cuts the whole row down to
  `M_{ρ l} − e_l ∈ L(P)` for all those columns at once.

### 6. Row-by-row localization (`main_claim`)

Fix `ℓ`, the vector `v`, block sizes with `a + d ≤ n`, and a precision
`S₀ ≤ −1`. For each `k ≤ d` there are a vector `w` and precisions
`S : ℕ → ℤ` with all `S i ≤ S₀` with the following property. Let `M` and
`M₀` in `GL_{n+1}` satisfy:

1. the rows of `M` from `a + k` on are standard basis rows;
2. `M_{ij} = 0` whenever `a ≤ j` and `i < j`;
3. `M₀` agrees with `M` in the rows `< a`, and its other rows are standard.

Then

```text
ℓ(π(M) w) = ℓ(π(M₀) v)  if M_{ij} − δ_{ij} ∈ L(S(i − a)) for a ≤ i < a + k,
            0           otherwise.
```

The base case `k = 0` takes `w = v`, since then `M₀ = M`. For the step
from `k` to `k + 1`, let `w₀, S` be the data for `k`, let `ρ = a + k`, and
let `S₁` be a fixing box of `w₀`. Put `P = min(S₀, S₁)`. Apply `row_step`
to row `ρ` with target the identity row, precision `P`, and all columns
`l ≤ ρ`. The entries of row `ρ` right of the diagonal vanish by (2), so
the condition is the full row congruence `M_{ρ j} − δ_{ρ j} ∈ L(P)`. The
new precisions are `S` with the value at `k` replaced by `P`.

If the row congruence fails, both sides are `0`. If it holds, let `κ` be
the identity matrix with row `ρ` replaced by row `ρ` of `M`. It is lower
triangular and row-graded congruent to `1` modulo `L(P)`, so it is
invertible (`discreteValuation_det`; `mkOfDetNeZero`). By `inv_rowBox` it
lies in the fixing box of `w₀`, so `π(κ) w₀ = w₀`. Column `ρ` of `M`
vanishes off the diagonal by (1) and (2), so `M κ⁻¹` is `M` with row `ρ`
replaced by the identity row. Then `ℓ(π(M) w₀) = ℓ(π(M κ⁻¹) w₀)`, and
`M κ⁻¹` satisfies hypotheses (1)–(3) for `k` with the same `M₀`. Its
congruence conditions in the rows `a, …, a + k − 1` are those of `M`.
The induction hypothesis then gives the claim for `k + 1`.

### 7. The chart

For the published chart
`lowerBlockLocalization c g x h = [[g,0,0],[x,h,0],[0,0,I_c]]`, the
published entry formulas `lowerBlockLocalization_11` … `_33`, together
with the local lemma `fin_blocks_cases` (every index of `Fin (a+d+c)` lies
in the image of one of the three published block embeddings), give:

* `chart_lastRows`: the rows from `a + d` on are standard basis rows;
* `chart_upper`: entries above the diagonal vanish in the columns from `a`
  on, since `h` is lower triangular;
* `chart_diag`: `lowerBlockLocalization c g 0 1` agrees with the chart in
  the first `a` rows and is the identity in the other rows;
* `chart_cond`: the congruence of the middle rows `a + i` modulo
  `L(S i)` is equivalent to the pair of conditions
  `x_{ij} ∈ L(S i)` and `h_{ij} − δ_{ij} ∈ L(S i)`.

### 8. The subgroups

`mul_rowBox` is described in section 4. `isOpen_entryBox` shows that the
entrywise row-graded box is open in `GL_m`: it is a finite intersection of
preimages of open lattices under the continuous entry maps.
`isCompact_rowBox` shows that the lower triangular row-graded box is
compact in `GL_m`. It is closed, since lower triangularity and the lattice
conditions are closed. By `inv_rowBox` it is contained in the published
compact group `GL_m(O)` (`isCompact_integralSubgroup`).

### 9. The theorem

Write `W = g ↦ ℓ(π(g) v)`, using the definition of `whittakerSet` as the
union of coefficient-map ranges. Then:

* By `exists_matrix_box`, all `x` with entries in `L(Sx)` lie in `Ux`.
* `Uh` contains the subtype preimage of a neighborhood `U'` of `1` in
  `GL_d`. By `exists_unit_box`, `U'` contains every `g` such that `g` and
  `g⁻¹` are entrywise congruent to `1` modulo `L(Sh)`.
* Apply `main_claim` with `n = a + d + c₀`, `k = d` and
  `S₀ = min(−1, Sx, Sh)`, giving `w` and `S`.

Define

```text
Ω₁ = { x | x_{ij} ∈ L(S i) for all i, j }                    (AddSubgroup),
Ω₂ = { h lower triangular | h_{ij} − δ_{ij} ∈ L(S i) }       (Subgroup),
W₀ = coefficientMap π ℓ w,  i.e.  g ↦ ℓ(π(g) w).
```

`Ω₂` is closed under products by `mul_rowBox` and under inverses by
`inv_rowBox`.

* `Ω₁` equals the finite product `Set.univ.pi` of the compact open
  lattices `L(S i)`, so it is compact and open. It lies in `Ux` because
  `S i ≤ Sx`.
* `Ω₂` is compact in the lower triangular group by `Subtype.isCompact_iff`
  and `isCompact_rowBox`. It is open there as the subtype preimage of
  `isOpen_entryBox`. It lies in `Uh` because `S i ≤ Sh` and `inv_rowBox`
  controls `h⁻¹`.
* `W₀` lies in the same `whittakerSet` with the same `ℓ`.

For any `g`, `x` and `h`, the chart point `M = lowerBlockLocalization c g x h`
and `M₀ = lowerBlockLocalization c g 0 1` satisfy the hypotheses of
`main_claim` by `chart_lastRows`, `chart_upper` and `chart_diag`. By
`chart_cond`, its congruence condition is exactly `x ∈ Ω₁ ∧ h ∈ Ω₂`.
This gives `W₀(M) = W(M₀)` on the product and `W₀(M) = 0` off it, for all
`g`, `x` and `h`.

## Imports

* `Langlands.Representation.Whittaker.LowerBlockLocalizationStatement`
  (the target and, through it, the chart, Whittaker functionals and
  coefficient maps);
* `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`
  (`isCompact_additiveLattice`, `isOpen_additiveLattice`);
* `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof`
  (`mul_mem_additiveLattice_iff`, `mem_additiveLattice_iff_exists_integer`,
  and the conductor results);
* `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`
  (`isCompact_integers`, `isOpen_integers`);
* `Langlands.Group.GL.IntegralSubgroup` (`isCompact_integralSubgroup`);
* `Langlands.LocalField.Topology`.
