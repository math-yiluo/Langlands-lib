# The group-theoretic core of Renard V.5.3

Module `Langlands.Representation.Hecke.IwahoriHeckeCore`, namespace
`Langlands.Hecke`. Worker 127 wrote it for Task 5575, the proof of Renard V.5.3
(`Langlands.Hecke.IwahoriHeckeDecompositionStatement`).

The module contains supporting results derived for the proof. They abstract the
arguments of Renard, *Représentations des groupes réductifs p-adiques* (registered
source `renard-2026-representations-groupes-reductifs-padiques`), V.5.3, printed
pp.123–125 / PDF pp.129–131. The finiteness Lemma does not use Renard's argument
on `ℕ^d`. That argument relies on V.3.24, which fails in general; see the statement's
Markdown. The module replaces it with Dickson's lemma applied to floor coordinates.

Throughout, `G` is a Hausdorff topological group with Borel structure and Haar
measure `μ`. `K` is an open subgroup with compact underlying set, and
`a g = massIndicator K hK μ g`.

## Sandwich spanning

`span_sandwich_eq_top` takes the following hypotheses:

- a subgroup `K₀` normalizes `K`;
- every `g` is `p₁ t p₂` with `p₁, p₂ ∈ K₀` and `t ∈ T`;
- every `a t` (`t ∈ T`) lies in the span of a set `S`.

The conclusion is that the products `a x₁ * s * a x₂` (`x₁, x₂ ∈ K₀`, `s ∈ S`)
span the corner. The corner is spanned by the double-coset elements
(`span_range_doubleCoset`), each a nonzero multiple of `a g`
(`doubleCoset_eq_smul_massIndicator`). Normality gives
`a (p₁ t p₂) = a p₁ * a t * a p₂` (`massIndicator_mul_of_normalizes` and its
primed version). The linear map `u ↦ a p₁ * u * a p₂` sends the span of `S` into
the span of the products (`Submodule.span_induction`).

## Lattice data and products

`IwahoriLatticeData K Λ ι` bundles the following data:

- three subsets `Kn`, `Km`, `Knb` of `K` (for `K ∩ N`, `K ∩ M`, `K ∩ N̄`) with
  `K = Kn · Km · Knb` elementwise (`decomp`);
- a map `c : Λ → G` from an additive group with `c (y + y') = c y * c y'`;
- root pairings `pair : ι → Λ →+ ℤ`.

Call `y` *dominant* when `0 ≤ pair α y` for all `α`. For dominant `y`, the data
require `c y Km (c y)⁻¹ ⊆ K` and `(c y)⁻¹ Km (c y) ⊆ K` (`conj_Km`),
`c y Kn (c y)⁻¹ ⊆ Kn` (`conj_Kn`) and `(c y)⁻¹ Knb (c y) ⊆ Knb` (`conj_Knb`).

- `c_sub_mul`, `mul_c_sub`: `c (y - t) * c t = c y` and `c t * c (y - t) = c y`.
- `massIndicator_mul_dominant` (Renard's second Lemma): for dominant `y₁, y₂`,
  `a (c y₁) * a (c y₂) = a (c (y₁ + y₂))`. Apply the left three-factor criterion
  with `P = Kn`, `Q = Km`, `R = Knb`. For `nb ∈ Knb`,
  `c y₁ nb c y₂ = (c y₁ c y₂)((c y₂)⁻¹ nb c y₂)`.

## Finiteness Lemma

`int_le_of_natFloor_add_le`: if `0 ≤ n + e` and `0 ≤ m + e` (with `m, n ∈ ℤ`,
`e ∈ ℝ`) and `⌊n + e⌋₊ ≤ ⌊m + e⌋₊`, then `n ≤ m`. The proof uses
`⌊k + e⌋ = k + ⌊e⌋`.

`exists_finite_stable_representatives`: let `φ : X → ι → ℕ` (`ι` finite) reflect
a relation `R` on a set `S`. Let `V y` be sets with `V y ⊆ B t` (`B t` compact)
whenever `y ∈ S` and `R t y`. Assume two sets `V y`, `V y'` inside a common
compact set are equal once they agree on a finite test set. Then a finite
`T ⊆ S` gives, for every `y ∈ S`, some `t ∈ T` with `R t y` and `V t = V y`.

The proof applies Dickson's lemma (`exists_finite_le_of_label`) twice. The first
application, with no label, gives a finite `T₀`, so every `V y` lies in the
compact `W = ⋃_{t ∈ T₀} B t`. The second application uses the label
`y ↦ {g ∈ tW | g ∈ V y}`, where `tW` is the finite test set of `W`.

Fix admissibility offsets `e : ι → Fidx → ℝ`, a finite type `Fidx` and elements
`fe : Fidx → G`. A pair `(y, f)` is *admissible* when
`0 ≤ pair α y + e α f` for all `α`. In the application this means that
`ϖ^y f` is dominant.

- `dominant_sub_of_floor_le`: for admissible `t, y` with the same `f`, the floor
  coordinates `α ↦ ⌊pair α · + e α f⌋₊` reflect the order. So
  `φ t ≤ φ y` implies that `y - t` is dominant.
- `exists_finite_left` (Renard's finiteness Lemma, module form): there is a finite
  set `T` of admissible pairs with the following property. Every admissible
  `(y, f)` has some `(t, f) ∈ T` and a dominant `z = y - t` with
  `a (c z) * a (c t * fe f) = a (c y * fe f)`.

  For each `f`, take `V y = (c y)⁻¹ Knb (c y) fe f K`. It is right-`K`-invariant
  and contained in `B t = (c t)⁻¹ K (c t) fe f K` when `y - t` is dominant,
  because `conj_Knb` gives `(c y)⁻¹ Knb c y ⊆ (c t)⁻¹ K c t`.
  `exists_finite_stable_representatives` then gives finitely many `t` with
  `V t = V y`.

  The product formula comes from the left criterion (`P = Kn`, `Q = Km`,
  `R = Knb`). For `nb ∈ Knb`, the element `(c t)⁻¹ nb c t fe f` lies in
  `V t = V y`, so it equals `(c y)⁻¹ nb' c y fe f k`. Hence
  `c z nb c t fe f = nb' (c y fe f) k ∈ K (c y fe f) K`.
- `exists_finite_right` (Renard's Remark): the same statement with
  `a (c t * fe f) * a (c z) = a (c y * fe f)`. It assumes that dominant `c y`
  commute with every `fe f`.

  Take the left-`K`-invariant sets
  `V y = K (c y fe f) Kn (c y fe f)⁻¹ ⊆ K (c t fe f) K (c t fe f)⁻¹`, using
  `c y fe f = c t fe f c (y - t)` for dominant `y - t`. The mirror criterion
  applies with `Q = Km` and `R = Knb` conjugated by `(c z)⁻¹`. For `n ∈ Kn`,
  `(c t fe f) n (c t fe f)⁻¹ ∈ V t = V y` gives
  `c t fe f n c z = k (c y fe f) n'`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.MassIndicatorProducts` | product criteria, Dickson with label, test sets |
| `Mathlib.Algebra.Order.Floor.Ring` | `Int.floor_intCast_add`, `Int.natCast_floor_eq_floor` |
