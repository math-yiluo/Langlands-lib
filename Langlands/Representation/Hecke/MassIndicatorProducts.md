# Products of mass-one double-coset indicators

Module `Langlands.Representation.Hecke.MassIndicatorProducts`, namespace
`Langlands.Hecke`. Worker 127 wrote it for Task 5575, the proof of Renard V.5.3
(`Langlands.Hecke.IwahoriHeckeDecompositionStatement`).

These are supporting lemmas, derived for this proof rather than taken from the
source. They hold for any Hausdorff topological group `G` with a Borel structure
and a Haar measure `μ`, and any open subgroup `K` with compact underlying set
(`hK`). The element `massIndicator K hK μ g`, written `a g` below, is the published
mass-one indicator of `K g K` from `Langlands.Representation.Hecke.DoubleCosetSandwich`.
The module also includes two purely combinatorial lemmas.

## Declarations

- `HeckeAlgebra.Corner.evalLinear x`: evaluation `f ↦ f x` of corner elements,
  as a `ℂ`-linear functional. `evalLinear_apply` is its defining equation.
- `massIndicator_eq_of_mem`: if `a' ∈ K g K` then `a a' = a g`. The proof uses
  `massIndicator_apply` and `doubleCosetSet_eq_of_mem`.
- `massIndicator_apply_self_ne_zero`, `massIndicator_apply_of_notMem`: `a g` is
  nonzero at `g` (because `K g K` has positive mass) and vanishes off `K g K`.
- `massIndicator_eq_iff`: `a g₁ = a g₂ ↔ g₁ ∈ K g₂ K`. For `→`, evaluate at `g₁`.
- `linearIndepOn_range_massIndicator`: the set of all `a g` is linearly
  independent. In a vanishing finite combination, evaluate at a representative
  `g` of one member. Every other member `a h ≠ a g` vanishes at `g`, because
  `g ∈ K h K` would force `a h = a g`. So the coefficient of `a g` is zero.
- `finite_image_massIndicator`: for compact `S`, the set `a '' S` is finite.
  Finitely many cosets `g K` cover `S`, and `y ∈ g K` gives `a y = a g`.
- `massIndicator_mul_of_normalizes`: if `x⁻¹ k x ∈ K` for all `k ∈ K`, then
  `a g * a x = a (g x)`. `massIndicator_mul_of_normalizes'`: if `x k x⁻¹ ∈ K`
  for all `k ∈ K`, then `a x * a g = a (x g)`. Both use the published criterion
  `massIndicator_mul` (`g₁ K g₂ ⊆ K g₁ g₂ K`), via
  `g k x = (g x)(x⁻¹ k x)` and `x k g = (x k x⁻¹)(x g)`.
- `TestFunction.mul_mem_doubleCosetSet_of_factor_left`: suppose every `k ∈ K` is
  `p q r` with `p ∈ P`, `q ∈ Q`, `r ∈ R`. If `g₁ P g₁⁻¹ ⊆ K`, `g₁ Q g₁⁻¹ ⊆ K` and
  `g₁ R g₂ ⊆ K g₁ g₂ K`, then `g₁ K g₂ ⊆ K g₁ g₂ K`. This follows from
  `g₁ p q r g₂ = (g₁ p g₁⁻¹)(g₁ q g₁⁻¹)(g₁ r g₂)`.
- `TestFunction.mul_mem_doubleCosetSet_of_factor_right`: the mirror version. If
  `g₂⁻¹ Q g₂ ⊆ K`, `g₂⁻¹ R g₂ ⊆ K` and `g₁ P g₂ ⊆ K g₁ g₂ K`, then
  `g₁ K g₂ ⊆ K g₁ g₂ K`, from `g₁ p q r g₂ = (g₁ p g₂)(g₂⁻¹ q g₂)(g₂⁻¹ r g₂)`.
- `exists_finite_le_of_label` (Dickson's lemma with a finite label): take
  `φ : X → ι → ℕ` with `ι` finite, a label `V : X → β` with `β` finite, and a
  set `s`. Then there is a finite `T ⊆ s` such that every `x ∈ s` has some
  `t ∈ T` with `φ t ≤ φ x` and `V t = V x`. For each label `b`, the minimal
  elements of `φ '' {y ∈ s | V y = b}` form an antichain. That antichain is
  finite because `ι → ℕ` is well-quasi-ordered (`Pi.wellQuasiOrderedLE`). Every
  element lies above a minimal one (`Set.IsPWO.exists_le_minimal`), and one
  preimage is chosen for each minimal element.
- `exists_finset_test_rightInvariant`: for compact `W` there is a finite set
  `t` with the following property. Two right-`K`-invariant subsets of `W` that
  contain the same points of `t` are equal. Cover `W` by finitely many cosets
  `g K` with `g ∈ t`. If `u ∈ U₁`, `u ∈ g K` and `g⁻¹ u ∈ K`, then `g ∈ U₁`,
  hence `g ∈ U₂`, hence `u ∈ U₂`. `exists_finset_test_leftInvariant` is the same
  statement with cosets `K g`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.DoubleCosetSandwich` | `massIndicator`, `massIndicator_apply`, `massIndicator_mul`, `doubleCosetSet` lemmas |
| `Mathlib.Order.WellQuasiOrder` | `Pi.wellQuasiOrderedLE`, `WellQuasiOrderedLE.finite_of_isAntichain` |
| `Mathlib.Order.WellFoundedSet` | `Set.isPWO_of_wellQuasiOrderedLE`, `Set.IsPWO.exists_le_minimal` |
