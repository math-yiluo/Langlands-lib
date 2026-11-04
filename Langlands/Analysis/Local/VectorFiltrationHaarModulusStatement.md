# Haar moduli along a filtration with vector-space quotients

Author: Worker 1423.

`Langlands.HaarModulus.VectorFiltrationHaarModulusStatement` is a proposition
definition awaiting proof. It states that the Haar modulus of conjugation by an
element `g` on a closed subgroup `U` is the product of the absolute values of
the determinants of the linear maps that `g` induces on the successive
quotients of a finite `g`-stable filtration of `U` whose quotients are finite
dimensional vector spaces over a nonarchimedean local field `k`. The module
supplies no proof and no axiom. It imports `Langlands.Group.HaarModulus`,
`Mathlib.NumberTheory.LocalField.Basic` and
`Mathlib.MeasureTheory.Measure.Haar.DistribChar` unchanged.

## Binders and hypotheses

- `k : Type u` is any nonarchimedean local field, given by
  `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]`.
  Positive characteristic is included.
- `G : Type v` is any locally compact Hausdorff topological group.
- `U : Subgroup G` is closed (`hU`). The hypothesis `_hcover` says that every
  element of `U` lies in a compact open subgroup of `U` (topology of `U` as a
  subspace of `G`).
- `g` is any element of `Subgroup.normalizer (U : Set G)`.
- `F : ℕ → Subgroup G` is a chain of subgroups of `G`, with `N : ℕ`, such that
  `F 0 = U` (`_hF0`), `F N = ⊥` (`_hFN`), `F (r + 1) ≤ F r` for `r < N`
  (`_hFle`), and `g` normalizes `F r` for `r < N` (`_hFg`). Only the values
  `F 0, …, F N` matter.
- For each `r`, `n r : ℕ` and `q r : F r → (Fin (n r) → k)` is a map from the
  subgroup `F r` (subspace topology) to the coordinate space `k^(n r)` (product
  topology). For `r < N` it is required to be a homomorphism from the group
  `F r` to the additive group of `k^(n r)` (`_hqmul`), with kernel exactly
  `F (r + 1)` (`_hqker`), continuous (`_hqc`), open (`_hqo`) and surjective
  (`_hqs`). Thus `q r` identifies the topological group `F r / F (r + 1)` with
  `k^(n r)`.
- For each `r`, `L r` is a `k`-linear automorphism of `k^(n r)`. For `r < N` the
  hypothesis `_hqL` says that it is the map induced by conjugation by `g`: if
  `x, y ∈ F r` and `y = g x g⁻¹`, then `q r y = L r (q r x)`.

The values of `n`, `q` and `L` at `r ≥ N` are irrelevant.

## Conclusion and conventions

The left side is `HaarModulus.closedNormalizerCharacter U hU g`, coerced to
`ℝ≥0`. It is `mulEquivHaarChar` of the conjugation `u ↦ g u g⁻¹` of `U`, which
the Library's `normalizerCharacter_smul_map` characterizes by
`c(g) • map (u ↦ g u g⁻¹) μ = μ` for a Haar measure `μ` on `U`. Hence
`μ(g S g⁻¹) = c(g) μ(S)`: the forward scaling factor.

On the right, `LinearEquiv.det (L r) : kˣ` is the determinant of `L r`, and
`MeasureTheory.distribHaarChar k : kˣ →* ℝ≥0` is Mathlib's Haar scaling
character of `kˣ` acting on `k` by multiplication. By `distribHaarChar_mul`,
`distribHaarChar k a * ν(s) = ν(a • s)` for a Haar measure `ν` on `k`, so it is
the forward scaling factor of multiplication by `a`, classically the normalized
absolute value `|a|_k`. The conclusion is

`c(g) = ∏_{r < N} |det (L r)|_k`,

with the product over `Finset.range N`. Both sides have the forward
orientation.

## Provenance

Provenance: internal.

This is an internal reduction step for the Library target
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentHaarDeterminantStatement`
(Haar scaling on a rational dynamic unipotent subgroup is the adjoint
determinant). It separates the measure-theoretic content of that statement from
its algebraic content. The algebraic part, a separate statement, is to supply
for the rational points of the dynamic unipotent subgroup a filtration with the
properties above whose graded determinants multiply to the adjoint determinant.
The covering hypothesis `_hcover` holds there by the Library's
`Langlands.BruhatTits.dynamicUnipotentCompactOpenContainment`.

The mathematics is the standard dévissage of Haar moduli. If `H` is a closed
normal subgroup of a locally compact group stable under a topological
automorphism `α`, the modulus of `α` is the product of the moduli of its
restriction to `H` and of the induced automorphism of the quotient. Each `F r`
is closed (`F (r + 1)` is the preimage of `0` under the continuous map `q r`)
and, by `_hcover`, every element of it lies in a compact open subgroup, so it is
unimodular. Applying the dévissage along the chain reduces the claim to the
quotients `F r / F (r + 1) ≅ k^(n r)`, where the modulus of a linear automorphism
is the absolute value of its determinant. The same computation, with lattice
filtrations of compact open subgroups instead of Haar measures, underlies the
classical formula for the modulus of a parabolic subgroup, for example in
Renard's proof of the Lemme in Section V.5.4 of *Représentations des groupes
réductifs p-adiques* (source
`renard-2026-representations-groupes-reductifs-padiques`). The statement is not
taken from any source, and no source formulates it in this generality.

The hypotheses are not vacuous: for `U = ⊥`, `N = 0` and `F r = ⊥` they hold
trivially, and the conclusion is the true identity `c(g) = 1`.
