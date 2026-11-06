# Conic bounds from Levi-orthogonal root weights

Lean module: `Langlands.LinearAlgebra.RootFaceCone`,
namespace `Langlands.LinearAlgebra.RootFaceCone`.

## Purpose and provenance

Provenance: internal. This is a finite-dimensional convex-geometry lemma written for the
convergence of the standard intertwining integrals (Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), IV.1.1, printed pp. 278–280). It is not
transcribed from a source. Waldspurger proves convergence by induction along a gallery of
parabolic subgroups. Here the decay of `δ_P^{1/2} χ` at Levi components on `Ū(F) ∩ U'(F)`
is instead obtained pointwise from line inequalities. The lemma is the combinatorial step that
turns those inequalities into decay.

Intended reading: `E` is the real character space of the split component `A` of a Levi `M`,
`B` the induced positive form, `Φ` the relative roots of `A`, and `m α` their multiplicities.
For a cocharacter `μ` whose `B`-dual is `y`, `rootWeight B Φ m y` is then the restriction to `A`
of the determinant of the adjoint action on the Lie algebra of the radical of `P(μ)`. The
inequality `H r ≥ -c` is the lower Iwasawa bound for the corresponding line, available when
`P(μ)` contains `Ū ∩ U'`, that is `B α r ≤ 0` for every `α` in the set `S` of roots of
`U ∩ Ū'`. Lines only for parabolics containing `P̄` (the opposite of `P`) or `P'` do not
suffice; all of these contain `Ū ∩ U'`. Equivalently, the bounds `H(2ρ_Q) ≤ c` for `Q ⊇ P` and
`H(2ρ_{Q'}) ≥ -c` for `Q' ⊇ P'` do not suffice, since `ρ_{Q̄} = -ρ_Q`. In `GL₄`, take
`P = B` upper triangular and `P'` the Borel subgroup of the order `(2,3,4,1)`. For `t ≥ 0`,
`H = t(-1,1,-1,1)` satisfies all of those inequalities with `c = 0`. For `R > 0`,
`μ = (2R, 0.9R, -2R, 0.9R)` satisfies `μ(α^∨) > R` on `S = {e₁-e₂, e₁-e₃, e₁-e₄}`, while
`μ(H) = 1.8Rt`, which is unbounded above. This motivates the family of all admissible `r` used
here. The module itself states only the linear
algebra below; no group appears in it.

## Setting and notation

- `E` is a real vector space, `B : LinearMap.BilinForm ℝ E`, `Φ : Finset E` and `m : E → ℝ`.
  No finite-dimensionality, symmetry or nondegeneracy is assumed globally. Each theorem lists
  its hypotheses.
- `rootWeight B Φ m y = ∑_{α ∈ Φ, 0 < B α y} m α • α`, written `ρ(y)` below.
- `closedFace B Φ y` is the set of `z` such that for every `α ∈ Φ`: `B α y = 0` implies
  `B α z = 0`, `0 < B α y` implies `0 ≤ B α z`, and `B α y < 0` implies `B α z ≤ 0`.
- `nonvanishingRoots B Φ y` is the finset of `α ∈ Φ` with `B α y ≠ 0`.
- The span is `Submodule.span ℝ Φ`. Roots always occupy the first argument of `B`.

The recurring hypotheses are:

- `hpos`: `0 < B x x` for every `x ≠ 0`;
- `hneg`: `-α ∈ Φ` for every `α ∈ Φ`;
- `hm`: `0 < m α` for every `α ∈ Φ`;
- `hlevi` (Levi orthogonality): for all `y` and `α ∈ Φ`, `B α y = 0` implies
  `B α (ρ y) = 0`.

## Declarations

- `rootWeight`, `closedFace`, `nonvanishingRoots`: the definitions above.
- `apply_eq_zero_of_mem_span`: if `w` is in the span and `B α z = 0` for every `α ∈ Φ`, then
  `B w z = 0`.
- `eq_zero_of_mem_span` (`hpos`): a vector of the span on which every root vanishes is zero.
- `rootWeight_mem_span`: `ρ(y)` lies in the span.
- `rootWeight_congr`: if `0 < B α y ↔ 0 < B α z` for every `α ∈ Φ`, then `ρ(y) = ρ(z)`.
- `rootWeight_smul`: `ρ(t • y) = ρ(y)` for `t > 0`.
- `rootWeight_apply`: `B (ρ y) z = ∑_{α ∈ Φ, 0 < B α y} m α * B α z`.
- `mem_closedFace_self`, `smul_mem_closedFace` (`t > 0`): `y` and `t • y` lie in the closed
  face of `y`.
- `closedFace_subset`: if `z` is in the closed face of `y`, the closed face of `z` is contained
  in that of `y`.
- `exists_pos_of_ne_zero` (`hpos`, `hneg`): a nonzero `y` of the span has some `α ∈ Φ` with
  `0 < B α y`.
- `nonneg_of_nonneg_on_fixed` (`hpos`, `hneg`, `hm`, `hlevi`): let `ψ : E →ₗ[ℝ] ℝ`, `y` in the
  span, and assume `0 ≤ ψ r` for every `r` in the closed face of `y` with `ρ(r) = r`. Then
  `0 ≤ ψ y`. It is stated for each `n` with the number of roots not vanishing at `y` equal to
  `n`.
- `exists_pos_le_subsetSum_pairing`: there is `ε > 0` with
  `ε ≤ B (∑_{α ∈ T} α) (∑_{α ∈ U} m α • α)` whenever `T, U ⊆ Φ` and the pairing is positive.
- `exists_pos_rootCone_bound` (`hpos`, `hneg`, `hm`, `hlevi`, `S ⊆ Φ`): there is `ε > 0` such
  that for every `c ≥ 0` and every `H : E →ₗ[ℝ] ℝ` with `-c ≤ H r` for all `r` satisfying
  `B α r ≤ 0` (`α ∈ S`) and `ρ(r) = r`, every `ν` in the span with `0 ≤ B α ν` for `α ∈ S`
  satisfies `H ν ≤ c / ε * ∑_{α ∈ Φ} |B α ν|`.
- `exists_pos_rootCone_decay` (same hypotheses): there are `ε > 0` and `L ≥ 0` such that for all
  `s ≥ 0` and `c ≥ 0`, all `H` as above, every `ν` in the span with `s * L ≤ B α ν` for
  `α ∈ S`, and every `β ∈ Φ`:
  `H ν + s * |H β| ≤ c / ε * (∑_{α ∈ Φ} |B α ν| + s * L)`.
  Here `L = ∑_{α, β ∈ Φ} |B α β|`.

The constraint is required only at fixed points `r = ρ(r)` of the weight. A family of bounds
`-c ≤ H (ρ y)` for all admissible `y` implies it, because `H r = H (ρ r)`.

## Proofs as implemented

**Span lemmas.** `apply_eq_zero_of_mem_span` is span induction in the first argument. If every
root vanishes at `z` and `z` is in the span, then `B z z = 0`, so `z = 0` by `hpos`. A nonzero
vector of the span therefore has a root with `B α y ≠ 0`. If that value is negative, `-α`
(`hneg`) is positive at `y`.

**Weights and faces.** `ρ(y)` is a sum of multiples of elements of `Φ`. It depends only on the
filter `{α | 0 < B α y}`, which is unchanged by positive scaling. The face lemmas compare signs
case by case. For the inclusion of faces, `0 ≤ B α z` splits into `B α z = 0` and `0 < B α z`.

**Fixed points generate faces** (`nonneg_of_nonneg_on_fixed`). The proof is strong induction on
the number `n` of roots not vanishing at `y`. If `y = 0` there is nothing to prove. Otherwise the
set `N` of nonvanishing roots is nonempty. For `α ∈ N` put `q α = B α ρ(y) / B α y`. By
`hlevi`, `B α ρ(y) = 0` for the roots outside `N`. Choose `a₁, a₂ ∈ N` minimizing and
maximizing `q`.

- If `q a₁ = q a₂ = l`, then `B α (ρ(y) - l • y) = 0` for every `α ∈ Φ`. Since
  `ρ(y) - l • y` is in the span, `ρ(y) = l • y`. Moreover
  `B (ρ y) y = ∑_{0 < B α y} m α B α y > 0`, so `l * B y y > 0` and `l > 0`. Hence
  `r = ρ(y)` is a fixed point (`rootWeight_smul`) in the closed face of `y`, and
  `ψ y = l⁻¹ ψ r ≥ 0`.
- If `q a₁ < q a₂`, put `d₁ = ρ(y) - q a₁ • y` and `d₂ = q a₂ • y - ρ(y)`. Then
  `B α d₁ = (q α - q a₁) B α y` and `B α d₂ = (q a₂ - q α) B α y` on `N`, and both vanish
  off `N`. So `d₁` and `d₂` lie in the span and in the closed face of `y`. Moreover `d₁`
  vanishes at `a₁` and `d₂` at `a₂`, so both have fewer nonvanishing roots. Their closed faces
  lie in that of `y` (`closedFace_subset`), so the induction hypothesis gives `ψ dᵢ ≥ 0`.
  Finally `y = (q a₂ - q a₁)⁻¹ • (d₁ + d₂)`.

**Uniform constant.** The pairings `B (∑_{T} α) (∑_{U} m α • α)` over pairs of subsets of `Φ`
form a finite set. `ε` is the least positive one, or `1` if there is none.

**Conic bound.** Put `y = -ν` and `e = ∑_{α ∈ Φ, 0 < B α y} α`, and apply
`nonneg_of_nonneg_on_fixed` to `ψ = H + (c / ε) • B e`. Let `r ≠ 0` be a fixed point in the
closed face of `y`. It is admissible, since `B α y = -B α ν ≤ 0` on `S` and faces preserve
weak signs. So `H r ≥ -c`. Every summand of `B e r` is nonnegative. A root positive at `r`
exists (`r = ρ(r)` is in the span) and must be positive at `y`, so `B e r > 0`. Because
`r = ρ(r)` and `e` are subset sums of the type above, `B e r ≥ ε`, and so `ψ r ≥ 0`. Hence
`ψ(-ν) ≥ 0`, which reads `H ν ≤ -(c/ε) B e ν`, and
`-B e ν = ∑ -B α ν ≤ ∑_{α ∈ Φ} |B α ν|`.

**Decay form.** Let `β ∈ Φ` and let `γ` be `β` or `-β` with `H γ = |H β|`. Since
`|B α γ| ≤ L` and `B α ν ≥ s L` on `S`, the vector `ν + s • γ` is admissible for the conic
bound. That bound, together with `|B α (ν + s γ)| ≤ |B α ν| + s |B α β|` and
`∑_α |B α β| ≤ L`, gives the inequality.

## Scope

This module is linear algebra only. It does not construct the lines, prove Levi orthogonality
for an actual induced character form, or relate `∑_{β} |H β|` to the height of a group element.
It does not prove `ParabolicCharacterDecayInput` or the host theorem.
