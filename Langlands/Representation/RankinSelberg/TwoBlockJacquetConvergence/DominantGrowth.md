# Growth of a unipotent-invariant functional on the dominant cone

Module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.DominantGrowth`,
namespace `Langlands.RankinSelberg.TwoBlockConvergence`.

Author: Worker 886.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockJacquetConvergenceStatement` (JPSS 1983,
Section (4.6)). It proves the elementary "finite growth exponent" estimate on
the dominant cone that the module `FunctionalGrowth` turns into a uniform
bound for the block functionals.

## Provenance

The content is internal to this proof. JPSS (source ID
`jpss-1983-rankin-selberg`) obtain bounds for Whittaker functions on the
dominant torus from asymptotic expansions (Section 2.5, printed pages
388–389). This module does not use Whittaker models or asymptotic expansions.
It uses a standard Hecke-operator argument that needs only smoothness, a
finite-dimensional space of vectors fixed by one principal level `P = K(a)`,
and invariance of the functional under `P ∩ N`. All averages are the
published `Hecke.fixedProjection` (normalized integration over a compact open
subgroup) from `Langlands.Representation.Hecke.ActionProjection`.

## Averaging (section `Average`)

`fixedProjection_dual_eq_of_const`: let `L` be a linear functional that takes
the constant value `c` on the orbit `{ρ(g) v : g ∈ K}` of a compact open
subgroup `K`. Then `L` takes the value `c` at the normalized average
`Π_K v`. Proof: `Hecke.integratedAction_dual` turns `L(Π_K v)` into the
integral of `g ↦ 1_K(g) vol(K)⁻¹ L(ρ(g) v)`. That integrand is the indicator
of `K` times the constant `vol(K)⁻¹ c`, so the integral equals `c`.

## Cone combinatorics (section `Cone`)

- `coneWeight lam = (lam 0 - lam n).toNat + |lam n|` for
  `lam : Fin (n + 1) → ℤ`.
- `coneGenerator s`: for `s = inl k` the step exponent with entries `1` at
  positions `≤ k` and `0` after it; for `s = inr true` and `s = inr false`
  the constant exponents `1` and `-1`.
- `antitone_coneGenerator`: each generator is antitone.
- `eq_zero_of_coneWeight_eq_zero`: an antitone exponent of weight zero is zero.
- `exists_coneGenerator_step`: a nonzero antitone `lam` is `lam' + coneGenerator s`
  with `lam'` antitone of weight `coneWeight lam - 1`. If `lam` is not constant,
  choose a descent `k` (`lam k > lam (k + 1)`) and subtract the step generator
  at `k`. If `lam` is constant, subtract the constant generator of the sign of
  `lam n`. The proof is a case analysis closed by `omega` and `linarith`.

## Torus growth (section `Torus`)

Here `k` is a valued topological field, `ϖ` a unit with `v(ϖ) ≤ 1`,
`P = principalLevelSubgroup k n a` with `a > 0`, and `ℓ` a linear functional
with `ℓ(ρ(x) v) = ℓ(v)` for every upper unipotent `x ∈ P`.

`dual_torus_fixedProjection_torus` (**projector identity**): for antitone
`lam₁, lam₂` and `w` fixed by `P`,

`ℓ(ρ(ϖ^lam₁) Π_P(ρ(ϖ^lam₂) w)) = ℓ(ρ(ϖ^(lam₁ + lam₂)) w)`.

Proof: by `fixedProjection_dual_eq_of_const` it suffices that
`g ↦ ℓ(ρ(ϖ^lam₁ g ϖ^lam₂) w)` is constant on `P`. By
`exists_unipotent_sandwich`, `ϖ^lam₁ g ϖ^lam₂ = x ϖ^(lam₁ + lam₂) y` with `x ∈ P`
upper unipotent and `y ∈ P`. Since `ρ(y) w = w` and `ℓ ∘ ρ(x) = ℓ`, the value is
`ℓ(ρ(ϖ^(lam₁+lam₂)) w)` (`torus_add`).

`exists_dominant_bound` (**growth on the dominant cone**): if the space `E` of
`P`-fixed vectors is finite-dimensional, there is `B ≥ 1` such that every
`w ∈ E` has a constant `C` with

`‖ℓ(ρ(ϖ^lam) w)‖ ≤ C B^(coneWeight lam)` for all antitone `lam`.

Proof as implemented: take a Haar measure on `GL_(n+1)(k)` normalized on `P`.
For each generator `s` let `T_s = Π_P ∘ ρ(ϖ^(coneGenerator s))`, an
endomorphism of `E`. Transport `E` to `Fin (dim E) → ℂ` by the
coordinate isomorphism `e` of `Module.finBasis`. Let `A_s` and `L` be the
continuous linear maps that correspond to `T_s` and `ℓ|_E`, and put
`B = 1 + ∑_s ‖A_s‖`. Induction on `N = coneWeight lam` gives
`‖ℓ(ρ(ϖ^lam) w)‖ ≤ ‖L‖ B^N ‖e w‖`. For `N = 0`, `lam = 0`. In the
inductive step write `lam = lam' + coneGenerator s`. The projector identity
gives `ℓ(ρ(ϖ^lam) w) = ℓ(ρ(ϖ^lam') T_s w)`, and `‖e(T_s w)‖ ≤ B ‖e w‖`.
Finally take `C = ‖L‖ ‖e w‖`.
