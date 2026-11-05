# An inverse power bound from a contraction-scaling argument

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ContractionScaling`,
namespace `Langlands.HarishChandraSchwartz`. It imports only Mathlib
(`Mathlib.Topology.Order.Compact`, `Mathlib.Analysis.SpecificLimits.Basic`).

## Purpose and provenance

Provenance: internal. This is an abstract topological lemma for the proof of the height
comparison II.2 (6) in J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra* (2003), printed p. 254 (PDF p. 20). The lemma is not
transcribed from Waldspurger. He derives II.2 (6) from the polynomial estimates (7), (8) and
from the closedness of unipotent orbits (Humphreys). The route planned here is different:
for `ū` in the opposite unipotent radical, conjugation by a contracting torus element `a`
shrinks the size `β(ū)` (for example, the largest entry of `ρ₀(ū) − 1` in a weight basis
of a faithful representation). It also shrinks `g(ū) = ‖τ(ū) e − e‖` for a weight vector
`e`, and the lemma compares the two. The application to actual groups is not part of this
module. No group structure and no field are used here.

## Declarations

Let `X` be a type, `c : X → X`, `β g : X → ℝ`, `q : ℝ` and `D : ℕ`.

- `contractionScalingAnnulus β q D` is the set `{x | 1 ≤ q ^ D * β x ∧ β x ≤ 1}`.
- `le_pow_mul_iterate_of_le_mul`: if `0 ≤ K` and `β x ≤ K β (c x)` for all `x`, then
  `β x ≤ K ^ n β (cⁿ x)` for all `n` and `x`. This is proved by induction on `n`, using
  `c^[n+1] x = c^[n] (c x)`.
- `pow_mul_iterate_le_of_mul_le`: if `0 ≤ q` and `q g (c x) ≤ g x` for all `x`, then
  `q ^ n g (cⁿ x) ≤ g x`. The proof is the same induction.
- `exists_iterate_le_one_of_le_mul`: if `0 ≤ θ < 1` and `β (c x) ≤ θ β x` for all `x`, then
  every `x` has some `n` with `β (cⁿ x) ≤ 1`. By induction `β (cⁿ x) ≤ θ ^ n β x`, and
  `θ ^ n β x → 0`.
- `exists_le_mul_pow_of_contractionScaling` (main result). The hypotheses are:
  - `1 ≤ q`;
  - `β x ≤ q ^ D β (c x)` for all `x`;
  - `q g (c x) ≤ g x` for all `x`;
  - every `x` has some `n` with `β (cⁿ x) ≤ 1`;
  - the annulus `S = contractionScalingAnnulus β q D` is compact (for some topology on `X`);
  - `g` is continuous on `S` and positive at every point of `S`.

  The conclusion is that some `C > 0` gives `β x ≤ C g(x) ^ D` for every `x` with
  `1 ≤ β x`.

## Proof of the main result as implemented

A positive lower bound `m` for `g` on `S` exists. If `S` is empty, take `m = 1`. Otherwise
`g` has a minimum on `S` (`IsCompact.exists_isMinOn`), and the minimum is positive. Take
`C = (m ^ D)⁻¹`.

Fix `x` with `1 ≤ β x`. Let `n` be the least index with `β (cⁿ x) ≤ 1` (`Nat.find`). The
point `y = cⁿ x` lies in `S`:

- If `n = 0`, then `y = x` and `1 ≤ β x ≤ q ^ D β x` because `q ^ D ≥ 1`.
- If `n = k + 1`, then `β (cᵏ x) > 1` by minimality, and
  `β (cᵏ x) ≤ q ^ D β (cᵏ⁺¹ x)`, so `1 < q ^ D β y`.

The first iteration lemma gives `β x ≤ (q ^ D) ^ n β y ≤ (q ^ n) ^ D`. The second gives
`q ^ n m ≤ q ^ n g(y) ≤ g(x)`. Raising this to the power `D` (both sides nonnegative) gives
`(q ^ n) ^ D ≤ (m ^ D)⁻¹ g(x) ^ D`.

## Scope

The lemma assumes the one-step inequalities exactly, with no multiplicative constants. In
an application, `β` and `g` must be computed in norms adapted to the weights of the
contracting element. Positivity of `g` on the annulus is an explicit hypothesis. For
`g(ū) = ‖τ(ū) e − e‖` it is equivalent to triviality of the stabilizer of `e` on the
annulus, and it is not proved here.
