# Derivatives along paths and finite-order orbit derivatives on a Lie group

The module `Langlands.Geometry.Manifold.GroupPathDerivative` proves two facts about the orbit
derivative `groupDirectionalValue I X f g`, the derivative at the identity of `h ↦ f (g h)` in the
direction `X` of the Lie algebra, on a Lie group `G` modelled on a finite-dimensional space.

- `hasDerivAt_comp_path`: if `f : G → ℂ` is differentiable at `c t` and the path `c : ℝ → G` is
  differentiable at `t`, then `s ↦ f (c s)` has derivative at `t` equal to the orbit derivative of
  `f` at `c t` in the direction `leftPathVelocity c t`, the derivative at `t` of `s ↦ (c t)⁻¹ c s`, that is the
  velocity of `c` at `t` translated to the identity. This is the chain rule, written with the left-invariant trivialization of the tangent
  bundle.
- `contMDiff_groupDirectionalValue_of_le`: if `f` is of class `Cⁿ` (`n ≤ ∞`) and `m + 1 ≤ n`, the
  orbit derivative `g ↦ groupDirectionalValue I X f g` is of class `Cᵐ`. It is the composition of
  the differential of `f` with the smooth left translations, and the differential of a `Cⁿ` map is
  `Cⁿ⁻¹`.
