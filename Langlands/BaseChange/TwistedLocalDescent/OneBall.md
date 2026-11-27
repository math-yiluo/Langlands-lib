# Change of variables on one ultrametric ball

Module `Langlands.BaseChange.TwistedLocalDescent.OneBall`. Let `X` be an ultrametric normed
additive group, proper, with Borel σ-algebra and an additive Haar measure `ν`.

- `map_restrict_closedBall_of_perturbation`: let `A` be a homeomorphism of `X` with `A 0 = 0` and
  `ν.map A = c • ν`, and `χ : X → X` with `χ 0 = 0` such that `u(x) = A⁻¹(χ x) − x` is continuous
  and Lipschitz with constant `k < 1` on the closed ball `B(0, r)`. Then
  `(ν|_{B(0,r)}).map χ = c • ν|_{A(B(0,r))}`.
  Proof: `χ = A ∘ (id + u)`; the Library's `HarmonicAnalysis.map_closedBall_add_perturbation`
  shows that `id + u` maps `ν|_{B(0,r)}` to `ν|_{B(0,r)}` (as `u(0) = 0`), and `A` is a measurable
  embedding scaling `ν` by `c`.
- `image_closedBall_add_perturbation'`: for complete `X`, `id + u` maps `B(0, r)` onto `B(0, r)`
  when `u(0) = 0` and `u` has Lipschitz constant `< 1` on the ball (the ultrametric inequality for
  "into"; the contraction `x ↦ b − u(x)` of the ball has a fixed point for "onto").
- `image_closedBall_of_perturbation`: under the hypotheses of the first item (with `X` complete),
  `χ(B(0, r)) = A(B(0, r))`.
- `map_restrict_closedBall_of_perturbation'` and `image_closedBall_of_perturbation''`: the same
  statements when the topology of `X` is given as a separate instance equal to the norm topology
  (used for matrices, whose topology instance is the product topology).
