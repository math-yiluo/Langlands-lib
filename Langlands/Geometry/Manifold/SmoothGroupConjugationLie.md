# Tangent conjugation is a Lie algebra automorphism

Let `G` be a real Lie group of class `C^∞` modelled on `I`, with model space
`E`. For `g ∈ G`, the published `groupTangentConjugation I g` is the derivative
at the identity of conjugation `c_g : h ↦ g h g⁻¹`, a continuous linear
endomorphism of the identity tangent space `GroupLieAlgebra I G`. This module
proves that it is an automorphism of Lie algebras. The bracket is Mathlib's: the
bracket of the left-invariant vector fields, evaluated at the identity.

## Results

- `contMDiff_conjugation` and its corollaries: conjugation, inverse conjugation
  and left multiplication are smooth and differentiable at every point.
- `mfderiv_conjugation_mul_left_apply`: for `x ∈ G` and a tangent vector `v` at
  the identity, `d(c_g)_x (dL_x v) = dL_(c_g x) (Ad(g) v)`. It follows from the
  chain rule and the identity `c_g ∘ L_x = L_(c_g x) ∘ c_g`.
- `mfderiv_inv_conjugation_comp` and `mfderiv_conjugation_comp_inv`: at every
  point, the derivatives of `c_(g⁻¹)` and `c_g` are mutually inverse, by the
  chain rule. `inverse_mfderiv_conjugation` expresses this with Mathlib's
  `ContinuousLinearMap.inverse`.
- `mpullback_conjugation_mulInvariantVectorField`: the pullback along `c_g` of
  the invariant vector field of `Ad(g) v` is the invariant vector field of `v`.
- `groupTangentConjugation_lie`: `Ad(g) ⁅v, w⁆ = ⁅Ad(g) v, Ad(g) w⁆`. This
  needs a complete model space. The proof applies Mathlib's naturality of the
  Lie bracket under pullback (`mpullback_mlieBracket`) to `c_g` at the identity,
  rewrites both pulled-back fields with the previous item, and applies `Ad(g)`.
- `groupTangentConjugation_one` and `groupTangentConjugation_mul`:
  `Ad(1) = id` and `Ad(g k) = Ad(g) ∘ Ad(k)`, from `c_1 = id`,
  `c_(gk) = c_g ∘ c_k` and the chain rule. Hence
  `Ad(g⁻¹) (Ad(g) v) = v` and `Ad(g) (Ad(g⁻¹) v) = v`.
- `groupTangentConjugationLieEquiv`: `Ad(g)` as a real Lie algebra equivalence
  with inverse `Ad(g⁻¹)`. This needs the instance
  `LieGroup I (minSmoothness ℝ 3) G` that Mathlib's Lie algebra structure uses.

## Provenance

The content is internal. It is the standard fact that the differential of a
Lie group automorphism is a Lie algebra automorphism. The proof uses Mathlib's
`GroupLieAlgebra`, invariant vector fields and pullback naturality of the Lie
bracket, together with the published `groupTangentConjugation`.

## Scope

No exponential map is used and no statement about one-parameter subgroups is
made. The module asserts nothing about the adjoint group beyond these
composition laws.
