# Actual two-place enveloping tensor retractions

Work in `Langlands.Global.ArchimedeanGL`. Let `F : Type u` be any field,
let `n : ℕ`, and use its actual real and complex infinite places. No
`NumberField F` or positivity hypothesis on `n` is needed for these
algebraic constructions. All tensor products of enveloping algebras in
this file are algebraic tensor products over `ℂ`; no topological completion
is taken.

The imported global algebra `EnvelopingAlgebra F n` is the universal
enveloping algebra over `ℂ` of the complexification of the actual global
real archimedean matrix Lie algebra. The imported local algebras are

- `RealPlaceEnvelopingAlgebra n = U_ℂ(ℂ ⊗[ℝ] M_n(ℝ))`;
- `ComplexPlaceEnvelopingAlgebra n = U_ℂ(ℂ ⊗[ℝ] M_n(ℂ))`.

At a complex place the scalar extension uses the full underlying real
Lie algebra of `M_n(ℂ)`, retaining both real directions. All coordinates,
inclusions and projections below are the actual ones constructed in
`ArchimedeanPlaceLie` and `ArchimedeanPlaceEnveloping`.

The four `realPlaceComplexLieProjection_otherInclusion`,
`complexPlaceComplexLieProjection_otherInclusion`,
`realPlaceComplexLieProjection_complexInclusion` and
`complexPlaceComplexLieProjection_realInclusion` identities prove that a
complexified coordinate projection annihilates a different coordinate
inclusion. The first two require the two places of the same type to be
distinct; the mixed identities need no inequality. Tensor induction
reduces these claims to the imported real coordinate identities, with
additivity handling sums.

The three new unital complex algebra homomorphisms have domain
`EnvelopingAlgebra F n` and these targets:

| Definition | Places | Target |
| --- | --- | --- |
| `realPlacesEnvelopingTensorProjection` | real `v, w` | `RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n` |
| `complexPlacesEnvelopingTensorProjection` | complex `v, w` | `ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n` |
| `realComplexPlacesEnvelopingTensorProjection` | real `v`, complex `w` | `RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n` |

Each definition applies `Langlands.Algebra.EnvelopingTensor.lift` to the
two actual coordinate Lie projections followed by their local enveloping
generators. Write `p_v` and `p_w` for these complexified Lie projections
and `ι_v`, `ι_w` for the respective local enveloping generators. The three
`_generator` identities give the exact formula

`P(ι_global(X)) = ι_v(p_v(X)) ⊗ 1 + 1 ⊗ ι_w(p_w(X))`

for every `X : ComplexLieAlgebra F n`. The same-type definitions and
these generator formulas are available even when `v = w`.

For distinct places of the same type, or any real/complex pair, each
projection prefix has these further identities and consequences:

- `_comp_left` and `_comp_right` identify composition with the actual local
  enveloping inclusions with `Algebra.TensorProduct.includeLeft` and
  `includeRight`, respectively.
- `_leftInclusion` and `_rightInclusion` evaluate those identities on every
  local enveloping element: `P(I_v(a)) = a ⊗ 1` and
  `P(I_w(b)) = 1 ⊗ b`.
- `_comp_map` identifies composition with the corresponding imported
  `realPlacesEnvelopingTensorMap`, `complexPlacesEnvelopingTensorMap` or
  `realComplexPlacesEnvelopingTensorMap` with the identity algebra map.
  `_map` evaluates it on every tensor element `t`, proving `P(T(t)) = t`.
- Each tensor map's `_injective` theorem and each projection's
  `_surjective` theorem follow from this constructed left inverse.

The six composition-with-inclusion proofs use the universal enveloping
homomorphism extensionality principle. On a Lie generator, the imported
same-coordinate retraction gives the original local direction and the
proved cross-coordinate law gives zero in the other factor. This yields
the claimed tensor-factor inclusion. Tensor algebra homomorphism
extensionality then reduces `P ∘ T = id` to pure tensors. Since the actual
tensor map sends `a ⊗ b` to `I_v(a) I_w(b)`, multiplicativity of `P` and
the factor formulas give `(a ⊗ 1)(1 ⊗ b) = a ⊗ b`. Injectivity follows by
applying `P` to an equality; surjectivity uses `T(t)` as the preimage of
`t`. No PBW theorem is required.

This is an internal construction from the imported actual archimedean
coordinate and commuting tensor maps, the generic tensor-factor Lie
lift, and pinned Mathlib's universal enveloping and algebra tensor
product universal properties (`Algebra/Lie/UniversalEnveloping.lean`
and `RingTheory/TensorProduct/Basic.lean`). Its intrinsic split identities
are proved here. It supplies actual two-place operator algebra
infrastructure for the global automorphic branch. It makes no global
tensor decomposition, representation tensor decomposition, admissibility,
automorphic existence, local-factor or local-global compatibility claim.
