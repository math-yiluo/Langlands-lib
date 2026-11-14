# Euler characteristics of twists on fibres are polynomials

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistEuler` (namespace
`Langlands.AlgebraicGeometry.Modules.FibreTwist`) proves the content of clause 3 of
`ProjectiveFibreTwistCohomologyStatement`.

- `supportedIn_top`: the sections presheaf of a module is supported in the whole space (an affine
  open disjoint from the space is empty, and sections over the empty open are trivial).
- `eulerPolynomial_of_point`: let `B` be a field (`IsField B`) and `b : Spec B ⟶ T` a point. The
  alternating sum `∑ᶠ p, (-1)ᵖ dim_B Hᵖ` of the base change of `F(n)` along `b` is `P(n)` for one
  rational polynomial `P` of degree at most `N`. The proof:
  1. Base change the presentation of `𝓛X` along `Spec B ⟶ Spec A`, as in clause 1. The base change
     `X_b` is a closed subscheme of `ℙᴺ_B`, so `dim X_b ≤ N` (FLT
     `ProjSpace.topologicalKrullDim_le_of_isClosedImmersion`).
  2. The FLT theorem `OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2`
     gives `P` of degree at most `N` with FLT Čech Euler characteristic of
     `ofModules(F_b ⊗ L^{⊗ n})` equal to `P(n)`.
  3. `CechBridge.eulerChar_ofModules_eq` (module `CechEulerBridge`) identifies that Euler
     characteristic with the alternating sum of actual cohomology dimensions. `pullbackTwistIso` and
     `twistTensorPowIso` identify the module with the restriction of `F(n)`.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
