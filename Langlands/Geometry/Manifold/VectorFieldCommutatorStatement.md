# The scalar differential commutator for actual manifold vector fields

This is an internal calculus prerequisite for tangent differentiation on the
constructed infinite adelic group. Its provenance is Mathlib's actual manifold
derivative and vector-field bracket, together with the vector-space identity
`VectorField.fderiv_apply_lieBracket`. The proposition asks for the corresponding
manifold identity; this file does not prove it or assume it as an axiom.

Let `E` be a complete real normed vector space, let
`I : ModelWithCorners ℝ E H` be boundaryless, and let `M` carry the specified
charted-space structure and `IsManifold I ∞ M`. The model and manifold may have
independent universes. For actual tangent vector fields
`V W : (x : M) → TangentSpace I x`, assume that the sections
`x ↦ (V x : TangentBundle I M)` and `x ↦ (W x : TangentBundle I M)` are
`MDifferentiable I I.tangent`. For every real smooth function `f : M → ℂ`,
`smoothVectorFieldCommutator I M` asserts at every `x : M` that

```
df_x([V,W]_x)
  = d(y ↦ df_y(W_y))_x(V_x) - d(y ↦ df_y(V_y))_x(W_x).
```

All three displayed scalar derivatives are precisely `mvfderiv` with the
specified source model `I` and real scalar field. The bracket is precisely
`VectorField.mlieBracket I V W`, as constructed from chart pullbacks in Mathlib;
it is not a supplied operation or a separate action on functions. The sign is
the one in Mathlib's `VectorField.fderiv_apply_lieBracket`: differentiation first
along `W`, then along `V`, minus the reverse order.

The vector-field hypotheses require differentiability of the tangent-bundle
sections, not smoothness of every order. The function is smooth, so the second
derivatives needed for the commutator are genuine. The definition retains the
explicit complete-space and boundaryless hypotheses needed by the intended
adelic consumer. It asserts no version for manifolds with boundary.

For a smooth group, applying this statement to its actual left-invariant vector
fields and using `mulInvariantVector_mlieBracket` is the intended route to
`D_[X,Y] = D_X D_Y - D_Y D_X` for the positive right-orbit derivative.
That application, its eventual enveloping-algebra extension, exponential
curves, moderate growth, and cuspidal realizations are separate obligations.
