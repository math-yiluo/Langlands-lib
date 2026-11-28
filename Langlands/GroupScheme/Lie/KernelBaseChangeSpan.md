# Bases and images of Lie algebras after a change of the coefficient algebra

Module `Langlands.GroupScheme.Lie.KernelBaseChangeSpan`, namespace `Langlands.GroupScheme.Lie`.

Let `G` and `H` be group schemes over `Spec k` for a field `k`, with affine structure morphisms, and
let `A` be a commutative `k`-algebra in the universe of `k`. The Lie algebra over `A` is the
dual-number identity kernel `lieKernel G A`; `lieKernelMapLinear G (Algebra.ofId k A)` is the change
of coefficients from `k` to `A`, and `targetMapLinear f A` is the map of Lie algebras over `A`
induced by a morphism `f : H ⟶ G`.

## Contents

- `kernelBaseChangeBasis G A e` (for `G` locally of finite type): the `A`-basis of
  `lieKernel G A` obtained from a `k`-basis `e` of `lieKernel G k` through the Library's
  isomorphism `kernelScalarExtension G A : A ⊗[k] lieKernel G k ≃ lieKernel G A`;
  `kernelBaseChangeBasis_apply` identifies its vectors with the changed vectors
  `lieKernelMapLinear G (Algebra.ofId k A) (e i)`.
- `lieKernelMapLinear_mem_span_image`: change of coefficients maps the `k`-span of a set into the
  `A`-span of its image.
- `mem_span_range_lieKernelMapLinear` (for `G` locally of finite type): every vector of
  `lieKernel G A` is an `A`-combination of changed vectors.
- `lieKernelMapLinear_mem_range_targetMapLinear` (no finiteness hypothesis): change of
  coefficients maps the image of `targetMapLinear f k` into the image of `targetMapLinear f A`.
- `range_targetMapLinear_le_span` (for `H` locally of finite type): if the image of
  `targetMapLinear f k` lies in a `k`-submodule `S`, the image of `targetMapLinear f A` lies in the
  `A`-span of the changed vectors of `S`.
- `range_targetMapLinear_le_span_of_le_span` (for `H` locally of finite type): the same with `S`
  the `k`-span of a set `T`, and the conclusion with the changed vectors of `T`.

## Proof

All statements follow from the compatibility of change of coefficients with the induced maps
(`lieKernelMapLinear_targetMapLinear`) and from `mem_span_range_lieKernelMapLinear`. For `G` locally
of finite type, `lieKernel G k` is finite-dimensional and the Library's isomorphism
`kernelScalarExtension G A` turns the changed vectors of `Module.finBasis k (lieKernel G k)` into
an `A`-basis of `lieKernel G A`. The two image statements expand vectors of `lieKernel H A` in the
same way, which is why they assume `H` locally of finite type. They are proved by induction on
span membership. Without a finiteness hypothesis the spanning statements fail: for an infinite
product of additive groups over `k` and `A = k[t]`, the sequence `(tⁿ)ₙ` in `lieKernel G A = A^ℕ`
is not an `A`-combination of finitely many vectors of `k^ℕ`.
