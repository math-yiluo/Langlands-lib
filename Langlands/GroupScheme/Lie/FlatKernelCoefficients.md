# Actual square-zero kernel coefficients on flat affine tests

Let `R` be a commutative ring, `G` a smooth affine group scheme over `Spec R`,
and `I` an ideal of `R` with `I² = 0`. For a flat `R`-algebra `B`,
`flatKernelCoefficientEquiv` gives an additive equivalence

`Additive ker(G(B) → G(B/IB)) ≃+ B ⊗[R] (I ⊗[R] Additive (lieKernel G R))`.

Here `IB` is the actual ideal `I.map (algebraMap R B)`. Its square is zero
by functoriality of ideal powers; no flatness is needed for this fact. The
comparison itself uses the published arbitrary-flat-algebra
`ElementaryKernelTensor.idealTensorEquiv`, identifying `B ⊗[R] I` with `IB`,
together with the previously constructed actual kernel tensor comparison and
tensor reassociation. The flatness assumption on `B` is retained throughout
this equivalence.

`flatKernelPoint` reconstructs the actual point from a module coefficient.
It takes sums to group products, is injective, and always reduces to the
identity. Its pure-tensor formula evaluates the base Lie vector in the ideal
element corresponding to `b ⊗ i`; that ideal element has value
`algebraMap R B i * b`.

`flatKernelPoint_naturality` proves that this actual reconstruction commutes
with every morphism between flat affine test algebras. Nested tensor induction
reduces the assertion to the pure-tensor formula and the naturality of actual
Lie tangent evaluation. The latter is proved earlier in the file without
affineness or smoothness assumptions: it follows from the commuting algebra
maps which evaluate dual numbers in compatible ideal elements.
`flatKernelCoefficientEquiv_naturality` gives the equivalent forward formula
for two actual kernel points whose images agree under the test-algebra map.

This internal construction deliberately uses flat test algebras. It does not
assert the displayed tensor description on arbitrary nonflat tests, extend
the target comparison to nonaffine `G`, descend these coefficients to the
quotient base, or prove a cohomological lifting result.
