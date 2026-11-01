# Actual Euler values of affine pullback tensor powers

`AffinePullbackTensorPowerEulerStatement` concerns an arbitrary affine
morphism `f : X → Y`, a structure morphism `s : Y → Spec K` over an arbitrary
field, an actual line bundle `L` on `Y`, and any natural exponent `n`,
including zero. It compares the actual module sheaves

```text
A = (f* L)^n on X,
B = L^n tensor f_* O_X on Y.
```

It asserts equivalence of finite cohomology for `A` over `f ≫ s` and for
`B` over `s`. When those conditions hold, their integer Euler
characteristics agree for any choices of finiteness witnesses. These
are the published actual derived relative cohomology and its finite
alternating dimension sum.

This is an internal derivation from the line-bundle projection formula,
the actual pullback/tensor-power comparison, and the published
`affinePushforwardEulerCharacteristic`. The tensor power `L^n` is again
a line bundle. The projection formula applied to it and `O_X`, followed
by the tensor right unitor and pullback/tensor-power comparison,
identifies `B` with `f_* A`. The local rank-one property implies
quasi-coherence of `A`, as required by the affine cohomology theorem.

No smoothness, properness, finiteness, flatness, ampleness, or numerical
rank hypothesis is required. The statement supplies the cohomological
projection step for a finite-flat Euler comparison. It asserts neither
polynomiality nor a leading-coefficient or polarized-rank equation.
