# Unitized regular module and scalar-projection kernel

Let `R : Type uR` be a commutative ring and `A : Type uA` a nonunital ring.
The universes `uR` and `uA` are independent. Assume an `R`-module structure
on `A`, with `IsScalarTower R A A` and `SMulCommClass R A A`, so
multiplication on `A` is compatible with scalars on both sides. Put
`U = Unitization R A`. Supply an actual ordinary `U`-module structure on `A`
and the elementwise action formula

```
u • a = u.fst • a + u.snd * a.
```

The target is the actual ideal `RingHom.ker (Unitization.fstHom R A)`,
with its inherited left `U`-module structure. In namespace
`Langlands.Algebra.UnitizationRegularKernel`, `regularKernelEquiv` constructs
the `U`-linear equivalence from `A` to this kernel by `a ↦ (0,a)`. Its inverse
takes the second coordinate. The zero first coordinate of a kernel element
proves the right inverse law. Mathlib's coordinate addition and multiplication,
together with the supplied action formula, prove linearity.

The four intrinsic coordinate laws `regularKernelEquiv_apply_coe`,
`regularKernelEquiv_apply_fst`, `regularKernelEquiv_apply_snd` and
`regularKernelEquiv_symm_apply` state respectively that the underlying image
is `Unitization.inr a`, its coordinates are `0` and `a`, and the inverse is
the second coordinate. They follow by reduction of the construction.

This is derived implementation algebra motivated by Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, I.2.1, printed14/PDF20, and C.II, printed279/PDF285.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The book's unitization motivates the coordinates; this precise Mathlib
kernel equivalence is an internal construction rather than a separately
numbered source definition. Worker 709 authored this implementation.

The input action is supplied explicitly; this module constructs no new
unitization action. It assumes no commutativity, identity, nonzero
multiplication, finite generation or Noetherianity of `A`. Zero multiplication
is allowed. Comparisons of finite generation and Noetherianity, including
the source's compatible nonunital-module conventions, require separate
statements and proofs. The construction does not settle those conventions
or the final C.II localization proposition.
