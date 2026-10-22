# Monodromy kernels and inertia invariants

Worker 17 authored this construction module for task
`503968de-16f8-4f63-ba13-b5e167e11dce`. It imports `Langlands.WeilDeligne.Basic` and
`Langlands.Weil.Representation.Invariants` for the actual pair and
invariant-representation constructions.

For a pair `(r,N)` with norm character `nu`,
`kernelSubrepresentation` is the actual subspace `ker N`, equipped with
its restricted Weil action. Its stability proof evaluates
`r(g) N r(g⁻¹) = nu(g) N` at `r(g)v`, cancels the inverse group action,
and uses that `nu(g)` is a unit. Thus `Nv=0` implies `N(r(g)v)=0`.
`kernelRepresentation` bundles this action as a finite-dimensional
representation; `kernelInclusion` is its actual inclusion intertwiner.

`kernelMap` restricts a morphism of pairs to the two monodromy kernels.
Its defining square with monodromy proves that the restriction lands in
the target kernel, and the original equivariance proves that it is an
intertwiner. The identity and composition obligations are proved as
linear-map equalities in `kernelFunctor`. `kernelEquiv` maps actual pair
isomorphisms to representation equivalences; this supplies the
well-definedness proof for `kernelClass`.

For an explicitly normal subgroup `I`, `inertiaKernelRepresentation`
then takes its invariants in this kernel. This is the actual nested
subspace consisting of vectors annihilated by `N` and fixed by every
element of `I`. `inertiaKernelFunctor` composes the two functors, and
`inertiaKernelClass` gives the corresponding construction on genuine
isomorphism classes. A chosen geometric Frobenius acts through the
representation on this space; no Frobenius choice or Euler polynomial
is built into the definition.

All constructions work over an arbitrary field. They require neither
a topology nor finite inertia image. Nilpotence is part of the input
pair, although kernel stability uses only covariance and the nonzero
norm character. The carrier universe is independent of the field and
group universes; `kernelMap` also permits different carrier universes.

The mathematical source is Tate, *Number theoretic background*, Corvallis
Part II, printed page 20, §§4.1.5–4.1.6:
the Weil-stable kernel and the space denoted `V_N^I`.
Source ID `tate-1979-number-theoretic-background`; retained Part II PDF
SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
Functorial maps and quotient descent are intrinsic implementation
obligations proved here, not assumed comparison theorems.

## Included restriction module

`Langlands.WeilDeligne.Restriction` is the accompanying independent pair
in this contribution. Its homomorphism restriction retains the actual
carrier and monodromy, pulls back the norm, and proves map, functor,
equivalence and genuine quotient obligations. Its paired Markdown gives
the complete formula and source correspondence. Both modules use the
same pair-isomorphism interface from `Langlands.WeilDeligne.Basic`.
