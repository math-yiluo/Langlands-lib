# Scalar extension of finite convolution duals

This module constructs the canonical algebra equivalence between scalar extension
of a finite convolution dual and the convolution dual of the scalar-extended
coalgebra. It is an internal derived construction from Mathlib's tensor-product
universal property, its finite free dual base-change equivalence, and its actual
convolution formulas. No external literature assertion is introduced.

## Inputs and structures

All public declarations are in `Langlands.CoalgebraDescent`. The main definition
is `convolutionDualBaseChangeEquiv k D K`, with independent universe parameters
`u`, `v`, `w` and the following inputs, in declaration order:

```lean
(k : Type u) [Field k]
(D : Type v) [AddCommGroup D] [Module k D] [Coalgebra k D]
(K : Type w) [Field K] [Algebra k K]
[FiniteDimensional k D]
```

Its result is

```lean
K ⊗[k] WithConv (D →ₗ[k] k) ≃ₐ[K]
  WithConv ((K ⊗[k] D) →ₗ[K] K)
```

The coalgebra structure on `K ⊗[k] D` is Mathlib's
`TensorProduct.instCoalgebra`, using the usual coalgebra on the base ring `K`.
Both duals use Mathlib's `WithConv` instances from
`Mathlib.RingTheory.Coalgebra.Convolution`: multiplication is convolution, and
the unit is the counit followed by the scalar algebra map. The source is the
usual algebra tensor product, with its left `K`-algebra structure.
No local replacement coalgebra, multiplication, unit, or algebra instance is
defined in this module.

The coalgebra need not be cocommutative; its convolution dual can therefore be
noncommutative. There are no assumptions on characteristic, perfection,
separability, the degree of the extension, or positive dimension of `D`.

## Linear construction and canonical forward formula

`convolutionDualBaseChangeLinearEquiv` first removes the source `WithConv`
synonym by the base change of `WithConv.linearEquiv k (D →ₗ[k] k)`. It then
applies `(TensorProduct.isBaseChange k D K).toDualBaseChange` and restores the
target synonym with the inverse of `WithConv.linearEquiv K`.

The middle equivalence is Mathlib's `IsBaseChange.toDualBaseChange` from
`Mathlib.LinearAlgebra.Dual.BaseChange`. The finite-dimensional vector space
`D` is free and finite over `k`, as required there. Mathlib constructs the
forward linear map using the scalar-extension universal property: a linear
functional `f` extends to the unique `K`-linear functional whose value on
`1 ⊗ d` is `algebraMap k K (f d)`. Tensoring this assignment with `K` gives
the forward map. Mathlib proves it bijective by expressing this map through
a finite basis and the corresponding scalar-extended basis.

The wrapper construction and its evaluation lemma do not require a coalgebra
structure on `D`. The coalgebra is used when upgrading to an algebra
equivalence.

Both `convolutionDualBaseChangeLinearEquiv_tmul_apply` and
`convolutionDualBaseChangeEquiv_tmul_apply` give the precise formula

```lean
E (a ⊗ₜ[k] f) (b ⊗ₜ[k] d) = a * b * algebraMap k K (f d)
```

where `E` is the respective equivalence. The proof first uses Mathlib's
`IsBaseChange.toDualBaseChange_tmul` at `1 ⊗ d`, then uses `K`-linearity to
evaluate at `b ⊗ d`. The displayed order of factors agrees with the Lean
statement. Since `K` is commutative, rearranging these scalar factors during
the proof does not impose commutativity on the convolution algebra.

This formula also explains canonicity: pure tensors generate the source and
target as modules, so their prescribed evaluations determine the forward
linear map. The construction exposes no choice of basis.

## Preservation of convolution and unit

The private lemma `convMul_tmul` expands convolution using Mathlib's finite
representation `ℛ k d` of the original comultiplication. Writing this
representation as

\[
\Delta_D(d)=\sum_i d'_i\otimes d''_i,
\]

the lemma proves, for the actual scalar-extended convolution,

\[
(F*G)(b\otimes d)=
  \sum_i F(1\otimes d'_i)\,G(b\otimes d''_i).
\]

Its proof rewrites `LinearMap.convMul_apply`, `TensorProduct.comul_tmul`,
`CommSemiring.comul_apply`, and the representation equality, and distributes
over the finite sum. This is a direct computation in the existing coalgebra
and convolution structures.

`convolutionDualBaseChangeEquiv` applies
`Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct` to the linear
equivalence. It suffices to verify multiplicativity on source pure tensors
and preservation of `1 ⊗ 1`. For multiplicativity, equality of the target
`K`-linear maps reduces to evaluation on `1 ⊗ d`. The private expansion and
the forward evaluation formula turn both sides into the same finite sum,
using the original convolution expansion `(ℛ k d).convMul_apply` and
multiplicativity of `algebraMap k K`.

For the unit, evaluation on `1 ⊗ d` reduces by
`LinearMap.convOne_apply` to the scalar-extension formula for the counit.
Thus the algebra upgrade preserves exactly the original convolution unit.

## Backward formula and coherence

The following equations hold by definitional equality:

- `convolutionDualBaseChangeEquiv_toLinearEquiv` identifies the underlying
  linear equivalence with `convolutionDualBaseChangeLinearEquiv`.
- `convolutionDualBaseChangeEquiv_symm_toLinearEquiv` identifies the inverse
  underlying linear equivalence with the inverse linear construction.
- `convolutionDualBaseChangeEquiv_apply` and
  `convolutionDualBaseChangeEquiv_symm_apply` give these identifications
  pointwise.

`convolutionDualBaseChangeEquiv_apply_symm_apply` states that applying the
forward map after its inverse, then evaluating at any `b ⊗ d`, recovers the
original functional's value. Conversely,
`convolutionDualBaseChangeEquiv_symm_apply_apply` recovers every tensor in
the source. These follow from the inverse laws of the same algebra
equivalence.

There is also an explicit inverse formula. For any finite indexing type `ι`
in an additional independent universe and any `basis : Module.Basis ι k D`,
`convolutionDualBaseChangeEquiv_symm_apply_eq_sum` proves

```lean
E.symm F =
  ∑ i, F (1 ⊗ₜ[k] basis i) ⊗ₜ[k] toConv (basis.coord i)
```

Here `basis.coord i` is the original `k`-linear coordinate functional.
The proof applies injectivity of `E`, evaluates on `1 ⊗ d`, and uses the
forward formula and `basis.sum_repr d`. Scalar movement through `F` uses
`LinearMap.map_smul_of_tower`, so the original `k`-coordinates become their
images in `K`. This proves the formula for every finite basis; it does not
make the equivalence depend on that basis.

## Zero coalgebra and checks

When the underlying module `D` is zero, its finite basis is empty. The inverse
formula is then the empty sum. Both dual modules and their tensor products
are zero modules, with convolution units equal to zero. An algebra equivalence
between these subsingleton algebras is valid, and none of the construction or
its proofs assumes `Nontrivial D` or a positive dimension.

The core module compiles without errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Declaration inspection of the main
definition reports exactly the independent universe parameters `u`, `v`, `w`;
inspection of the finite-basis inverse formula additionally reports its index
universe. Their transitive axiom checks report only `propext`,
`Classical.choice`, and `Quot.sound`. Compilation and these development
checks are separate from independent semantic review and publication.
