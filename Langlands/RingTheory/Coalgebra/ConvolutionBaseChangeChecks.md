# Checks for scalar extension of finite convolution duals

This module contains elaboration checks and proved examples for the
declarations of `Langlands.RingTheory.Coalgebra.ConvolutionBaseChange`, whose
main definition is `Langlands.CoalgebraDescent.convolutionDualBaseChangeEquiv`.
It is internal verification infrastructure for that construction. The examples
add no assumptions to its public interface and make no new mathematical claim
beyond the checked facts described below. All declarations are in
`Langlands.CoalgebraDescent.ConvolutionBaseChangeChecks`.

## Complete interfaces and universes

The eleven private `*Interface` abbreviations write out the complete types of
all eleven public declarations of the construction module:
the linear equivalence `convolutionDualBaseChangeLinearEquiv` and its
pure-tensor evaluation lemma, the algebra equivalence
`convolutionDualBaseChangeEquiv`, the two identifications of its forward and
inverse underlying linear equivalences, the two pointwise forms of these
identifications, the pure-tensor evaluation lemma
`E (a ⊗ f) (b ⊗ d) = a * b * algebraMap k K (f d)`, the two inverse laws, and
the inverse expansion in an arbitrary finite basis.

Each interface binds the field `k : Type u`, the module `D : Type v`, and the
field `K : Type w` with their instances in declaration order. The two linear
interfaces have no `Coalgebra k D` input; all algebra-level interfaces have
it. `FiniteDimensional k D` is the only finiteness input. No cocommutativity,
nontriviality, positive-dimension, separability, perfection, characteristic, or
extension-degree input appears in any of them.

Each interface is checked against the complete unapplied declaration at the
universe variables `u, v, w`, and at the closed unequal tuples `(0, 1, 2)` and
`(2, 1, 0)`, in the order `k`, `D`, `K`. The finite-basis inverse expansion
also quantifies a basis index type `ι : Type x` with `Fintype ι`; it is
checked at `u, v, w, x`, `(0, 1, 2, 3)` and `(3, 2, 1, 0)`. These assignments
check the whole argument telescope and the independence of the universes.
The complete-type universe maxima are intentional, hence
`set_option linter.checkUnivs false` in this module.

`equivInterface` is a public definition whose type is the complete
unapplied type of the main equivalence,

```lean
(k : Type u) → [Field k] → (D : Type v) → [AddCommGroup D] → [Module k D] →
[Coalgebra k D] → (K : Type w) → [Field K] → [Algebra k K] →
[FiniteDimensional k D] →
K ⊗[k] WithConv (D →ₗ[k] k) ≃ₐ[K] WithConv ((K ⊗[k] D) →ₗ[K] K)
```

and whose value is `@convolutionDualBaseChangeEquiv.{u,v,w}`. It is an alias
used only as the entry declaration of this check module, and it is checked
against the corresponding private interface.

## Actual Mathlib structures

For an arbitrary `k`-coalgebra `D` and field extension `K`, reflexivity
checks identify the inferred instances with Mathlib's named instances:

- the coalgebra on `K ⊗[k] D` is `TensorProduct.instCoalgebra`;
- the `K`-algebra on `K ⊗[k] WithConv (D →ₗ[k] k)` is
  `Algebra.TensorProduct.leftAlgebra`;
- on `WithConv (D →ₗ[k] k)`, the `k`-algebra, multiplication and unit are
  `LinearMap.convAlgebra`, `LinearMap.convMul` and `LinearMap.convOne`;
- on `WithConv ((K ⊗[k] D) →ₗ[K] K)`, the `K`-algebra, semiring,
  multiplication and unit are `LinearMap.convAlgebra`,
  `LinearMap.convSemiring`, `LinearMap.convMul` and `LinearMap.convOne`.

The examples then record the formulas these instances give on the target:
`(F * G) c` is `LinearMap.mul' K K` applied to
`TensorProduct.map F G (Coalgebra.comul c)`, and `1 c` is
`algebraMap K K (Coalgebra.counit c)`. They also record Mathlib's
scalar-extended comultiplication and counit on `b ⊗ d`
(`TensorProduct.comul_tmul` and `TensorProduct.counit_tmul`).
Finally, the main equivalence is applied to products, to `1`, and to `K`-scalar
multiples through `map_mul`, `map_one` and `map_smul`. These examples use the
general interface, with the actual instances above.

## Coherence of forward and inverse formulas

For any finite basis of `D`, with index type in an independent universe `x`,
three proved examples relate the forward pure-tensor formula and the inverse
basis expansion:

- the inverse of the forward image of `a ⊗ f` is
  `∑ i, (a * algebraMap k K (f (basis i))) ⊗ toConv (basis.coord i)`;
- consequently `a ⊗ f` itself equals that dual-basis expansion;
- the forward image of the expansion
  `∑ i, F (1 ⊗ basis i) ⊗ toConv (basis.coord i)`, evaluated at `b ⊗ d`, is
  `F (b ⊗ d)`.

The first two computations use the expansion lemma, the pure-tensor
evaluation lemma and `mul_one`; the second also rewrites `a ⊗ f` by the
inverse law `symm (E x) = x`. The third rewrites the expansion back to
`symm F` and applies the inverse law `E (symm F) (b ⊗ d) = F (b ⊗ d)`.

## Zero coalgebras

If `D` is subsingleton, instance inference gives `Unique` instances on both
the source `K ⊗[k] WithConv (D →ₗ[k] k)` and the target
`WithConv ((K ⊗[k] D) →ₗ[K] K)`, through Mathlib's subsingleton tensor-product
and linear-map instances. With a coalgebra structure, the target unit equals
zero. Thus the equivalence is between zero algebras in this case; no
nontriviality is needed or assumed.

Two concrete zero coalgebras instantiate the main equivalence:

- `Fin 0 → k`, whose inferred coalgebra is reflexively Mathlib's
  `Pi.instCoalgebra`, is finite-dimensional and subsingleton. Using
  `Pi.basisFun k (Fin 0)` in the expansion lemma, the inverse of every
  target element is `0`, an empty sum.
- `PUnit.{v + 1}`, in the universe of `D`, carries the private explicit zero
  coalgebra `punitZeroCoalgebra` with zero comultiplication and counit; its
  axioms hold by subsingleton elimination. It is finite-dimensional, and the
  main equivalence elaborates for it.

## A nonzero coalgebra

For `D = k`, the inferred coalgebra is reflexively
`CommSemiring.toCoalgebra k`. Its convolution unit is the counit, the
identity functional. The forward image of `1 ⊗ 1` therefore evaluates to `1`
at `1 ⊗ 1`. The same evaluation proves that `1` in
`K ⊗[k] WithConv (k →ₗ[k] k)` is nonzero: otherwise `1 = 0` in the field `K`.
For the singleton basis `Module.Basis.singleton (Fin 1) k`, the inverse of
`F` is `F (1 ⊗ 1) ⊗ coord 0`.

## Provenance and limits

These are internal derived checks of an internal construction; no external
literature is cited. They rely on the definitions and lemmas of the
construction module and on the cited Mathlib instances and lemmas from
`Mathlib.RingTheory.Coalgebra.Convolution`,
`Mathlib.RingTheory.Coalgebra.TensorProduct` and
`Mathlib.RingTheory.Coalgebra.Basic`.
They establish no descent statement and no claim about the group-like elements
or simple subcoalgebras of `D`.
