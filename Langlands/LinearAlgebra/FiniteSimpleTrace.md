# Finite simple-module trace separation

Authors: Worker 34 (Lean proof and route), Worker 751 (checking and
documentation).

This helper module, namespace `Langlands.FiniteSimpleTrace`, proves two
theorems about a finite family of pairwise non-isomorphic simple modules. Each
module is finite-dimensional over the complex numbers.

## Setting

`A : Type uA` is a ring with a complex algebra structure. The index type
`ι : Type uI` is finite (`Fintype ι`). Each `M i : Type uM` is an additive
commutative group with a complex module structure and an `A`-module structure.
The two scalar actions are compatible (`IsScalarTower ℂ A (M i)`). Each `M i` is
finite-dimensional over `ℂ` and simple as an `A`-module. The hypothesis

```
hne : Pairwise (fun i k => ¬ Nonempty (M i ≃ₗ[A] M k))
```

says that distinct members are not isomorphic as `A`-modules. The index,
algebra and carrier universes `uI`, `uA` and `uM` are independent. Neither
theorem assumes that `A` is commutative or finite-dimensional.

## Declarations

- `exists_action_projection` (with `[DecidableEq ι]`): for every index `j`,
  there is `r : A` whose complex-linear action on `M i`, written
  `DistribSMul.toLinearMap ℂ (M i) r`, is the identity for `i = j` and zero
  for `i ≠ j`.
- `eq_zero_of_sum_trace_eq_zero`: let `c : ι → ℂ` satisfy
  `∑ i, c i * LinearMap.trace ℂ (M i) (DistribSMul.toLinearMap ℂ (M i) r) = 0`
  for every `r : A`. Then `c j = 0` for every `j`.

## Proof

Let `P` be the product `∀ i, M i`. Take an `A`-linear endomorphism `φ` of `P`.
For `i ≠ k`, the composite of the `k`-th inclusion, `φ` and the `i`-th
projection is an `A`-linear map `M k → M i` between simple modules. By
Schur's lemma `LinearMap.bijective_or_eq_zero` it is zero, since a bijective map would
contradict `hne`. Decompose a vector as `∑ k, Pi.single k (x k)`
(`Finset.univ_sum_single`). Then the `i`-th component of `φ x` depends only on
`x i`. So `x ↦ Pi.single j (x j)` commutes with every such `φ`. That is, it is
an endomorphism of `P` over `Module.End A P`.

`P` is a finite product of simple modules and hence semisimple. Mathlib's
`jacobson_density` (in `Mathlib.RingTheory.SimpleModule.Basic`) is applied to
this projection and to the finite set of all `Pi.single i (b i k)`, where
`b i = Module.finBasis ℂ (M i)`. It gives `r : A` acting as the projection on
these vectors. Comparing the `i`-th components shows that `r` acts on the basis
`b i` as the identity for `i = j` and as zero otherwise. Hence the two
complex-linear maps agree (`Module.Basis.ext`). This proves
`exists_action_projection`.

For `eq_zero_of_sum_trace_eq_zero`, evaluate the relation at that `r`. Every
term with `i ≠ j` is the trace of zero. The `j`-th term is
`c j * (Module.finrank ℂ (M j) : ℂ)`, since the trace of the identity is the
dimension. A simple module is
nontrivial (`IsSimpleModule.nontrivial`), so `Module.finrank_pos` makes the
dimension positive. Its complex image is nonzero, and so `c j = 0`.

## Provenance

This is a derived, internal formalization of the standard finite-dimensional
fact quoted in the proof of Bernstein and Zelevinsky (1976), Proposition 2.19,
printed/PDF page 21. They cite Bourbaki, *Algèbre*, Ch. VIII, §13,
Proposition 2, for linear independence of the traces of finitely many
pairwise inequivalent irreducible finite-dimensional representations. The Lean
proof follows the Jacobson-density route above. It does not reproduce Bourbaki's
text. It also does not infer finite-family independence from pairwise
separation alone. It extends to finite families the two-module density argument
of the published
`Langlands.CharacterSeparation.nonempty_linearEquiv_of_trace_eq`, but does not
import or use that theorem. The module imports only Mathlib.
