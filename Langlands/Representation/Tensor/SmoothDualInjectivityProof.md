# Injectivity of the canonical finite smooth-dual tensor map: proof

Worker 261 wrote the Lean proof and this account of it.

## Result

`Langlands.FiniteTensor.smoothDualTensorInjectivity` proves the entire
published proposition
`Langlands.FiniteTensor.SmoothDualTensorInjectivityStatement` from
[SmoothDualInjectivityStatement](SmoothDualInjectivityStatement.md). Its type
is `SmoothDualTensorInjectivityStatement.{uI, uG, uV}`, so the three universe
levels of the index type, the groups and the carriers stay independent.

So for every finite index type `ι` (the empty type included), every family of
topological groups `G i` and every family of complex representations `ρ i` on
complex vector spaces `V i`, the published map `smoothDualTensorMap ρ` from
`⨂[ℂ] i, SmoothDual (ρ i)` to the smooth dual of the external tensor product
is injective.

The proof adds no hypothesis to the statement. It uses no admissibility,
smoothness of `ρ`, compact-open cofinality, finite-dimensionality of the
carriers, nonzero carriers, irreducibility, or any property of the group
topologies. Empty `ι` and zero carriers need no separate case: the argument
below is uniform in `ι` and the carriers. The statement pair and every
imported pair are unchanged. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Imports and reused results

The module imports the statement module,
`Mathlib.LinearAlgebra.Dual.Lemmas` and
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`. It uses these results by name:

- `smoothDualTensorMap_val` (published, `Langlands.Representation.Tensor.SmoothDual`):
  the underlying functional of `smoothDualTensorMap ρ x` is
  `PiTensorProduct.dualDistrib (PiTensorProduct.map (fun i => smoothDualPairing (ρ i)) x)`.
- `smoothDualPairing ρ` is the subtype inclusion of
  `SmoothDual ρ = smoothVectors ρ.dual` into the full algebraic dual, so it is
  injective by `Submodule.injective_subtype`.
- Mathlib's `PiTensorProduct.span_tprod_eq_top`, `PiTensorProduct.map_tprod`,
  `PiTensorProduct.map_comp`, `PiTensorProduct.map_id`,
  `PiTensorProduct.dualDistrib_apply` and `PiTensorProduct.ext`.
- Mathlib's `PiTensorProduct.dualDistribEquiv`, the linear equivalence
  `(⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i)` for a finite index and
  finite free modules. Here it is used only on finite-dimensional subspaces,
  never on the ambient spaces, where it does not exist in general.
- Mathlib's `Module.evalEquiv`, `LinearMap.dualMap_injective_iff`,
  `LinearMap.exists_rightInverse_of_surjective` and
  `Module.forall_dual_apply_eq_zero_iff`, all over a field.

## Implemented proof

The module proves four generic lemmas over an arbitrary field `K` and a
finite index type, followed by the closing theorem. No new definition is
introduced.

1. `exists_finiteDimensional_tensor_preimage` (no finiteness of the index is
   needed). Every tensor `x : ⨂[K] i, N i` is the image of some
   `y : ⨂[K] i, D i` under `PiTensorProduct.map (fun i => (D i).subtype)`,
   for finite-dimensional subspaces `D i ≤ N i`. Since pure tensors span,
   `x` is a finite linear combination `∑ c f • tprod f`. Let `D i` be the span
   of the finitely many coordinates `f i` with `f` in the support of `c`.
   Then `y` is the same combination of pure tensors of these coordinates, now
   viewed in the `D i`, and `map_tprod` gives the equality termwise.

2. `dualDistrib_comp_map_injective_of_finiteDimensional`. Let the `D i` be
   finite-dimensional and let `g i : D i →ₗ[K] Dual K (M i)` be injective.
   Then `PiTensorProduct.dualDistrib ∘ₗ PiTensorProduct.map g` is injective.
   A `Fintype` structure is chosen from `Finite ι`.

   - **Evaluation is surjective.** The flipped map
     `(g i).flip : M i →ₗ[K] Dual K (D i)` sends `m` to `d ↦ g i d m`. It is
     surjective because its dual map is injective. Two elements of
     `Dual K (Dual K (D i))` are evaluations at some `d` and `d'` by
     `Module.evalEquiv`. If they agree after composing with `(g i).flip`, then
     `g i d` and `g i d'` agree at every `m`, so `d = d'` by injectivity.
   - **Right inverses.** Each `(g i).flip` has a linear right inverse
     `s i : Dual K (D i) →ₗ[K] M i`.
   - **Key identity.** For `φ : ⨂[K] i, Dual K (D i)` and `y : ⨂[K] i, D i`,
     `dualDistrib φ y` equals
     `dualDistrib (map g y) (map s φ)`. Stated as an equality of linear maps,
     it is checked on pure tensors in both arguments by `PiTensorProduct.ext`.
     There both sides are products over `i`, by `dualDistrib_apply` and
     `map_tprod`, and the factors agree because
     `g i (d i) (s i (φ i)) = φ i (d i)` by the right-inverse property.
   - **Conclusion.** Suppose `dualDistrib (map g y) = 0`. Every functional
     on `⨂[K] i, D i` is `dualDistrib φ` for some `φ`, by surjectivity of
     `dualDistribEquiv` on the finite-dimensional `D i`. By the key identity,
     each such functional vanishes at `y`. Hence `y = 0` by
     `Module.forall_dual_apply_eq_zero_iff`.

3. `dualDistrib_comp_map_injective`. The same conclusion for injective
   `g i : N i →ₗ[K] Dual K (M i)` with no finiteness assumption on the `N i`
   or the `M i`. Let `x` lie in the kernel. Step 1 writes `x` as the image of
   some `y : ⨂[K] i, D i` with finite-dimensional `D i ≤ N i`. The composites
   `g i ∘ₗ (D i).subtype` are injective, and by `PiTensorProduct.map_comp` the
   composite map sends `y` to the image of `x`, which is zero. Step 2 gives
   `y = 0`, so `x = 0`.

4. `dualDistrib_injective`. The special case `g i = id` of step 3, using
   `PiTensorProduct.map_id`: over a field, `PiTensorProduct.dualDistrib` is
   injective for arbitrary factor spaces. The closing theorem does not use
   this corollary.

5. `smoothDualTensorInjectivity` introduces the binders of the statement.
   If `smoothDualTensorMap ρ x = smoothDualTensorMap ρ y`, then their
   underlying functionals agree. By `smoothDualTensorMap_val` these are the
   images of `x` and `y` under
   `dualDistrib ∘ₗ map (fun i => smoothDualPairing (ρ i))`. Step 3 with the
   injective inclusions `smoothDualPairing (ρ i)` over `K = ℂ` gives `x = y`.

The task's suggested route first proves injectivity of
`PiTensorProduct.map` for injective factor maps by left inverses, and
injectivity of `dualDistrib` separately. The implemented proof instead applies
the finite-dimensional reduction of step 1 directly to the composite of
`dualDistrib` with `map g`. Neither separate lemma about `PiTensorProduct.map`
is needed.

## Provenance

The target is an internal derived proposition, as its statement Markdown
explains, rather than a verbatim theorem from external literature. The proof
is standard finite tensor linear algebra over a field. It follows the second
step of the route sketched in the task: reduction to finite-dimensional
subspaces, surjective evaluation maps, and finite tensor duality on the
finite-dimensional pieces.
