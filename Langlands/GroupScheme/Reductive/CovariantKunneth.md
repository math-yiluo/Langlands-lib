# Tensors that are covariant in each factor

Worker 1628 derives this internal result from flatness of modules over a field.
It is a Künneth-type criterion. A tensor in `A ⊗ A` that is left covariant in
each tensor factor separately multiplies into the product of the two
left-covariant coordinate subspaces. It is the step that turns a two-variable
function, covariant in each variable, into a sum of products of covariant
coordinates. The exhaustion results in `Reductive/CellExhaustion.lean` use it.
No group scheme, Borel subgroup or cell is involved here.

## Kernels of tensor maps

Let `k` be a field and `M`, `M'`, `N`, `N'` vector spaces over `k`, with linear
maps `φ : M → N` and `φ' : M' → N'`.

`mem_range_map_ker_subtype` takes a tensor `F ∈ M ⊗ M'` with
`(φ ⊗ id) F = 0` and `(id ⊗ φ') F = 0`. It concludes that `F` lies in the image
of `ker φ ⊗ ker φ' → M ⊗ M'`, the tensor product of the two subspace
inclusions.

Proof. Every module over a field is flat. By Mathlib's
`Module.Flat.lTensor_exact`, the sequence `M ⊗ ker φ' → M ⊗ M' → M ⊗ N'` is
exact, so `F` is the image of some `G ∈ M ⊗ ker φ'`. Next, `(φ ⊗ id) G` maps
to `(φ ⊗ id) F = 0` under the injective map `N ⊗ ker φ' → N ⊗ M'`
(`Module.Flat.lTensor_preserves_injective_linearMap`), so `(φ ⊗ id) G = 0`.
Exactness of `ker φ ⊗ ker φ' → M ⊗ ker φ' → N ⊗ ker φ'`
(`Module.Flat.rTensor_exact`) then writes `G` as the image of some
`G' ∈ ker φ ⊗ ker φ'`, and `G'` maps to `F`.

## Covariant tensors

Now let `A` be a commutative bialgebra over `k`, and let `C` and `D` be vector
spaces over `k`. For a linear map `r : A → C` and `χ ∈ C`, the existing
`leftCovariantSubspace r χ` consists of the `a` with `(r ⊗ id)(Δ a) = χ ⊗ a`.

- `leftCovariantSubspace_eq_ker` records that this subspace is, by definition,
  the kernel of `(r ⊗ id) ∘ Δ - (a ↦ χ ⊗ a)`.
- `mul'_mem_mul_leftCovariantSubspace` takes linear maps `r : A → C` and
  `s : A → D`, weights `χ ∈ C` and `ψ ∈ D`, and a tensor `F ∈ A ⊗ A` that
  satisfies two hypotheses. Covariance in the first factor says that applying
  `(r ⊗ id) ∘ Δ` to the first factor of `F` agrees with `a ↦ χ ⊗ a` applied to
  the first factor of `F`. Covariance in the second factor says the same for
  `(s ⊗ id) ∘ Δ` and `a ↦ ψ ⊗ a` on the second factor. The conclusion is that
  the multiplication of `F`, `LinearMap.mul' k A F`, lies in the product
  submodule `leftCovariantSubspace r χ * leftCovariantSubspace s ψ`.

  Pointwise, `F` is a function `F(x, y)` with `F(i(p) x, y) = χ(p) F(x, y)` and
  `F(x, i'(q) y) = ψ(q) F(x, y)`. Its restriction to the diagonal,
  `x ↦ F(x, x)`, is then a sum of products `v(x) w(x)`, with `v` covariant of
  weight `χ` and `w` covariant of weight `ψ`.

  Proof. Apply `mem_range_map_ker_subtype` to the two maps
  `(r ⊗ id) ∘ Δ - (a ↦ χ ⊗ a)` and `(s ⊗ id) ∘ Δ - (a ↦ ψ ⊗ a)`. The two
  hypotheses say that both kill `F`. Hence `F` comes from
  `leftCovariantSubspace r χ ⊗ leftCovariantSubspace s ψ`. Multiplication of
  that tensor product into `A` is Worker 1330's `coordinateProduct`, whose
  image is the product submodule (`range_coordinateProduct`).

## Scope

The results are purely algebraic and hold for an abstract commutative
bialgebra and arbitrary linear maps `r` and `s`. They do not show that any
particular tensor is covariant in each factor. The covariance results for
cell lifts in `Reductive/CellExhaustion.lean` do that for the tensors built
there.
