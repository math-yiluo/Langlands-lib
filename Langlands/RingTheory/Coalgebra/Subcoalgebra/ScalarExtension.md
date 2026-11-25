# Images of coalgebra maps and scalar extension of subcoalgebras

The file works with the subcoalgebras of [Basic](Basic.md): a subcoalgebra is a subspace `D` with `Δ(D) ⊆ D ⊗ D`, and over a field it carries the coalgebra structure constructed there. This is the convention of Milne, *Algebraic Groups* (2017), printed pp. 236–238, especially the definition of a finite-dimensional subcoalgebra in the proof of Theorem 12.18 on p. 237 (PDF pages 252–254). The registered source is `milne-2017-algebraic-groups`, content SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. The official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02` has no correction to this passage. Images, scalar extension and their lemmas are derived here; the source does not state them.

All universes are arbitrary and independent. `k : Type u` is a field, and `C : Type v`, `E : Type w` are `k`-coalgebras with `[AddCommGroup _]`. No cocommutativity or finite dimensionality is assumed.

## The image of a homomorphism

For `f : C →ₗc[k] E`, `range f` is the subcoalgebra of `E` with underlying submodule `LinearMap.range f.toLinearMap` (`range_toSubmodule`); `e ∈ range f` means `e = f c` for some `c` (`mem_range`).

Closure under comultiplication: by Mathlib's `TensorProduct.range_mapIncl` and `TensorProduct.range_map`, the image of `range f ⊗ range f` in `E ⊗ E` and the range of `f ⊗ f` are the same submodule, namely the span of the tensors `f c ⊗ f c'`. Since `f` is a homomorphism, `Δ (f c) = (f ⊗ f)(Δ c)` lies in it.

## Restricting the codomain

For a subcoalgebra `D` of `E` and `f : C →ₗc[k] E` with `f c ∈ D` for all `c`, `codRestrict D f h : C →ₗc[k] D` is the linear map `c ↦ ⟨f c, h c⟩`, shown to be a homomorphism:

- the counit of `D` is the counit of `E` restricted, so compatibility with counits is that of `f`;
- for comultiplication, both sides are compared after `tensorSquareInclusion D`, which is injective. The inclusion of `D` composed with the restricted map is `f` (`LinearMap.subtype_comp_codRestrict`), so by `TensorProduct.map_map` the left side becomes `(f ⊗ f)(Δ c) = Δ (f c)`, and the right side is `Δ (f c)` by `map_comul_subtype`.

`codRestrict_apply` and `subtype_comp_codRestrict` say that it is `f` after inclusion into `E`.

`rangeRestrict f : C →ₗc[k] range f` is the case `D = range f`. It is surjective (`rangeRestrict_surjective`), and injective when `f` is (`rangeRestrict_injective`). For injective `f`, `equivRange f hf : C ≃ₗc[k] range f` is the resulting equivalence, from Mathlib's `CoalgEquiv.ofBijective`.

## Scalar extension

Let `K : Type x` be a field with `[Algebra k K]`; nothing is assumed about the extension `K/k`. For `D : Subcoalgebra k C`:

- `baseChangeMap K D : K ⊗[k] D →ₗc[K] K ⊗[k] C` is Mathlib's `Coalgebra.TensorProduct.map` of the identity of `K` and `D.subtype`. Its linear map is `D.toSubmodule.subtype.baseChange K` (`baseChangeMap_toLinearMap`), it sends `a ⊗ d` to `a ⊗ d` (`baseChangeMap_tmul`), and it is injective because `K` is flat over `k` (`baseChangeMap_injective`).
- `baseChange K D` is `range (baseChangeMap K D)`, a subcoalgebra of Mathlib's tensor product coalgebra `K ⊗[k] C`. Its underlying submodule is `D.toSubmodule.baseChange K` (`baseChange_toSubmodule`). `mem_baseChange` and `tmul_mem_baseChange` describe its elements; the second is Mathlib's `Submodule.tmul_mem_baseChange_of_mem`.
- `toBaseChange K D : K ⊗[k] D →ₗc[K] baseChange K D` is `rangeRestrict (baseChangeMap K D)`; it is bijective (`toBaseChange_bijective`), and followed by the inclusion it is `baseChangeMap K D` (`toBaseChange_apply`, `toBaseChange_tmul`, `subtype_comp_toBaseChange`).
- `baseChangeEquiv K D : K ⊗[k] D ≃ₗc[K] baseChange K D` is `equivRange` of `baseChangeMap K D`. Its homomorphism is `toBaseChange K D` (`baseChangeEquiv_toCoalgHom`), with the corresponding formulas `baseChangeEquiv_apply`, `baseChangeEquiv_tmul`.
- `baseChange_bot`, `baseChange_top` and `baseChange_mono` reduce to the statements for submodules (`Submodule.baseChange_bot`, `Submodule.baseChange_top`, `Submodule.baseChange_mono`), since a subcoalgebra is determined by its underlying submodule.
- If `D` is finite dimensional over `k`, then `baseChange K D` is finite dimensional over `K` (`instFiniteDimensionalBaseChange`): `K ⊗[k] D` is finite over `K` by Mathlib's `Module.Finite.base_change`, and `baseChangeEquiv K D` is a linear equivalence. `C` itself need not be finite dimensional, and `D = ⊥` is included.

The file does not show that finite-dimensional subcoalgebras cover `C` (see [LocalFiniteness](LocalFiniteness.md)), and proves no descent or duality statement.
