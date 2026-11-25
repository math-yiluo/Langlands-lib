# Subcoalgebras, and the coalgebra structure of a subcoalgebra over a field

## The notion

Let `R : Type u` be a commutative semiring and `C : Type v` an `R`-coalgebra in Mathlib's sense (`Coalgebra R C`); the two universes are independent. A term of `Langlands.Subcoalgebra R C` consists of a submodule `carrier` of `C` and the property `comul_mem'`: for every `c ∈ carrier`, the element `Coalgebra.comul c` lies in the range of `TensorProduct.map carrier.subtype carrier.subtype : carrier ⊗[R] carrier → C ⊗[R] C`.

This is the condition `Δ(D) ⊆ D ⊗ D` used by Milne, *Algebraic Groups* (2017), proof of Theorem 12.18, printed pp. 237–238 (registered source `milne-2017-algebraic-groups`), where Milne works over a field and restricts the counit. The official errata snapshot of 2026-11-02 makes no correction to this passage. Over a general base ring the map `D ⊗ D → C ⊗ C` need not be injective, so the condition is stated with the range of that map. No comultiplication on `D`, no coalgebra structure and no splitting is part of the data. The bundled type, the subcoalgebras `⊥` and `⊤` and the structural lemmas below are not in the source.

## Over a commutative semiring

- `Subcoalgebra R C` is a `SetLike` type: the set of a subcoalgebra is the set of its carrier. Two subcoalgebras with the same set have the same carrier, and the remaining field is a proposition, so they are equal. This gives `ext` (equality from equal membership) and the order: `D ≤ E` means that every element of `D` lies in `E` (`le_def`).
- Sums, zero and scalar multiples of elements of `D` lie in `D` (`AddSubmonoidClass`, `SMulMemClass`), because they do for the carrier.
- `toSubmodule D` is the carrier. The lemmas `mem_carrier`, `mem_toSubmodule`, `toSubmodule_carrier` and `toSubmodule_le_toSubmodule` hold by definition.
- `comul_mem` is the closure property for `c ∈ D`. `ofSubmodule` makes a subcoalgebra from a submodule with the closure property (`ofSubmodule_carrier`, `mem_ofSubmodule`).
- `⊤` has carrier `⊤`. Its closure property is `comul_mem_tensorSquare_top`: by Mathlib's `TensorProduct.range_mapIncl` the range of `p ⊗ q → C ⊗ C` is the submodule spanned by the tensors `x ⊗ y` with `x ∈ p`, `y ∈ q`, and for `p = q = ⊤` this is everything (`TensorProduct.map₂_mk_top_top_eq_top`). The lemma uses the comultiplication only, so it is stated for `CoalgebraStruct`.
- `⊥` has carrier `⊥`: its only element is `0`, and `Δ 0 = 0`.
- `top_toSubmodule`, `bot_toSubmodule`, `mem_top` and `mem_bot` describe the two. They are the largest and the smallest subcoalgebra (`OrderTop`, `OrderBot`), because their carriers are the largest and the smallest submodule.

## Coalgebra axioms along an injective map

`coalgebraOfInjective` is stated for a field `k` and vector spaces `A`, `B` in independent universes. `A` carries a comultiplication `Δ_A` and a counit `ε_A` (`CoalgebraStruct k A`), `B` is a coalgebra with `Δ_B` and `ε_B`, and `f : A →ₗ[k] B` is an injective linear map with `ε_B (f x) = ε_A x` and `(f ⊗ f)(Δ_A x) = Δ_B (f x)` for all `x`. The conclusion is that `A`, with its given structure maps, is a coalgebra.

Each axiom is an equality of two linear maps from `A` to a tensor power of `A`. The proof evaluates at `x` and applies the corresponding tensor power of `f`, which is injective because all vector spaces are flat.

- Left counit law, `(ε_A ⊗ id)(Δ_A x) = 1 ⊗ x` in `k ⊗ A`. Apply `k ⊗ f` (`Module.Flat.lTensor_preserves_injective_linearMap`). Since `(k ⊗ f) ∘ (ε_A ⊗ id) = ε_A ⊗ f = (ε_B ∘ f) ⊗ f = (ε_B ⊗ id) ∘ (f ⊗ f)` (`LinearMap.lTensor_comp_rTensor`, `LinearMap.rTensor_map`), the left side becomes `(ε_B ⊗ id)((f ⊗ f)(Δ_A x)) = (ε_B ⊗ id)(Δ_B (f x)) = 1 ⊗ f x` by the counit law of `B`, and this is the image of `1 ⊗ x`.
- Right counit law: the same with `f ⊗ k` and the factors exchanged.
- Coassociativity, an equality in `A ⊗ (A ⊗ A)`. Apply `f ⊗ (f ⊗ f)`, injective by two uses of `TensorProduct.map_injective_of_flat_flat`. `TensorProduct.map_map_assoc` moves it through the associator; `LinearMap.map_rTensor` and `LinearMap.map_lTensor` merge it with `Δ_A ⊗ id` and `id ⊗ Δ_A` into `((f ⊗ f) ∘ Δ_A) ⊗ f` and `f ⊗ ((f ⊗ f) ∘ Δ_A)`. Replacing `(f ⊗ f) ∘ Δ_A` by `Δ_B ∘ f` and splitting off `f ⊗ f` again (`LinearMap.rTensor_map`, `LinearMap.lTensor_map`) turns the two sides into the two sides of coassociativity of `B` at the element `(f ⊗ f)(Δ_A x) = Δ_B (f x)`.

## Over a field

Let `k : Type u'` be a field and `C : Type v'` a `k`-coalgebra with `[AddCommGroup C]`. No cocommutativity, finite dimensionality or universe condition is assumed, and the zero subcoalgebra is included.

- The elements of `D : Subcoalgebra k C` form the subtype of its carrier, with the additive group and `k`-module structures of that submodule; negatives of elements of `D` lie in `D` (`AddSubgroupClass`).
- `tensorSquareInclusion D` is `TensorProduct.map D.carrier.subtype D.carrier.subtype`. It is injective (`tensorSquareInclusion_injective`) by `TensorProduct.map_injective_of_flat_flat`. `tensorSquareEquivRange D` is the resulting linear equivalence of `D ⊗[k] D` with the range of this map.
- `carrierComul D` restricts `Δ` to `D`, regards it as a map into that range, which is possible by `comul_mem`, and applies the inverse of `tensorSquareEquivRange D`. So `carrierComul D x` is the unique element of `D ⊗[k] D` with image `Δ x`.
- `instCoalgebraStruct` gives `D` the comultiplication `carrierComul D` and the counit of `C` restricted to `D`.
- `map_comul_subtype`: the image of `Δ x`, computed in `D`, under `tensorSquareInclusion D` is `Δ x`, computed in `C`. This is `LinearEquiv.apply_symm_apply` for `tensorSquareEquivRange D`, read in `C ⊗[k] C`. `map_comul_subtype_comp` is the same statement for linear maps, and `counit_subtype` holds by definition.
- `instCoalgebra D` is `coalgebraOfInjective` for the inclusion `D → C`, whose two hypotheses are `counit_subtype` and `map_comul_subtype`. The coalgebra structure of `D` is therefore determined by the closure property alone.
- `subtype D : D →ₗc[k] C` is the inclusion as a homomorphism of coalgebras. Its linear map is the inclusion of the submodule (`subtype_toLinearMap`), it sends `x` to `x` (`subtype_apply`), and it is injective (`subtype_injective`).

That every element of a coalgebra over a field lies in a finite-dimensional subcoalgebra is proved in [LocalFiniteness](LocalFiniteness.md). Images of homomorphisms and scalar extension are in [ScalarExtension](ScalarExtension.md).
