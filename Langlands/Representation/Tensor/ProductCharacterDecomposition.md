# Coordinate restrictions and decomposition of product-subgroup characters

This module shows that a character of a finite product subgroup is the same thing as a tuple of characters of its factors. It complements `productCharacter` from [CharacterLocalization.lean](CharacterLocalization.lean). All public declarations are in `Langlands.FiniteTensor`.

The coefficient ring `R` is any commutative ring. The index type `ι` (universe `uI`), the groups `H i` (universe `uG`) and `R` (universe `uR`) have independent universe levels. Each `U i : Subgroup (H i)` is an actual subgroup, and the product subgroup is `Subgroup.pi Set.univ U`. Every lemma involving `productCharacter` assumes `Fintype ι`, as `productCharacter` does. The insertion maps and the restriction of characters need no finiteness. The module makes no nonempty-index, nontrivial-factor, decidable-equality, commutativity or topological-group assumptions.

## Coordinate insertion

`coordinateInclusion U i : U i →* Subgroup.pi Set.univ U` sends `u` to the tuple whose `i`th coordinate is `u` and whose other coordinates are `1`. The tuple is `Pi.mulSingle i u`, built with classical decidable equality on `ι`. It lies in the product subgroup by `Subgroup.mulSingle_mem_pi`, and the homomorphism laws are `Pi.mulSingle_one` and `Pi.mulSingle_mul`.

Evaluation lemmas:

- `coordinateInclusion_apply_self`: the `i`th coordinate of `coordinateInclusion U i u` is `u`.
- `coordinateInclusion_apply_of_ne`: for `j ≠ i`, the `j`th coordinate is `1`.
- `coordinateInclusion_coord_self` and `coordinateInclusion_coord_of_ne`: the same two facts, stated for the coordinate packaged with its membership proof as an element of `U i` or `U j`. This is the form in which `productCharacter_apply` evaluates the factors.
- `coe_coordinateInclusion`: for any `DecidableEq ι` instance, the underlying tuple equals `Pi.mulSingle i u`. The proof checks each coordinate using the two lemmas above, so the classical choice inside the definition is invisible to users.
- `coordinateInclusion_injective`: insertion is injective, because the `i`th coordinate recovers `u`.

## Coordinate characters and the two inverse laws

For `η : Subgroup.pi Set.univ U →* Rˣ`, the restriction `coordinateCharacter U η i : U i →* Rˣ` is defined as `η.comp (coordinateInclusion U i)`. The lemma `coordinateCharacter_apply` states `coordinateCharacter U η i u = η (coordinateInclusion U i u)` and holds by definition.

With `Fintype ι`:

- `productCharacter_coordinateInclusion`: `productCharacter U θ (coordinateInclusion U i u) = θ i u`. In the defining product over `ι`, the `i`th factor is `θ i u` and every other factor is `θ j 1 = 1` (`Finset.prod_eq_single`).
- `coordinateCharacter_productCharacter`: `coordinateCharacter U (productCharacter U θ) i = θ i`. This follows from the previous lemma by extensionality of monoid homomorphisms.
- `productCharacter_coordinateCharacter`: `productCharacter U (coordinateCharacter U η) = η` for every character `η` of the product subgroup. Fix `u` and, for each finite set `s ⊆ ι`, let `piece s` be the element of the product subgroup that agrees with `u` on `s` and is `1` off `s` (`Finset.piecewise`). Induction on `s` shows that `∏ j ∈ s, coordinateCharacter U η j u_j = η (piece s)`. For the empty set, `piece ∅ = 1`. For the insertion step with `j ∉ s`, `coordinateInclusion U j u_j * piece s = piece (insert j s)`, compared coordinatewise, and this combines with multiplicativity of `η`. Taking `s = Finset.univ` gives `piece univ = u`.
- `productCharacterEquiv U : (∀ i, U i →* Rˣ) ≃ (Subgroup.pi Set.univ U →* Rˣ)` bundles `productCharacter U` and `coordinateCharacter U` with these two inverse laws. Its evaluation lemmas are `productCharacterEquiv_apply` and `productCharacterEquiv_symm_apply`.

The `@[simp]` lemmas are `coordinateInclusion_apply_self`, `coordinateInclusion_coord_self`, `coordinateCharacter_apply`, `productCharacter_coordinateInclusion`, both inverse laws, and the two `productCharacterEquiv` evaluation lemmas.

For an empty index type, the product subgroup is trivial, every product character is the empty product `1`, and the same proofs apply without change. Trivial factors `U i = ⊥` need no special treatment either.

## Topology

Section `Topology` takes an arbitrary `TopologicalSpace (H i)` for each `i`. The product subgroup gets the subspace topology of the product topology on `∀ i, H i`, and `U i` gets the subspace topology of `H i`. These are the instances Mathlib infers.

- `continuous_coordinateInclusion`: each coordinate insertion is continuous. By `continuous_induced_rng` it suffices that `u ↦ Pi.mulSingle i (u : H i)` is continuous. This is `continuous_mulSingle i` composed with the continuous subtype inclusion.
- `isLocallyConstant_coordinateCharacter`: if `fun u => (η u : R)` is locally constant on the product subgroup, then each `fun u => (coordinateCharacter U η i u : R)` is locally constant on `U i`. It is `IsLocallyConstant.comp_continuous` applied to the continuous insertion.
- `isLocallyConstant_coordinateCharacter_units`: the same transfer for `η` and `coordinateCharacter U η i` viewed as functions into `Rˣ`.
- `continuous_coordinateCharacter`: for any `TopologicalSpace R`, continuity of `fun u => (η u : R)` implies continuity of `fun u => (coordinateCharacter U η i u : R)`.

`IsLocallyConstant` involves only the topology on the domain, so the locally-constant transfers need no topology on `R`. When `R` carries a topology, they hold for it as well. No discreteness, topological-group, local-compactness or finite-dimensionality hypothesis is used.

The intended specialization has `R = ℂ`, `H i = Langlands.GeneralLinear (n i) F` and `U i = Langlands.GeneralLinear.upperUnipotent (n i) F`, where `F` is a commutative ring with any topology. Given an arbitrary character `η` of `Subgroup.pi Set.univ U` into `ℂˣ` with `(η · : ℂ)` locally constant, the lemmas yield locally constant block restrictions, and `productCharacter_coordinateCharacter` recovers `η` from them. A test file that was compiled but not submitted checked this instantiation and the empty-index case.

## Derived provenance and scope

This is derived internal algebra and point-set topology, and it asserts no external literature theorem. It uses three inputs: the published `productCharacter` and `productCharacter_apply` from `Langlands.Representation.Tensor.CharacterLocalization`, imported by Lean name, Mathlib's `Pi.mulSingle` and `Finset.piecewise` API together with `Subgroup.mulSingle_mem_pi`, and Mathlib's continuity of `Pi.mulSingle` and the composition rule `IsLocallyConstant.comp_continuous` (`Mathlib.Topology.LocallyConstant.Basic`). The private single-coordinate helpers in `CharacterLocalization` are not used, and that module is unchanged. The module proves no finiteness, multiplicity-one or representation-theoretic statement.
