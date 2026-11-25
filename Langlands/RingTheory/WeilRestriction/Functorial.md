# Functoriality of the finite-type Weil restriction algebra

The commutative `A`-algebra `B` is finite projective, and `C`, `D`, `E` are commutative `B`-algebras of finite type. There are no topological, faithfulness, field, Noetherian or freeness hypotheses, and the universes of the algebras are independent.

[FiniteType](FiniteType.md) constructs the `A`-algebra `WeilRestrictionFiniteType A B C` together with a bijection `homEquiv A B C T` between `A`-algebra maps `WeilRestrictionFiniteType A B C →ₐ[A] T` and `B`-algebra maps `C →ₐ[B] B ⊗[A] T`, the points of `C` over `T`. The point of a map `g` is `B ⊗ g` composed with the universal point (`homEquiv_apply`), and for `h : T →ₐ[A] T'` the point of `h ∘ g` is `B ⊗ h` composed with the point of `g` (`homEquiv_comp`). This file makes the construction a functor in `C`.

It is derived infrastructure for Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), Example 2.4, printed page 3: it supplies the map of representing algebras needed to state preservation of closed immersions without a finite-presentation hypothesis.

## The induced map

For `φ : C →ₐ[B] D`, the composite of `φ` with the universal point of `D` is a point of `C` over `WeilRestrictionFiniteType A B D`. `map A B φ` is the `A`-algebra map `WeilRestrictionFiniteType A B C →ₐ[A] WeilRestrictionFiniteType A B D` with that point, that is, its preimage under `homEquiv`.

- `homEquiv_map`: the point of `map A B φ` is the universal point of `D` composed with `φ`. This is the definition, read through the bijection.
- `lTensor_map_universalPoint`: the same statement evaluated at `c : C`; `B ⊗ map A B φ` sends the universal point at `c` to the universal point at `φ c`. It is a `simp` lemma.
- `homEquiv_comp_map`: for `g` out of the Weil restriction of `D`, the point of `g ∘ map A B φ` is the point of `g` composed with `φ`. By `homEquiv_comp` the left side is `B ⊗ g` composed with the point of `map A B φ`, which `homEquiv_map` identifies; the result is the point of `g` composed with `φ` by `homEquiv_apply`.

## Functor laws

Both are proved by comparing points, using that `homEquiv` is injective.

- `map_id`: the point of `map A B (AlgHom.id B C)` is the universal point (`homEquiv_map`), and so is the point of the identity, since `B ⊗ id` is the identity.
- `map_comp`: for `ψ : D →ₐ[B] E`, the point of `map A B ψ ∘ map A B φ` is the point of `map A B ψ` composed with `φ` (`homEquiv_comp_map`), which is the universal point of `E` composed with `ψ` and then with `φ`. This is the point of `map A B (ψ ∘ φ)`.

## Comparison with the finitely presented case

When `C` and `D` are finitely presented, [FiniteType](FiniteType.md) gives isomorphisms `finitePresentationAlgEquiv` with `Langlands.Algebra.WeilRestriction`, which has its own map `Langlands.Algebra.WeilRestriction.map A B φ` (see [PresentedAlgebra](PresentedAlgebra.md)). `finitePresentationAlgEquiv_map` states that the square formed by the two maps and the two isomorphisms commutes.

The proof computes the point of both composites as maps out of `WeilRestrictionFiniteType A B C`. For the composite through `WeilRestriction A B C`, `homEquiv_comp_finitePresentationAlgEquiv` turns it into the point of `WeilRestriction.map A B φ` for the other bijection, which is the universal point of `WeilRestriction A B D` composed with `φ`. For the composite through `WeilRestrictionFiniteType A B D`, `homEquiv_comp_map` gives the point of the comparison isomorphism of `D` composed with `φ`, and that point is the same universal point by `finitePresentationAlgEquiv_universalPoint`.

Preservation of surjections, and the closed-immersion statement for schemes, are in [WeilRestrictionClosedImmersionProof](../../AlgebraicGeometry/PointTopology/WeilRestrictionClosedImmersionProof.md).
