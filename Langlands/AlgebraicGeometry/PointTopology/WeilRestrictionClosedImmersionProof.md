# Proof of closed-immersion preservation for finite-type Weil restriction

The file proves `WeilRestrictionClosedImmersionProperties A B`, the statement of `WeilRestrictionClosedImmersionStatement.lean`. This is the closed-immersion preservation step in Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), Example 2.4, printed page 3 (registered source `conrad-2011-weil-grothendieck-adelic-points`).

All rings are arbitrary commutative rings, and `B` is finite projective over `A`. No topology, faithfulness, field, Noetherian or finite-presentation hypothesis is used. This scope extends Conrad's formulation for a ring extension: the only property of `A → B` needed below is that `B` is flat over `A`, so injectivity of `A → B` is not required. The extension is already part of the stated target.

Notation is that of [Functorial](../../RingTheory/WeilRestriction/Functorial.md): `C` is a `B`-algebra of finite type, `homEquiv A B C T` sends an `A`-algebra map `g : WeilRestrictionFiniteType A B C →ₐ[A] T` to its point `C →ₐ[B] B ⊗[A] T`, and `map A B φ` is the map induced by `φ : C →ₐ[B] D`.

## Factoring through an injective map

The private lemma `range_le_range_iff_exists_comp` is about algebra maps `j : X →ₐ[R] Y` and `f : Z →ₐ[R] Y` with `j` injective: the range of `f` lies in the range of `j` if and only if `f = j ∘ v` for some `v : Z →ₐ[R] X`. If `f = j ∘ v` the inclusion of ranges is clear. Conversely `j` is an isomorphism onto its range (Mathlib's `AlgEquiv.ofInjective`), and `v` is `f`, regarded as a map into that range, followed by the inverse.

## Ranges and points

`range_le_iff_range_homEquiv_le`: for `g : WeilRestrictionFiniteType A B C →ₐ[A] T` and a subalgebra `S` of `T`, the range of `g` lies in `S` if and only if the range of the point of `g` lies in the range of `B ⊗[A] S → B ⊗[A] T`.

The proof applies the lemma twice. The inclusion `S → T` is injective with range `S`, so the left condition says that `g` factors through `S`. The map `B ⊗[A] S → B ⊗[A] T` is injective because the projective module `B` is flat over `A` (`Module.Flat.lTensor_preserves_injective_linearMap`), so the right condition says that the point of `g` factors through `B ⊗[A] S`. These two factorizations correspond to each other:

- if `g = (S → T) ∘ g'`, then by `homEquiv_comp` the point of `g` is the point of `g'` followed by `B ⊗[A] S → B ⊗[A] T`;
- if the point of `g` is `v` followed by `B ⊗[A] S → B ⊗[A] T`, let `g'` be the map to `S` with point `v`. By `homEquiv_comp` the map `(S → T) ∘ g'` has the same point as `g`, so it equals `g` because `homEquiv` is injective.

## Surjections

`map_surjective`: if `φ : C →ₐ[B] D` is surjective, then so is `map A B φ`.

Let `S` be the range of `map A B φ`, a subalgebra of `WeilRestrictionFiniteType A B D`. The criterion, applied to `map A B φ` itself, says that its point, the universal point of `D` composed with `φ` (`homEquiv_map`), has range in the image of `B ⊗[A] S`. Since `φ` is surjective, this range is the range of the universal point of `D` (`AlgHom.range_comp`, `Algebra.map_top`). The universal point is the point of the identity map (`map_id` and `homEquiv_map`), so the criterion, now applied to the identity, says that the range of the identity lies in `S`. Hence `S` is everything.

No finite-presentation assumption enters: only the representing bijection for algebras of finite type is used.

## Schemes

`affineWeilRestrictionMap_isClosedImmersion`: for affine schemes `X`, `Y` locally of finite type over `Spec B` and a morphism `f : X ⟶ Y` over `Spec B` that is a closed immersion, `affineWeilRestrictionMap A B f` is a closed immersion.

A closed immersion into an affine scheme is surjective on global sections (Mathlib's `IsClosedImmersion.isAffine_surjective_of_isAffine`), so `affineCoordinatePullback B f` is surjective, and by `map_surjective` so is the induced map of Weil restriction algebras. The morphism `affineWeilRestrictionMap A B f` is `Spec` of that map (`ringTestMap_left`), and `Spec` of a surjective ring map is a closed immersion (`IsClosedImmersion.spec_of_surjective`).

`weilRestrictionClosedImmersionProperties_proof` puts `map_surjective` and `affineWeilRestrictionMap_isClosedImmersion` together; these are the two parts of the target.
