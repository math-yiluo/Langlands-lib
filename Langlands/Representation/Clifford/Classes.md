# Types lying over classes of a normal subgroup

This internal module sets up the objects counted by Clifford theory for a
topological group `G` and a normal subgroup `N`: the isomorphism classes of
continuous irreducible finite-dimensional complex representations of `G`
("types"), the relation "lies over" between types and open-kernel irreducible
classes of `N`, and the pullback of both kinds of classes along continuous
automorphisms. In the application `G` is the inertia group of a local field
and `N` its wild inertia group.

## Types and the relation over

- `IsTypeRep A` says that `A : FiniteRepresentation.{0, uG, uW} ℂ G` is
  continuous and irreducible; `TypeObj G` is the subtype of such objects,
  `TypeClasses G` the Library's `IsomorphismClassesWith IsTypeRep`, and
  `typeClass B` the class of an object. `typeClass_eq_iff` describes equality
  of classes by equivalences.
- `Over N B A` says that there is a nonzero intertwiner from the restriction
  of `B` to `N` to the open-kernel irreducible object `A` of `N`
  (`WildObj N`, module `Langlands.Representation.Clifford.Stabilizer`).
  `over_of_equiv` shows that it depends only on the classes, and
  `LiesOver N x c` is the induced relation between a type class `x` and a
  class `c` of `N`; `liesOver_iff` compares the two.

## Pullback along continuous automorphisms

- `equivComp` precomposes an equivalence with a homomorphism.
- `conjCts h` is conjugation `g ↦ h g h⁻¹` as a continuous automorphism.
- `typeObjPullback α B` is `B ∘ α`, again continuous and irreducible, and
  `typePullback α` is the induced map on type classes (`typePullback_mk`).
- `conjCompEquiv` and `typeClass_pullback_conj`: `ρ ∘ (g ↦ h g h⁻¹)` is
  equivalent to `ρ` through `ρ h⁻¹`, so inner automorphisms act trivially on
  type classes; consequently `typePullback_conj_trans`: pulling back along
  `conjCts h` followed by `α` is the same as pulling back along `α`.
- For an automorphism `α` with `x ∈ N ↔ α x ∈ N`, `restrictAut` restricts it
  to `N`; it is continuous (`continuous_restrictAut`) and surjective
  (`restrictAut_surjective`). `wildObjPullback α hN A` is `A ∘ α|_N`, an
  open-kernel irreducible object, and `wildPullback α hN` is the induced map
  on `OpenKernelIrreducibleClasses N`.
- Properties of `wildPullback`: `wildPullback_mk` on representatives;
  `symm_mem` and `wildPullback_symm_wildPullback` (pullback along `α⁻¹` is
  inverse to pullback along `α`, hence `wildPullback_injective`);
  `wildPullback_smul`, the identity
  `wildPullback α (g • c) = α⁻¹ g • wildPullback α c`;
  `wildPullback_trans` for composites; `wildPullback_conjCts`, pullback along
  conjugation by `h` is the action of `h⁻¹`.
- `mem_stabilizer_iff_of_fixed`: if the pullback along `α` fixes the class
  `c`, then `α` preserves the stabilizer of `c`, by `wildPullback_smul`.
