# Every torus is a quotient of an induced torus

This module proves the unchanged published proposition
`Langlands.GroupScheme.InducedTorusQuotientStatement.{u}` by the theorem

```lean
theorem Langlands.GroupScheme.inducedTorusQuotient :
    Langlands.GroupScheme.InducedTorusQuotientStatement.{u}
```

For every field `k : Type u` and group scheme `T` over `Spec k` satisfying `IsTorus T`,
it constructs a commutative algebra `A : Type u` with `Algebra.Etale k A` and
`Module.Finite k A`, and a group scheme homomorphism
`WeilGm.groupScheme (CommRingCat.of k) A ⟶ T` whose underlying scheme morphism is
flat and surjective. There are no further hypotheses on the field or torus.
The statement module and its imports are unchanged.

## Provenance

The target is Proposition 12.63, printed p.251, of James S. Milne,
*Algebraic Groups: The Theory of Group Schemes of Finite Type over a Field* (2017),
registered source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Definition 12.62 and Lemma 12.61 on the same page describe induced tori and their
permutation character modules. Definition 5.5, printed p.99, identifies quotient
maps with faithfully flat homomorphisms; the published statement's Markdown records
that source correspondence.

The original Proposition 12.63 proof was read on printed p.251 (PDF p.267).
The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` was also read: its Chapter 12 entries
concern 12.41 and 12.57, with no correction to 12.61–12.63.

The implemented argument uses an explicit permutation-lattice injection, rather than
constructing a surjection onto the dual lattice and dualizing as Milne does. It chooses
a single finite Galois splitting extension `E/k` and takes `A` to be a finite product
of copies of `E`. The auxiliary coordinate construction is internal derived content.
All group scheme realization and descent results it uses are published Library theorems.

## The permutation-lattice injection

The helper declarations are in namespace `Langlands.GroupScheme.InducedTorusQuotient`.
They use the definitions in `Torus.GaloisLatticeRealizationProof`:

- `Coord k E J` consists of pairs `c = (j, τ)`, where `τ` is a `k`-embedding of the
  top intermediate field of `E/k` into `E`.
- `gal k E τ` is the automorphism of `E/k` associated to this embedding.
- `permRep J σ` acts by inverse pullback on coordinates:
  `(permRep J σ m)(j, τ) = m(j, σ⁻¹ ∘ τ)`.

For an integral representation `ρ` on an abelian group `V` with a finite basis `b`
indexed by `J`, `coordinateMap ρ b` is the integral linear map

```text
x ↦ (c ↦ (b.equivFun (ρ (gal k E c.2)⁻¹ x)) c.1).
```

It is defined as a family of composites of linear maps.

`coordinateMap_equivariant` proves
`coordinateMap ρ b (ρ σ x) = permRep J σ (coordinateMap ρ b x)`.
At each coordinate, `gal_comp` identifies the automorphism belonging to
`σ⁻¹ ∘ τ` with `σ⁻¹ * gal τ`. Taking its inverse gives `(gal τ)⁻¹ * σ`,
and the representation's multiplication law proves the equality.

`coordinateMap_injective` evaluates an equality of coordinate vectors at
`(j, (⊤ : IntermediateField k E).val)`. By `gal_val`, the corresponding automorphism
is the identity, so all the original basis coordinates agree. Injectivity of
`b.equivFun` then gives equality in `V`. This proof also covers the empty basis.

## Proof of the target

1. `IsTorus.isCommMonObj` equips the original `T` with a commutativity certificate,
   giving a commutative group scheme `Tc` whose underlying group scheme is `T`.
   `torusFiniteGaloisSplitting` gives a finite Galois extension `E/k` splitting `T`.
   Write `bc` for base change from `k` to `E`.
2. A splitting isomorphism of `bc.obj Tc` with a finite split torus supplies an index
   type `J`. The character isomorphism of that split torus transports the standard
   basis to a basis `b` of `X*(T_E)`. Let `ρ` be its actual Galois representation.
3. Set `R = permTorus k E J`, the commutative Weil restriction from
   `A = ∀ j : J, (⊤ : IntermediateField k E)`. Its base change is split by
   `permTorus_isSplit`. The published equivalence
   `WeilGm.productEmbeddingCharacterEquiv` identifies `X*(R_E)` with
   `Coord k E J → ℤ`.
4. Compose `coordinateMap ρ b` with the inverse of that equivalence to obtain
   `F : X*(T_E) →+ X*(R_E)`. It is injective by `coordinateMap_injective`.
   Its equivariance follows from `coordinateMap_equivariant` and
   `permTorus_equiv_symm_galois`, which concerns the actual Galois action on the
   Weil restriction's characters.
5. `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap` descends `F` to a
   homomorphism `φ : R ⟶ Tc`. Its character pullback after base change is exactly
   `F`, by the equality supplied by that theorem, hence is injective. The resulting
   underlying group scheme homomorphism is the required `q`.
6. `IsSplitTorus.flat_and_surjective_of_injective_characterPullback` applies to the
   base change of `q`, since both its source and target are split tori. It proves
   flatness and surjectivity over `E`.
7. Each factor of `A` is finite separable over `k`.
   `Algebra.FormallyEtale.of_isSeparable` gives formal étaleness; finite generation
   over the noetherian field `k` gives finite presentation by
   `Algebra.FinitePresentation.of_finiteType`. The finite-product instance then
   gives `Algebra.Etale k A`. Module finiteness is the finite-product instance for
   the finite-dimensional field factors.
8. `fieldExtension_fpqc` makes `Spec E → Spec k` flat, surjective and quasi-compact.
   `baseChange_map_isPullback` identifies the underlying scheme map of the
   base-changed `q` with its pullback along the projection from `T_E` to `T`.
   That projection is itself fpqc. Two applications of
   `MorphismProperty.of_isPullback_of_descendsAlong` descend flatness and surjectivity
   to `q`, completing the exact existential statement.

## Validation scope

Compilation and declaration inspection succeeded with zero errors and
zero warnings.
The theorem has the single universe parameter `u`; its assumptions are only
`propext`, `Classical.choice`, and `Quot.sound`.
