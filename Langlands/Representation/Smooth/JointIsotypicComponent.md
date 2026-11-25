# An isotypic component inside a jointly irreducible smooth representation

Lean module: `Langlands.Representation.Smooth.JointIsotypicComponent`
(namespace `Langlands.JointIsotypic`). It imports
`Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof`,
`Langlands.Representation.FiniteVectors` and
`Mathlib.RingTheory.TensorProduct.Finite`. It adds helper definitions and proved theorems without changing any
published module. It is a helper for the proof of
`Langlands.Automorphic.LocalComponentExistenceStatement`
(`localComponentExistence` in `Langlands.Automorphic.LocalComponentExistenceProof`); the
module `Langlands.Automorphic.LocalComponentFinitePlace` applies it.

## Setting

`G` is a group, `V` a complex vector space, `σ : Representation ℂ G V`, and
`C : Set (Module.End ℂ V)` a set of linear operators on `V`.

- `IsJointlyIrreducible σ C`: every subspace `P` of `V` that is stable under
  every `σ g` and every `c ∈ C` is `⊥` or `⊤`.
- `CommutesWith σ C`: `c (σ g x) = σ g (c x)` for all `c ∈ C`, `g`, `x`.
- `commutingHom c hc`: an operator commuting with `σ`, as an intertwining map
  `σ → σ` (with `commutingHom_apply`).

## Results

### Isotypy (`iSup_range_eq_top`)

If `CommutesWith σ C` and `IsJointlyIrreducible σ C`, then for every nonzero
subrepresentation `U` of `σ` the images of the intertwining maps
`U.toRepresentation → σ` span `V`.

Proof. Let `T` be the span of these images. It is stable under `σ g` (compose
a map with `U`'s own action) and under every `c ∈ C` (post-compose with
`commutingHom c`). By joint irreducibility `T = ⊥` or `T = ⊤`. The inclusion
`U → V` (`TwoFactorExistence.subtypeHom`) shows that `T` contains the nonzero
vectors of `U`, so `T = ⊤`.

### Irreducible orbit spans

- `isIrreducible_orbitSubrepresentation`: if `y ≠ 0` lies in the orbit span
  of every nonzero vector of its own orbit span (`FiniteVectors.orbitSpan`),
  the orbit subrepresentation of `y` is irreducible.
- `orbitSubrepresentation_ne_bot`: the orbit subrepresentation of `y ≠ 0` is
  nonzero.

### With a topology (`G` a topological group)

- `exists_fixed_of_ne_bot`: let `σ` be smooth, `K` a compact open subgroup,
  and `x ≠ 0` a `K`-fixed vector. Under `CommutesWith σ C` and
  `IsJointlyIrreducible σ C`, every nonzero subrepresentation `N` of `σ`
  contains a nonzero `K`-fixed vector. Proof: let `e` be averaging over `K`
  (`Compact.averageMap`, which commutes with intertwining maps,
  `Compact.averageMap_commute`). If `e` kills `N`, then
  `Z = {v | e (σ g v) = 0 for all g}` is stable under `σ` and `C` and
  contains `N ≠ 0`, so `Z = ⊤`; but `e x = x ≠ 0`.
- `exists_cyclic`: suppose every open subgroup contains a compact open one
  (`hcpt`), and `N` is a subrepresentation whose intersection with the fixed
  vectors of every compact open subgroup is finite-dimensional. Then a
  nonzero `x ∈ N` gives a nonzero `y ∈ N` lying in the orbit span of every
  nonzero vector of its own orbit span. `y` minimizes, among the nonzero
  `K`-fixed vectors of `N` (for a compact open `K` fixing `x`), the dimension
  of the `K`-fixed part of its orbit span inside `N`; `exists_fixed_of_ne_bot`
  and the minimality give the property.
- `isAdmissible_of_le`: under the same hypotheses on `N`, every
  subrepresentation `U ≤ N` is admissible (`Langlands.IsAdmissible`, all open
  subgroups).
- `exists_irreducible_admissible_isotypic`: combining the three, under
  `CommutesWith σ C`, `IsJointlyIrreducible σ C`, smoothness, `hcpt` and such
  an `N ∋ x ≠ 0`, there is an irreducible admissible subrepresentation `U`
  of `σ` such that the images of the intertwining maps `U → σ` span `V`.

### Type spans (a supply of `N`)

Let `κ : Representation ℂ K V` be a representation of a second group `K`
commuting with `σ`, `τ : Representation ℂ K E` a representation on a
finite-dimensional space, and `P` a subrepresentation of `σ`.

- `equivariantInto κ τ P`: the `K`-equivariant linear maps `E → V` with
  values in `P` (`mem_equivariantInto`, `equivariantInto_mono`).
- `typeSpan κ τ P`: the span of their images (`apply_mem_typeSpan`); it is
  `σ`-stable (`typeSpan_stable`), giving `typeSpanSubrepresentation`.
- `finiteDimensional_fixedVectors_inf_typeSpan`: for a compact open `L`, if
  the space `J` of equivariant maps with values in `P ⊓ V^L` is
  finite-dimensional, so is `V^L ⊓ typeSpan κ τ P`. Averaging over `L` maps
  the type span into the image of `J ⊗ E → V`, `φ ⊗ w ↦ φ w`, and fixes
  `V^L`.
- `exists_irreducible_admissible_isotypic_of_typeSpan`: the existence theorem
  with `N = typeSpan κ τ P`; it needs one equivariant map `φ` into `P` and a
  vector `w` with `φ w ≠ 0`.

## Provenance

The isotypy statement is the one Flath records at the end of the proof of his
Theorem 1: for an admissible irreducible module `W ≅ W₁ ⊗ W₂` of
`G₁ × G₂`, "the restriction of `W` to `G_i` is `W_i`-isotypic" (Flath,
*Decomposition of representations into tensor products*, Corvallis Part I,
1979, p.180, PDF page 176 of the registered file `flath-1979-tensor-products`,
SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`;
printed page = PDF page + 4).

The route is an internal adaptation of the two-factor argument and does not
factor `V` as a tensor product. It
generalizes the published proof of Flath's two-factor theorem
(`Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof`),
where `C` is the action of the second factor: `exists_fixed_of_ne_bot`,
`exists_cyclic` and `isIrreducible_orbitSubrepresentation` follow that
module's averaging argument and minimal-dimension choice, with "stable under
the second factor" replaced by "stable under `C`". The isotypy argument
(the span of the images of `Hom(U, V)` is stable under `σ` and `C`) replaces
the tensor factorization. The type-span finiteness replaces the admissibility
of the whole representation, which is not available in the application
(an automorphic representation is only jointly admissible).

## Axioms

The module uses only `propext`, `Classical.choice` and `Quot.sound`
(inspection of the dependent theorem
`Langlands.Automorphic.localComponentExistenceStatement_of_infinitePlaces`).
