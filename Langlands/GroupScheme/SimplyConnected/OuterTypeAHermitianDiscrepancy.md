# The Hermitian presentation from discrepancy predicates

Author: Worker 5375.

This internal module belongs to Task 6209 (`OuterTypeAHermitianPresentationStatement`).
It restates the hypotheses of `OuterTypeAHermitian.exists_hermitianPresentation`
(module `OuterTypeAHermitianTorus`) in the vocabulary of the special-linear cocycle API.
That vocabulary is the one in which the cocycle side of the proof delivers its results.
The module proves no new mathematics: each step only unfolds a definition.

## Setting

The setting is that of `OuterTypeAHermitianDescent`:
- `K`, `L`, `M` are fields in one universe, of any characteristic.
- `L` and `M` are `K`-algebras, `M` is an `L`-algebra and `IsScalarTower K L M` holds.
- `L/K` is a separable quadratic extension.
- `H` is a `HermitianMatrix.Form` over `L` for the conjugation of `L/K`, indexed by
  `Fin (n + 1)`.
- `E` is a local isomorphism from `SL_(n+1)` over `Spec K` to a group scheme `G` over the
  cover `Spec M → Spec K`.

The image of `L` in `M` is the field range of `IsScalarTower.toAlgHom K L M`, whose
underlying map is `algebraMap L M`.

## Definition

`HermitianOuterDiscrepancy L H E` says the following. For every `σ ∈ Aut_K(M)` that moves
some `algebraMap L M y`, the published `HasOuterDiscrepancy E σ X` holds with `X` the image
of `H⁻¹` in `GL_(n+1)(M)`. That predicate says: for every test scheme `Z`, cover point `a`
and `g ∈ SL_(n+1)(Γ(Z))`, the discrepancy of `E` at `σ` sends `g` to
`a(X) · (g⁻¹)ᵀ · a(X)⁻¹`, computed in `GL_(n+1)(Γ(Z))`. Here `a(X)` is `X` with the
coefficient map of `a` applied to its entries, and `(g⁻¹)ᵀ` is `inverseTranspose g`.

## Results

- `innerTrivial_of_hasTrivialDiscrepancy`: assume `HasTrivialDiscrepancy E S`, with `S`
  the fixing subgroup of the image of `L`. Then `InnerTrivial L E` holds.
  - `HasTrivialDiscrepancy` comes from the module `SpecialLinearTitsOuterDiscrepancy`. It
    says that every element of `S` has identity discrepancy on every test.
  - `InnerTrivial L E` says that every `σ` fixing each `algebraMap L M y` has identity
    discrepancy on every test.
  - Proof: such a `σ` lies in `S` by `IntermediateField.mem_fixingSubgroup_iff`.
- `outerHermitian_of_hermitianOuterDiscrepancy`: `HermitianOuterDiscrepancy L H E`
  implies `OuterHermitian L H E`.
  - `OuterHermitian L H E` is the same identity read on underlying matrices.
  - Proof: take underlying matrices of the `GL` equation (`Units.val_mul`). Then rewrite
    `a(X⁻¹) = a(X)⁻¹` (`map_inv`). The `SL` and `GL` coercions agree definitionally.
- `exists_hermitianPresentation_of_discrepancy`: assume `IsGalois K M`, that `G` is
  affine over `Spec K`, the two predicates above and `TorusDiagonal E incl ch`. Then the
  conclusion of `exists_hermitianPresentation` holds. Namely, there is a family `ρ` of
  group homomorphisms from `T`-points of `G` to `GL_(n+1)(L ⊗_K Γ(T))` with these
  properties:
  - it is injective on every test scheme;
  - its image is exactly the determinant-one isometries of `H` over `L ⊗_K Γ(T)`;
  - it is natural in `T`;
  - it sends `s ≫ incl` to the diagonal matrix with entries `1 ⊗ χ_i(s)`.

  These are clauses 3 to 6 of the conclusion of `OuterTypeAHermitianPresentationStatement`
  with `J = H.gram`. The proof applies `exists_hermitianPresentation` to the two
  conversions above.

## Provenance and scope

The provenance is internal; this is an interface translation between two internal APIs.
The module does not produce `E`, `H`, the torus data or any of the hypotheses. It does not
prove the star-action, Hermitian-symmetry or root-restriction clauses of the target
statement.
