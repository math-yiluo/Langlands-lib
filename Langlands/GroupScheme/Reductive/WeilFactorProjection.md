# Factor projections of a Weil restriction attached to idempotents

Module `Langlands.GroupScheme.Reductive.WeilFactorProjection`, namespace
`Langlands.GroupScheme.WeilFactor`. It imports
[`AffineIdempotentPoints`](../AffineIdempotentPoints.md) and
[`AffineWeilRestriction`](../AffineWeilRestriction.md).

## Provenance

Provenance: derived/internal. For a finite projective `A`-algebra `B`, an affine group `G` over
`Spec B`, an `A`-algebra `T` and an idempotent `e ∈ B ⊗_A T`, the Weil restriction
`H = R_{B/A}(G)` over `T` has the endomorphism "keep the `e`-component, kill the
`(1 - e)`-component". These are the transformations classified by
[`WeilFactorIdempotentRigidityStatement`](WeilFactorIdempotentRigidityStatement.md).

## Declarations

`A B : Type u`, `B` finite and projective over `A`, `G : GroupScheme (Spec B)` affine and
locally of finite type, and `T : CommAlgCat (CommRingCat.of A)`.

- `lTensor_lTensor`: composition of the maps `B ⊗ X → B ⊗ Y → B ⊗ Z` induced by algebra maps.
- `Fun A B G T := Under.forget T ⋙ (AffineWeil.groupScheme A B G).affinePointFunctor`: the
  group functor of `H` on `T`-algebras. This is the functor in the rigidity statement.
- `baseIdem X e`: the image of `e` in `B ⊗_A X.right` (`Algebra.TensorProduct.lTensor B X.hom.hom`).
- `factorProjection A B G e he : Fun A B G T ⟶ Fun A B G T` (for idempotent `e`): on points
  over `X`, `x ↦ pointsEquiv⁻¹ (proj (baseIdem X e) (pointsEquiv x))`. Naturality uses
  `AffineWeil.pointsEquiv_naturality` and `IdempotentPoints.proj_map`.
- `pt ψ X`: the component of a transformation `ψ` as a homomorphism of
  `H.affinePoints (CommAlgCat.of _ X.right)`. Lemmas `pt_comp` and `ext_pt` (transformations
  agreeing on all points are equal).
- `pointsEquiv_pt_factorProjection`: the defining formula.
- `factorProjection_spec`: `factorProjection e` satisfies the property in the conclusion of
  the rigidity statement for `e`.
- `eq_factorProjection`: any transformation with that property for `e` equals
  `factorProjection e` (by `IdempotentPoints.eq_proj_iff`).
- `factorProjection_comp`: `factorProjection e ≫ factorProjection f = factorProjection (f e)`.
- `factorProjection_idem`: `factorProjection e` is idempotent.
- `pt_factorProjection_zero`: `factorProjection 0` is trivial.
- `pt_factorProjection_conj`: `factorProjection e` is normal (commutes with conjugation).
- `restrict χ ψ`: restriction of a transformation over `T` to `T₁`-algebras along
  `χ : T ⟶ T₁` (via `Under.map χ`), with `pt_restrict` and `restrict_comp`.
- `restrict_factorProjection`: `restrict χ (factorProjection e) = factorProjection (lTensor χ e)`.
