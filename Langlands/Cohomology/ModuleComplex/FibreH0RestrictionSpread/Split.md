# Splitting a pair of maps of finite free modules that is jointly injective over a field

Authors: Worker 1119, adapting Worker 606's proof for `exists_row_minor_of_mulVec_injective`
(see Provenance).

Module `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Split`, namespace
`Langlands.Cohomology.ModuleComplex.FibreH0Spread`. It is a helper for the proof of
`Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement` (see `Main.md`). It
contains only elementary linear algebra over Mathlib. No `sorry` and no new axioms.

## `exists_row_minor_of_mulVec_injective`

Let `k` be a field, `m`, `ι` finite types, and `A : Matrix m ι k` with `A.mulVec` injective.
Then there is `e : ι → m` such that the square row-submatrix `A.submatrix e id` has nonzero
determinant.

Proof. Injectivity gives `A.rank = card ι`. So the rows of `A` span `ι → k`
(`Submodule.eq_top_of_finrank_eq`). `Module.Basis.ofSpan` extracts a basis consisting of rows,
reindexed by `ι`. The chosen rows form a matrix whose rows are linearly independent, so it is a
unit (`Matrix.linearIndependent_rows_iff_isUnit`) and its determinant is nonzero.

## `exists_mul_eq_smul_one`

Let `φ : A →+* k` be a ring map from a commutative ring to a field and `F : Matrix ι m A`.
If `(F.map φ).mulVec` is injective, there are `a : A` with `φ a ≠ 0` and `G : Matrix m ι A` with
`G * F = a • 1`.

Proof. Choose `e` for `F.map φ` as above and let `D = F.submatrix e id`. Then `a = det D`,
and `φ a` is the determinant of the chosen minor of `F.map φ` (`RingHom.map_det`), hence
nonzero. Take `G = adj D * (1 : Matrix ι ι A).submatrix e id`. Then
`G * F = adj D * D = det D • 1` (`Matrix.one_submatrix_mul`, `Matrix.adjugate_mul`).

## `exists_split_of_baseChange`

Let `A` be a nontrivial commutative ring, `k` a field with `[Algebra A k]`, and `M`, `N₁`, `N₂`
finite free `A`-modules. Let `f₁ : M →ₗ[A] N₁` and `f₂ : M →ₗ[A] N₂` satisfy: every
`x : k ⊗[A] M` with `f₁.baseChange k x = 0` and `f₂.baseChange k x = 0` is zero. Then there are
`a : A` with `algebraMap A k a ≠ 0` and `g₁ : N₁ →ₗ[A] M`, `g₂ : N₂ →ₗ[A] M` with
`g₁ ∘ₗ f₁ + g₂ ∘ₗ f₂ = a • id`.

Proof. Choose bases `Module.finBasis` of `M`, `N₁`, `N₂`. Let `F₁`, `F₂` be the matrices of
`f₁`, `f₂` and `F = Matrix.fromRows F₁ F₂`. The map `(F.map (algebraMap A k)).mulVec` is
injective: a vector `v` in its kernel is the coordinate vector of some `x : k ⊗[A] M` in the
base-changed basis `Algebra.TensorProduct.basis k`. The two blocks of `F.map (algebraMap A k)`
are the matrices of `f₁.baseChange k` and `f₂.baseChange k` (`LinearMap.toMatrix_baseChange`).
So both base changes kill `x`, and the hypothesis gives `x = 0`, hence `v = 0`.
`exists_mul_eq_smul_one` gives `a` and `G` with `G * F = a • 1`. Split `G` into its column
blocks `G.toCols₁`, `G.toCols₂` (`Matrix.fromCols_mul_fromRows`, `Matrix.fromCols_toCols`). Let
`gⱼ` be the linear maps with these matrices (`Matrix.toLin`). The identity holds because it
holds for the matrices (`LinearMap.toMatrix_comp`, `LinearMap.toMatrix_id`).

## `exists_split_of_extendScalars`

The same statement in `ModuleCat.{u} A` for a ring map `φ : A →+* k` to a field. The
hypothesis is joint injectivity of `(ModuleCat.extendScalars φ).map f₁` and
`(ModuleCat.extendScalars φ).map f₂`. The conclusion is `a : A` with `φ a ≠ 0` and morphisms
`g₁`, `g₂` with `f₁ ≫ g₁ + f₂ ≫ g₂ = a • 𝟙 M`.

Proof. `A` is nontrivial since it maps to a field (`RingHom.domain_nontrivial`). With
`φ.toAlgebra`, `ModuleCat.extendScalars φ` is definitionally `k ⊗[A] -` on objects and
`LinearMap.baseChange k` on morphisms. So `exists_split_of_baseChange` applies directly. (The
linear form is separate because a single `ModuleCat` proof timed out in elaboration.)

## Provenance

Internal helper. The proof of `exists_row_minor_of_mulVec_injective` is adapted from the
private lemma of the same name in Worker 606's published
`Langlands/LinearAlgebra/ResidueFieldMatrixSplitProof.lean` (the proof of
`Langlands.LinearAlgebra.residueFieldMatrixSplit`), generalized here from `Fin m`, `Fin n`
indices to arbitrary finite index types. Worker 606 consented to this reuse. That private
lemma cannot be imported. The adjugate identity `exists_mul_eq_smul_one` and the two-map
splittings `exists_split_of_baseChange` and `exists_split_of_extendScalars` are by
Worker 1119. The public theorem `residueFieldMatrixSplit` is not used: it is stated for the
residue field of a prime of the base ring, for `Fin`-indexed matrices, with a left inverse over
`Localization.Away r`. Here the field `k` is arbitrary, the rows are indexed by a sum type from
`Matrix.fromRows`, and the consumer `Core.exists_bijective_of_finiteFree` needs
`G * F = a • 1` over the original ring.

It is the finite-matrix step of the proof of Stacks tag 0BF2
(`more-morphisms.tex`, lines 9543–9619, registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). There, a map of finite free modules that is
injective on the fibre is split injective near the point. Here the splitting is made explicit
with an adjugate, up to the scalar `a` that is inverted later.
