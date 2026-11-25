/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The spectrum of an algebraic closure as a scheme over the base field

`Spec K̄`, viewed as an object of `Over (Spec (.of K))`. Morphisms from it to a `K`-scheme `X`
are the geometric points of `X`.

## Main definitions

- `AlgebraicGeometry.Scheme.specAlgebraicClosure`: `Spec K̄` as a scheme over `K`.
- `AlgebraicGeometry.Scheme.specAlgebraicClosureMap`: the endomorphism of `Spec K̄` over `K`
  induced by a `K`-endomorphism of `K̄`. Precomposition with it is the action of
  `Gal(K̄/K)` on geometric points "by coordinates".
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- `Spec K̄`, the spectrum of an algebraic closure of `K`, as a scheme over `K`. Its morphisms
to a `K`-scheme are the geometric points of that scheme. -/
noncomputable def Scheme.specAlgebraicClosure (K : Type u) [Field K] : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))

/-- The endomorphism `Spec σ` of `Spec K̄` over `K` induced by a `K`-algebra endomorphism `σ` of
`K̄`. If a geometric point `P` of an affine `K`-scheme has coordinates `xᵢ ∈ K̄`, then
`specAlgebraicClosureMap σ ≫ P` has coordinates `σ xᵢ`. -/
noncomputable def Scheme.specAlgebraicClosureMap {K : Type u} [Field K]
    (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) :
    Scheme.specAlgebraicClosure K ⟶ Scheme.specAlgebraicClosure K :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) <| by
    change _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σ.commutes x

@[simp]
theorem Scheme.specAlgebraicClosureMap_left {K : Type u} [Field K]
    (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) :
    (Scheme.specAlgebraicClosureMap σ).left = Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  rfl

/-- `σ ↦ Spec σ` is contravariant. -/
theorem Scheme.specAlgebraicClosureMap_comp {K : Type u} [Field K]
    (σ τ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) :
    Scheme.specAlgebraicClosureMap (σ.comp τ) =
      Scheme.specAlgebraicClosureMap σ ≫ Scheme.specAlgebraicClosureMap τ := by
  ext1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

@[simp]
theorem Scheme.specAlgebraicClosureMap_id {K : Type u} [Field K] :
    Scheme.specAlgebraicClosureMap (AlgHom.id K (AlgebraicClosure K)) = 𝟙 _ := by
  ext1
  simp only [specAlgebraicClosureMap_left, Over.id_left]
  exact Spec.map_id _

@[simp]
theorem Scheme.specAlgebraicClosureMap_symm_comp_self {K : Type u} [Field K]
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Scheme.specAlgebraicClosureMap σ.symm.toAlgHom ≫ Scheme.specAlgebraicClosureMap σ.toAlgHom =
      𝟙 _ := by
  rw [← specAlgebraicClosureMap_comp]
  convert specAlgebraicClosureMap_id
  ext x
  exact σ.symm_apply_apply x

@[simp]
theorem Scheme.specAlgebraicClosureMap_comp_symm {K : Type u} [Field K]
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ Scheme.specAlgebraicClosureMap σ.symm.toAlgHom =
      𝟙 _ := by
  simpa using specAlgebraicClosureMap_symm_comp_self σ.symm

end AlgebraicGeometry
