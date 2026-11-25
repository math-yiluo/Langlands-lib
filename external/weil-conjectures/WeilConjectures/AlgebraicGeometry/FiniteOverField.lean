/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Artinian.Algebra
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Schemes finite over a field

A scheme `Z` finite over a field `K` is affine, its ring of global sections is a finite
`K`-algebra, hence artinian, and so `Z` is a finite discrete space.

## Main statements

- `AlgebraicGeometry.finite_sections_top_of_isFinite`: `Γ(Z, 𝒪_Z)` is finite over `K`.
- `AlgebraicGeometry.finite_and_discreteTopology_of_isFinite`: `Z` is a finite discrete space.
- `AlgebraicGeometry.IsFinite.of_finite_of_locallyOfFiniteType`: conversely, a finite scheme
  locally of finite type over `K` is finite over `K`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- The global sections of a scheme finite over a field `K` form a finite `K`-algebra. -/
lemma finite_sections_top_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g] :
    letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appLE ⊤ ⊤ le_top).hom.toAlgebra
    Module.Finite K Γ(Z, ⊤) := by
  have hfin := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := g)).mp inferInstance
  rw [Scheme.Hom.appLE_top_top]
  have h2 : RingHom.Finite ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom := by
    rw [CommRingCat.hom_comp]
    exact hfin.2.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  exact h2

/-- A scheme finite over a field is a finite discrete space. -/
lemma finite_and_discreteTopology_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K))
    [IsFinite g] : Finite Z ∧ DiscreteTopology Z := by
  have : IsAffine Z := isAffine_of_isAffineHom g
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appLE ⊤ ⊤ le_top).hom.toAlgebra
  have := finite_sections_top_of_isFinite g
  have : IsArtinianRing Γ(Z, ⊤) := .of_finite K Γ(Z, ⊤)
  let e := Scheme.homeoOfIso Z.isoSpec
  have : Finite (Spec Γ(Z, ⊤)) := inferInstanceAs (Finite (PrimeSpectrum Γ(Z, ⊤)))
  have : DiscreteTopology (Spec Γ(Z, ⊤)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum _))
  exact ⟨Finite.of_injective e e.injective, e.isEmbedding.discreteTopology⟩

/-- **A finite scheme locally of finite type over a field is finite over it**: the morphism is
quasi-compact, the source being a finite space, and locally quasi-finite, its fibre being finite,
over the artinian scheme `Spec K`. -/
lemma IsFinite.of_finite_of_locallyOfFiniteType {Z : Scheme.{u}} [Finite Z]
    (g : Z ⟶ Spec (.of K)) [LocallyOfFiniteType g] : IsFinite g :=
  have : LocallyQuasiFinite g :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  IsFinite.of_locallyQuasiFinite g

/-- A nonempty scheme finite over a field `K` has non-zero `dim_K Γ(Z, 𝒪_Z)`. -/
lemma Scheme.Hom.finrankΓ_pos_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g]
    [Nonempty Z] : 0 < g.finrankΓ := by
  let _ := g.ΓAlgebra
  have : Module.Finite K Γ(Z, ⊤) := by
    have := finite_sections_top_of_isFinite g
    rwa [Scheme.Hom.appLE_top_top] at this
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨Classical.arbitrary Z, trivial⟩⟩
  exact Module.finrank_pos

end AlgebraicGeometry
