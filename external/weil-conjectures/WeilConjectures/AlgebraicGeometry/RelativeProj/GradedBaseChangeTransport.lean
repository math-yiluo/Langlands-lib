/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.Affine

/-! # Transport of coefficientwise graded base change

## References

* Stacks Project, Constructions, Tag 01O3
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace GradedRingHom

private theorem degree_bijective
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    {D : ℕ → Submodule R A} {D' : ℕ → Submodule S B}
    [GradedAlgebra D] [GradedAlgebra D']
    (f : D →+*ᵍ D') (hf : Function.Bijective f) (n : ℕ) :
    Function.Bijective (f.gradedAddHom n) := by
  constructor
  · intro a b hab
    exact Subtype.ext (hf.injective (congrArg Subtype.val hab))
  · intro b
    obtain ⟨a, ha⟩ := hf.surjective b
    refine ⟨DirectSum.decompose D a n, ?_⟩
    apply Subtype.ext
    change f (DirectSum.decompose D a n) = (b : B)
    rw [f.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same D' b.property]

/-- A coefficientwise graded base change is preserved by graded algebra isomorphisms
on source and target. -/
theorem isGradedBaseChangeAlong_transport
    {R S A₀ A₁ B₀ B₁ : Type u}
    [CommRing R] [CommRing S] [CommRing A₀] [CommRing A₁]
    [CommRing B₀] [CommRing B₁]
    [Algebra R A₀] [Algebra R A₁] [Algebra S B₀] [Algebra S B₁]
    {D₀ : ℕ → Submodule R A₀} {D₁ : ℕ → Submodule R A₁}
    {E₀ : ℕ → Submodule S B₀} {E₁ : ℕ → Submodule S B₁}
    [GradedAlgebra D₀] [GradedAlgebra D₁] [GradedAlgebra E₀] [GradedAlgebra E₁]
    (f : R →+* S) (φ : D₀ →+*ᵍ E₀) (hφ : φ.IsGradedBaseChangeAlong f)
    (α : D₁ →+*ᵍ D₀) (hα : Function.Bijective α)
    (hαR : ∀ r : R, α (algebraMap R A₁ r) = algebraMap R A₀ r)
    (β : E₀ →+*ᵍ E₁) (hβ : Function.Bijective β)
    (hβS : ∀ s : S, β (algebraMap S B₀ s) = algebraMap S B₁ s) :
    (β.comp (φ.comp α)).IsGradedBaseChangeAlong f := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R B₀ := ((algebraMap S B₀).comp f).toAlgebra
  let : Algebra R B₁ := ((algebraMap S B₁).comp f).toAlgebra
  let : IsScalarTower R S B₀ := .of_algebraMap_eq' rfl
  let : IsScalarTower R S B₁ := .of_algebraMap_eq' rfl
  have hφR := hφ.map_algebraMap
  have hR : ∀ r : R, (β.comp (φ.comp α)) (algebraMap R A₁ r) =
      algebraMap R B₁ r := by
    intro r
    change β (φ (α (algebraMap R A₁ r))) = algebraMap S B₁ (f r)
    rw [hαR, hφR, hβS]
  refine ⟨hR, ?_⟩
  intro n
  let eα : D₁ n ≃ₗ[R] D₀ n :=
    LinearEquiv.ofBijective (α.degreeLinearMap hαR n) (degree_bijective α hα n)
  let eβ : E₀ n ≃ₗ[S] E₁ n :=
    LinearEquiv.ofBijective (β.degreeLinearMap hβS n) (degree_bijective β hβ n)
  have hcomm : ((β.comp (φ.comp α)).degreeLinearMap hR n).comp
      (LinearEquiv.refl R (D₁ n)).toLinearMap =
      (eβ.restrictScalars R).toLinearMap.comp
        ((φ.degreeLinearMap (fun r ↦ hφR r) n).comp eα.toLinearMap) := by
    ext x
    rfl
  apply (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl R (D₁ n)) eβ hcomm).mp
  exact IsBaseChange.comp_equiv eα _ (hφ.isBaseChange n)

end GradedRingHom
