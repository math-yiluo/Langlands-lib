/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-!
# Cokernels of monomorphisms between dualizable objects are dualizable in `D(A)`

Let `A` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, and `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` a short exact sequence in `A` with `X₁` and `X₂`
dualizable. Then `X₃`, placed in degree zero, is dualizable in the derived category `D(A)`
(`DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact`): it is quasi-isomorphic to the
mapping cone of `X₁[0] ⟶ X₂[0]`, a bounded complex of dualizable objects.

The intended application is the constant complex `(Λ/ϖⁿ)_X` on a site, for a nonzerodivisor `ϖ`
of the coefficient ring `Λ`: it is the cokernel of `ϖⁿ : Λ_X ⟶ Λ_X`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

section

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]

/-- The mapping cone of a morphism `X₁[0] ⟶ X₂[0]` of complexes concentrated in degree zero
has its terms of degree `-1` and `0` dualizable as soon as `X₁` and `X₂` are, and all other
terms zero. -/
lemma isDualizable_mappingCone_single_X {X₁ X₂ : A} (h₁ : IsDualizable X₁)
    (h₂ : IsDualizable X₂)
    (φ : (HomologicalComplex.single A (.up ℤ) 0).obj X₁ ⟶
      (HomologicalComplex.single A (.up ℤ) 0).obj X₂) (n : ℤ) :
    IsDualizable ((CochainComplex.mappingCone φ).X n) := by
  refine IsDualizable.of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm ?_
  by_cases hn : n = -1
  · subst hn
    refine IsDualizable.biprod_of_isZero_right ?_
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide))
    exact h₁.of_iso (HomologicalComplex.singleObjXIsoOfEq _ 0 X₁ (-1 + 1) rfl).symm
  by_cases hn' : n = 0
  · subst hn'
    refine IsDualizable.biprod_of_isZero_left ?_
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide))
    exact h₂.of_iso (HomologicalComplex.singleObjXSelf _ 0 X₂).symm
  · refine IsDualizable.biprod_of_isZero_left (IsZero.isDualizable ?_) ?_
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hn'
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)

end

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

/-- **The cokernel of a monomorphism between dualizable objects is dualizable in `D(A)`.** For
a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in `A` with `X₁` and `X₂` dualizable, the complex
`X₃[0]` is dualizable in `D(A)`: it is quasi-isomorphic to the mapping cone of
`X₁[0] ⟶ X₂[0]` (`CochainComplex.mappingCone.quasiIso_descShortComplex`), a complex
concentrated in degrees `-1` and `0` with dualizable terms
(`DerivedCategory.isDualizable_Q_obj`). -/
theorem isDualizable_singleFunctor_obj_of_shortExact {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : IsDualizable S.X₁) (h₂ : IsDualizable S.X₂) :
    IsDualizable ((singleFunctor A 0).obj S.X₃) := by
  let S' := S.map (HomologicalComplex.single A (.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have : (CochainComplex.mappingCone S'.f).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  have : (CochainComplex.mappingCone S'.f).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  exact (isDualizable_Q_obj _ (-1) 0 (isDualizable_mappingCone_single_X h₁ h₂ S'.f)).of_iso
    (asIso (Q.map (CochainComplex.mappingCone.descShortComplex S')) ≪≫
      ((singleFunctorIsoCompQ A 0).app S.X₃).symm)

end DerivedCategory
