/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientEndpoints
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Composition of normalized scalar arrows

Source: diagonal tower coefficient changes, paragraph (2), scalar associativity.
(blueprint: lem-diagonal-scalar-endpoint-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
  [MonObj Λ₂] [IsCommMonObj Λ₂]
  (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (c : Λ₀ ⟶ Λ₂)
  [IsMonHom a] [IsMonHom b] [IsMonHom c]

/-- Composition of exact scalar restrictions, fixed by the ordinary identity-on-sheaves
comparison. Source: scalar associativity (blueprint: lem-diagonal-scalar-endpoint-composition).
-/
def scalarRestrictionCompIso (h : a ≫ b = c) (X : Scheme.{u}) :
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap c X)).mapDerivedCategory ≅
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (coefficientMap b X)).mapDerivedCategory ⋙
        (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap a X)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
        Mod.comapCongr (by rw [← h, coefficientMap_comp]))).symm

/-- The derived scalar associator is the uniqueness comparison of the actual
adjunctions, rather than an independently chosen tensor isomorphism.
Source: scalar associativity (blueprint: lem-diagonal-scalar-endpoint-composition). -/
def scalarCompIso (h : a ≫ b = c) (X : Scheme.{u}) :
    derivedScalars c X ≅ derivedScalars a X ⋙ derivedScalars b X :=
  (Adjunction.leftAdjointCompIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c X))
    (scalarRestrictionCompIso a b c h X).symm).symm

/-- The normalized derived arrow of any semilinear map, before asserting it invertible.
Source: endpoint normalization (blueprint: lem-diagonal-scalar-endpoint-composition). -/
def scalarHom {X : Scheme.{u}} {M : Modules Λ₀ X} {N : Modules Λ₁ X}
    {m : M.X ⟶ N.X} (s : Semilinear a M N m) :
    (derivedScalars a X).obj ((DerivedCategory.singleFunctor (Modules Λ₀ X) 0).obj M) ⟶
      (DerivedCategory.singleFunctor (Modules Λ₁ X) 0).obj N :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor (Modules Λ₀ X) 0).map s.hom ≫
      ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N)

/-- The corresponding normalized arrow after shifting by two.
Source: endpoint shifts (blueprint: lem-diagonal-scalar-endpoint-composition). -/
def scalarShiftHom {X : Scheme.{u}} {M : Modules Λ₀ X} {N : Modules Λ₁ X}
    {m : M.X ⟶ N.X} (s : Semilinear a M N m) :
    (derivedScalars a X).obj
        (((DerivedCategory.singleFunctor (Modules Λ₀ X) 0).obj M)⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (Modules Λ₁ X) 0).obj N)⟦(2 : ℤ)⟧ :=
  ((derivedScalars a X).commShiftIso (2 : ℤ)).hom.app _ ≫
    (scalarHom a s)⟦(2 : ℤ)⟧'

/-- Ordinary composition of semilinear maps using the identity-on-sheaves comparison.
Source: scalar associativity (blueprint: lem-diagonal-scalar-endpoint-composition). -/
def Semilinear.comp {X : Scheme.{u}} {M : Modules Λ₀ X} {N : Modules Λ₁ X}
    {P : Modules Λ₂ X} {m : M.X ⟶ N.X} {n : N.X ⟶ P.X}
    (h : a ≫ b = c) (s : Semilinear a M N m) (t : Semilinear b N P n) :
    Semilinear c M P (m ≫ n) where
  hom := s.hom ≫ (Mod.comap (coefficientMap a X)).map t.hom ≫
    (Mod.comapComp (coefficientMap a X) (coefficientMap b X)).inv.app P ≫
    (Mod.comapCongr (by rw [← h,
      coefficientMap_comp])).hom.app P
  underlying := by
    change s.hom.hom ≫ t.hom.hom ≫ 𝟙 _ ≫ 𝟙 _ = m ≫ n
    rw [s.underlying, t.underlying]
    simp only [Category.comp_id]

private theorem conjugate_symm_commShift
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.CommShift ℤ] [L₂.CommShift ℤ] [R₁.CommShift ℤ] [R₂.CommShift ℤ]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) [a₁.CommShift ℤ] [a₂.CommShift ℤ]
    (α : R₁ ⟶ R₂) [NatTrans.CommShift α ℤ] :
    NatTrans.CommShift ((conjugateEquiv a₁ a₂).symm α) ℤ := by
  dsimp [conjugateEquiv, mateEquiv, Iso.homCongr,
    TwoSquare.mk]
  infer_instance

private theorem shifted_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {F : C ⥤ D} {U : D ⥤ C} {G : D ⥤ E} {V : E ⥤ D}
    {H : C ⥤ E} {W : E ⥤ C}
    [U.CommShift ℤ] [V.CommShift ℤ] [W.CommShift ℤ]
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (ρ : V ⋙ U ≅ W)
    [NatTrans.CommShift ρ.hom ℤ]
    {X : C} {Y : D} {Z : E} (f : F.obj X ⟶ Y) (g : G.obj Y ⟶ Z)
    (h : H.obj X ⟶ Z)
    (hh : G.map f ≫ g = (Adjunction.leftAdjointCompIso a b c ρ).hom.app X ≫ h)
    (n : ℤ) :
    G.map ((Adjunction.LeftAdjointCommShift.iso a n).hom.app X ≫ f⟦n⟧') ≫
        (Adjunction.LeftAdjointCommShift.iso b n).hom.app Y ≫ g⟦n⟧' =
      (Adjunction.leftAdjointCompIso a b c ρ).hom.app (X⟦n⟧) ≫
        (Adjunction.LeftAdjointCommShift.iso c n).hom.app X ≫ h⟦n⟧' := by
  let := a.leftAdjointCommShift ℤ
  let := b.leftAdjointCommShift ℤ
  let := c.leftAdjointCommShift ℤ
  let : a.CommShift ℤ := a.commShift_of_rightAdjoint ℤ
  let : b.CommShift ℤ := b.commShift_of_rightAdjoint ℤ
  let : c.CommShift ℤ := c.commShift_of_rightAdjoint ℤ
  let α := Adjunction.leftAdjointCompIso a b c ρ
  have hc : NatTrans.CommShift α.hom ℤ :=
    conjugate_symm_commShift c (a.comp b) ρ.inv
  let := hc
  change G.map ((F.commShiftIso n).hom.app X ≫ f⟦n⟧') ≫
      (G.commShiftIso n).hom.app Y ≫ g⟦n⟧' =
    α.hom.app (X⟦n⟧) ≫ (H.commShiftIso n).hom.app X ≫ h⟦n⟧'
  rw [Functor.map_comp, Category.assoc]
  have hn := (G.commShiftIso n).hom.naturality f
  change G.map (f⟦n⟧') ≫ (G.commShiftIso n).hom.app Y =
    (G.commShiftIso n).hom.app (F.obj X) ≫ (G.map f)⟦n⟧' at hn
  rw [reassoc_of% hn, ← (shiftFunctor E n).map_comp, hh,
    (shiftFunctor E n).map_comp]
  have hα := NatTrans.shift_app_comm α.hom n X
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hα
  simpa only [α, Category.assoc] using congrArg (· ≫ h⟦n⟧') hα

/-- Normalized scalar arrows compose under the actual scalar associator, both before
and after shifting by two. No invertibility, diagram, trace or direct-image hypothesis
is involved.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2), scalar associativity.
(blueprint: lem-diagonal-scalar-endpoint-composition).

Proof: Faithfulness of the module forgetful functor identifies the composite of the
ordinary semilinear maps with the third. Exact degree-zero adjoint insertions compose
under the conjugate scalar associator. Cancel its inverse to obtain the first equation.
The conjugate formula in units and counits shows that this associator commutes with
shifts. Shift the first equation, use this compatibility and naturality of the second
scalar functor's shift comparison to obtain the second equation. -/
theorem scalarHom_comp (hcoeff : a ≫ b = c) {X : Scheme.{u}}
    {M₀ : Modules Λ₀ X} {M₁ : Modules Λ₁ X} {M₂ : Modules Λ₂ X}
    {m₀₁ : M₀.X ⟶ M₁.X} {m₁₂ : M₁.X ⟶ M₂.X} {m₀₂ : M₀.X ⟶ M₂.X}
    (s₀₁ : Semilinear a M₀ M₁ m₀₁) (s₁₂ : Semilinear b M₁ M₂ m₁₂)
    (s₀₂ : Semilinear c M₀ M₂ m₀₂) (hline : m₀₁ ≫ m₁₂ = m₀₂) :
    (scalarHom c s₀₂ =
      (scalarCompIso a b c hcoeff X).hom.app _ ≫
        (derivedScalars b X).map (scalarHom a s₀₁) ≫ scalarHom b s₁₂) ∧
    (scalarShiftHom c s₀₂ =
      (scalarCompIso a b c hcoeff X).hom.app _ ≫
        (derivedScalars b X).map (scalarShiftHom a s₀₁) ≫ scalarShiftHom b s₁₂) := by
  have hs : s₀₂.hom = s₀₁.hom ≫ (Mod.comap (coefficientMap a X)).map s₁₂.hom ≫
      ((Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
        Mod.comapCongr (by rw [← hcoeff, coefficientMap_comp])).hom.app M₂ := by
    apply Mod.hom_ext
    change s₀₂.hom.hom = s₀₁.hom.hom ≫ s₁₂.hom.hom ≫ 𝟙 _ ≫ 𝟙 _
    rw [s₀₂.underlying, s₀₁.underlying, s₁₂.underlying]
    simpa only [Category.comp_id] using hline.symm
  have hu := SheafExactDegreeZero.adjointInsertion_comp
    (Mod.comap (coefficientMap a X)) (Mod.comap (coefficientMap b X))
    (Mod.comap (coefficientMap c X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c X))
    ((Mod.comapComp (coefficientMap a X) (coefficientMap b X)).symm ≪≫
      Mod.comapCongr (by rw [← hcoeff, coefficientMap_comp]))
    s₀₁.hom s₁₂.hom s₀₂.hom hs
  unfold SheafExactDegreeZero.adjointInsertion at hu
  change (derivedScalars b X).map (scalarHom a s₀₁) ≫ scalarHom b s₁₂ =
    (scalarCompIso a b c hcoeff X).inv.app _ ≫ scalarHom c s₀₂ at hu
  have hfirst : scalarHom c s₀₂ =
      (scalarCompIso a b c hcoeff X).hom.app _ ≫
        (derivedScalars b X).map (scalarHom a s₀₁) ≫ scalarHom b s₁₂ := by
    rw [hu, Iso.hom_inv_id_app_assoc]
  refine ⟨hfirst, ?_⟩
  have : NatTrans.CommShift (scalarRestrictionCompIso a b c hcoeff X).symm.hom ℤ := by
    dsimp only [scalarRestrictionCompIso, Iso.symm_hom, Iso.symm_inv, Iso.trans_hom]
    infer_instance
  have hv := shifted_comp
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c X))
    (scalarRestrictionCompIso a b c hcoeff X).symm
    (scalarHom a s₀₁) (scalarHom b s₁₂) (scalarHom c s₀₂) hu (2 : ℤ)
  change (derivedScalars b X).map (scalarShiftHom a s₀₁) ≫ scalarShiftHom b s₁₂ =
    (scalarCompIso a b c hcoeff X).inv.app _ ≫ scalarShiftHom c s₀₂ at hv
  rw [hv, Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
