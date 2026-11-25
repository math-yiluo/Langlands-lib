/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierPoleBoundaryPullback
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Pullback of the positive integral diagonal boundary

Source: the latest blueprint, diagonal coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.comp Ext.mapExactFunctor
  diagonalIntegralBoundary cartierIntegralSourceIso

private theorem exact_square
    {C D E F : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [Category E] [Abelian E] [Category F] [Abelian F]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D] [HasExt.{u + 1} E] [HasExt.{u + 1} F]
    [EnoughInjectives C]
    (V : C ⥤ E) (U : E ⥤ F) (H : C ⥤ D) (W : D ⥤ F)
    [V.Additive] [U.Additive] [H.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (s : V ⋙ U ≅ H ⋙ W) {X Y : C} (κ : Ext X Y 1) :
    (Ext.mk₀ (s.hom.app X)).comp
        ((κ.mapExactFunctor H).mapExactFunctor W) (zero_add 1) =
      ((κ.mapExactFunctor V).mapExactFunctor U).comp
        (Ext.mk₀ (s.hom.app Y)) (add_zero 1) := by
  have h₁ := Ext.mapExactFunctor_mapExactFunctor_of_iso V U (V ⋙ U) (Iso.refl _) κ
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    Ext.mk₀_id_comp, Ext.comp_mk₀_id] at h₁
  have h₂ := Ext.mapExactFunctor_mapExactFunctor_of_iso H W (V ⋙ U) s κ
  rw [h₂, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_app, Ext.mk₀_id_comp, h₁]

private theorem transport_square
    {C D E F : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [Category E] [Abelian E] [Category F] [Abelian F]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D] [HasExt.{u + 1} E] [HasExt.{u + 1} F]
    [EnoughInjectives C]
    (V : C ⥤ E) (U : E ⥤ F) (H : C ⥤ D) (W : D ⥤ F)
    [V.Additive] [U.Additive] [H.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (s : V ⋙ U ≅ H ⋙ W) {X Y : C} {X' Y' : D} {P : E} {Q : F}
    (a : V.obj X ≅ P) (b : W.obj X' ≅ Q)
    (e : H.obj X ⟶ X') (l : H.obj Y ⟶ Y') (χ : U.obj P ⟶ Q)
    (hχ : U.map a.hom ≫ χ = s.hom.app X ≫ W.map e ≫ b.hom)
    (κ : Ext X Y 1) (κ' : Ext X' Y' 1)
    (hκ : (Ext.mk₀ e).comp κ' (zero_add 1) =
      (κ.mapExactFunctor H).comp (Ext.mk₀ l) (add_zero 1)) :
    (Ext.mk₀ χ).comp
        ((Ext.mk₀ b.inv).comp (κ'.mapExactFunctor W) (zero_add 1)) (zero_add 1) =
      (((Ext.mk₀ a.inv).comp (κ.mapExactFunctor V) (zero_add 1)).mapExactFunctor U).comp
        (Ext.mk₀ (s.hom.app Y ≫ W.map l)) (add_zero 1) := by
  have h := congrArg
    (fun z : Ext (H.obj X) Y' 1 ↦
      (Ext.mk₀ (s.hom.app X)).comp (z.mapExactFunctor W) (zero_add 1)) hκ
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at h
  rw [← Ext.comp_assoc_of_third_deg_zero,
    exact_square V U H W s κ, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀] at h
  simp only [Ext.mk₀_comp_mk₀_assoc] at h
  have h' := congrArg
    (fun z : Ext (U.obj (V.obj X)) (W.obj Y') 1 ↦
      (Ext.mk₀ (U.map a.inv)).comp z (zero_add 1)) h
  have hχ' : U.map a.inv ≫ s.hom.app X ≫ W.map e = χ ≫ b.inv := by
    have hh := congrArg (fun f ↦ U.map a.inv ≫ f ≫ b.inv) hχ
    simp only [← Category.assoc, ← Functor.map_comp, a.inv_hom_id] at hh
    rw [U.map_id P, Category.id_comp] at hh
    simpa only [Category.assoc, b.hom_inv_id, Category.comp_id] using hh.symm
  simpa only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, hχ'] using h'

/-- The supported integral endpoint obtained by transporting the canonical etale
closed exchange through the two fixed site comparisons.
Source: blueprint coefficient proof (3), Cartier extension pullback
(blueprint: lem-diagonal-integral-boundary-pullback). -/
def diagonalBoundarySource {Y Y' : Scheme.{u}}
    (v : diagonalSurface Y' ⟶ diagonalSurface Y)
    (w : ProjectiveLine Y' ⟶ ProjectiveLine Y)
    (sq : CommSq w (diagonalImmersion Y') (diagonalImmersion Y) v) :
    (upperStar Ab.{u + 1} v).obj (diagonalIntegralSource Y) ⟶
      diagonalIntegralSource Y' :=
  (upperStar Ab.{u + 1} v).map (cartierIntegralSourceIso (diagonalImmersion Y)).inv ≫
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} v).hom.app _ ≫
    (comparisonUpperStar Ab.{u + 1} (diagonalSurface Y')).map
      (Etale.relativeExtensionExchange (diagonalImmersion Y) (diagonalImmersion Y') v w sq) ≫
    (cartierIntegralSourceIso (diagonalImmersion Y')).hom

/-- The units endpoint is the canonical units pullback through the comparison square.
Source: blueprint coefficient proof (3), units map
(blueprint: lem-diagonal-integral-boundary-pullback). -/
def diagonalBoundaryUnits {Y Y' : Scheme.{u}}
    (v : diagonalSurface Y' ⟶ diagonalSurface Y) :
    (upperStar Ab.{u + 1} v).obj (diagonalComparisonUnits Y) ⟶
      diagonalComparisonUnits Y' :=
  (comparisonUpperStarCompUpperStarIso Ab.{u + 1} v).hom.app _ ≫
    (comparisonUpperStar Ab.{u + 1} (diagonalSurface Y')).map
      (Scheme.upperStarGmSheafToGmSheaf v)

/-- Pullback of the positive integral boundary, before reduction or completion.

Source: blueprint coefficient changes (3); Cartier pole-extension naturality.
(blueprint: lem-diagonal-integral-boundary-pullback).

Proof: the closed source exchange is invertible by finite base change. The
Cartier pole-boundary pullback equation is transported by exact site comparison.
The comparison square commutes on Ext by functoriality. Conjugating its source
by cartierIntegralSourceIso gives diagonalBoundarySource. The positive boundary
is the negative of the transported pole boundary on both schemes, so additivity
preserves its equation. The proof works for empty schemes and arbitrary base maps. -/
theorem diagonalIntegralBoundary_pullback {Y Y' : Scheme.{u}}
    (v : diagonalSurface Y' ⟶ diagonalSurface Y)
    (w : ProjectiveLine Y' ⟶ ProjectiveLine Y)
    (sq : IsPullback w (diagonalImmersion Y') (diagonalImmersion Y) v) :
    IsIso (diagonalBoundarySource v w sq.toCommSq) ∧
      (Ext.mk₀ (diagonalBoundarySource v w sq.toCommSq)).comp
          (diagonalIntegralBoundary Y') (zero_add 1) =
        ((diagonalIntegralBoundary Y).mapExactFunctor (upperStar Ab.{u + 1} v)).comp
          (Ext.mk₀ (diagonalBoundaryUnits v)) (add_zero 1) := by
  have he : IsIso (Etale.relativeExtensionExchange
      (diagonalImmersion Y) (diagonalImmersion Y') v w sq.toCommSq) := by
    have := Etale.isIso_baseChangeMap_of_isFinite Ab.{u + 1} sq
    unfold Etale.relativeExtensionExchange
    infer_instance
  refine ⟨?_, ?_⟩
  · unfold diagonalBoundarySource
    infer_instance
  · have h := transport_square
      (comparisonUpperStar Ab.{u + 1} (diagonalSurface Y)) (upperStar Ab.{u + 1} v)
      (Etale.upperStar Ab.{u + 1} v)
      (comparisonUpperStar Ab.{u + 1} (diagonalSurface Y'))
      (comparisonUpperStarCompUpperStarIso Ab.{u + 1} v)
      (cartierIntegralSourceIso (diagonalImmersion Y))
      (cartierIntegralSourceIso (diagonalImmersion Y'))
      (Etale.relativeExtensionExchange (diagonalImmersion Y) (diagonalImmersion Y') v w
        sq.toCommSq)
      (Scheme.upperStarGmSheafToGmSheaf v)
      (diagonalBoundarySource v w sq.toCommSq)
      (by
        dsimp only [diagonalBoundarySource]
        rw [← Functor.map_comp_assoc, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.id_comp])
      (Etale.cartierPoleBoundary (diagonalImmersion Y) (diagonalImmersion_cartier Y))
      (Etale.cartierPoleBoundary (diagonalImmersion Y') (diagonalImmersion_cartier Y'))
      (Etale.cartierPoleBoundary_pullback (diagonalImmersion Y)
        (diagonalImmersion_cartier Y) (diagonalImmersion Y')
        (diagonalImmersion_cartier Y') v w sq)
    have map_neg_boundary : ∀ z : Ext (diagonalIntegralSource Y)
        (diagonalComparisonUnits Y) 1,
        (-z).mapExactFunctor (upperStar Ab.{u + 1} v) =
          -(z.mapExactFunctor (upperStar Ab.{u + 1} v)) := fun z ↦
      map_neg ((upperStar Ab.{u + 1} v).mapExtAddHom _ _ 1) z
    simpa only [diagonalIntegralBoundary, transportBoundarySource,
      diagonalBoundaryUnits, Ext.comp_neg, map_neg_boundary, Ext.neg_comp] using
      congrArg Neg.neg h

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
