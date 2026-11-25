/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Homology commutes with exact colimits

In an abelian category `C` in which colimits of shape `J` are exact, the homology functors of
cochain complexes commute with colimits of shape `J`
(`HomologicalComplex.preservesColimitsOfShape_homologyFunctor`).

We also record two facts on natural transformations and colimits:

- `CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone`: a natural transformation
  `τ : P ⟶ R` between
  functors preserving a colimit cocone `c` is an isomorphism at its point as soon as it is an
  isomorphism at all objects of the diagram;
- `CategoryTheory.Limits.isColimitMapCoconeOfNatTrans`: if `β : P ⟶ R` is an isomorphism at all
  objects of a cocone `c` and its diagram, then `P` maps `c` to a colimit cocone as soon as `R`
  does.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace HomologicalComplex

variable (C : Type*) [Category* C] [Abelian C] (J : Type w) [Category.{v} J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

set_option backward.isDefEq.respectTransparency false in
/-- Homology of short complexes commutes with exact colimits. -/
instance _root_.CategoryTheory.ShortComplex.preservesColimitsOfShape_homologyFunctor :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor C) := by
  let L := colim (J := J) (C := C)
  have : L.PreservesHomology := inferInstance
  refine ⟨fun {D} ↦ ?_⟩
  let S := (ShortComplex.functorEquivalence J C).inverse.obj D
  let c : Cocone D :=
    { pt := S.map L
      ι :=
        { app := fun i ↦ S.mapNatTrans (colim.ι i)
          naturality := by
            intro i j f
            apply ShortComplex.Hom.ext
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₁) f
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₂) f
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₃) f } }
  have hc : IsColimit c := ShortComplex.isColimitOfIsColimitπ c
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)
  apply preservesColimit_of_preserves_colimit_cocone hc
  let e : D ⋙ ShortComplex.homologyFunctor _ ≅ S.homology :=
    NatIso.ofComponents (fun i ↦ S.mapHomologyIso ((CategoryTheory.evaluation _ _).obj i)) (by
      intro i j f
      change ShortComplex.homologyMap
        (S.mapNatTrans ((CategoryTheory.evaluation _ _).map f)) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp)
  have h : IsColimit ((Cocone.precompose e.hom).obj (colimit.cocone S.homology)) :=
    (IsColimit.precomposeInvEquiv e.symm _).symm (colimit.isColimit _)
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (S.mapHomologyIso L).symm ?_
  intro i
  dsimp only [Functor.mapCocone, c, Cocone.precompose, colimit.cocone,
    Cocone.functoriality, NatTrans.comp_app, Iso.symm_hom, ShortComplex.homologyFunctor_map]
  rw [Category.assoc]
  change e.hom.app i ≫ colimit.ι S.homology i ≫ (S.mapHomologyIso L).inv =
    ShortComplex.homologyMap (S.mapNatTrans (colim.ι i))
  rw [ShortComplex.homologyMap_mapNatTrans]
  rfl

/-- The homology functors of cochain complexes commute with exact colimits. -/
instance preservesColimitsOfShape_homologyFunctor (p : ℤ) :
    PreservesColimitsOfShape J (homologyFunctor C (ComplexShape.up ℤ) p) := by
  let H := HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) p
  have : PreservesColimitsOfShape J H :=
    ⟨fun {D} ↦ ⟨fun {c} hc ↦ ⟨ShortComplex.isColimitOfIsColimitπ (H.mapCocone c)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.up ℤ) ((ComplexShape.up ℤ).prev p)) hc)
      (isColimitOfPreserves (HomologicalComplex.eval _ (ComplexShape.up ℤ) p) hc)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.up ℤ) ((ComplexShape.up ℤ).next p)) hc)⟩⟩⟩
  change PreservesColimitsOfShape J (H ⋙ ShortComplex.homologyFunctor _)
  infer_instance

end HomologicalComplex

namespace CategoryTheory

variable {C D J : Type*} [Category* C] [Category* D] [Category* J] {P R : C ⥤ D}

/-- A natural transformation `τ : P ⟶ R` between functors which map a cocone `c` to colimit
cocones is an isomorphism at the point of `c` if it is an isomorphism at all the objects of the
diagram. -/
lemma NatTrans.isIso_app_of_isColimit_mapCocone (τ : P ⟶ R) {K : J ⥤ C} (c : Cocone K)
    (hP : IsColimit (P.mapCocone c)) (hR : IsColimit (R.mapCocone c))
    (h : ∀ j, IsIso (τ.app (K.obj j))) : IsIso (τ.app c.pt) := by
  have : ∀ j, IsIso ((Functor.whiskerLeft K τ).app j) := h
  have : IsIso (Functor.whiskerLeft K τ) := NatIso.isIso_of_isIso_app _
  let e := hP.coconePointsIsoOfNatIso hR (asIso (Functor.whiskerLeft K τ))
  have : e.hom = τ.app c.pt := hP.hom_ext fun j ↦ by
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    simp
  rw [← this]
  infer_instance

/-- If `β : P ⟶ R` is an isomorphism at the point of a cocone `c` and at all the objects of its
diagram, then `P` maps `c` to a colimit cocone if `R` does. -/
noncomputable def Limits.isColimitMapCoconeOfNatTrans (β : P ⟶ R) {K : J ⥤ C} (c : Cocone K)
    (h : ∀ j, IsIso (β.app (K.obj j))) (hpt : IsIso (β.app c.pt))
    (hR : IsColimit (R.mapCocone c)) : IsColimit (P.mapCocone c) := by
  have : ∀ j, IsIso ((Functor.whiskerLeft K β).app j) := h
  have : IsIso (Functor.whiskerLeft K β) := NatIso.isIso_of_isIso_app _
  refine (IsColimit.equivOfNatIsoOfIso (asIso (Functor.whiskerLeft K β)) _ _ ?_).symm hR
  exact Cocone.ext (asIso (β.app c.pt)) fun j ↦ by simp

/-- If `β : P ⟶ R` is an isomorphism at the point of a cocone `c` and at all the objects of its
diagram, then `R` maps `c` to a colimit cocone if `P` does. -/
noncomputable def Limits.isColimitMapCoconeOfNatTrans' (β : P ⟶ R) {K : J ⥤ C} (c : Cocone K)
    (h : ∀ j, IsIso (β.app (K.obj j))) (hpt : IsIso (β.app c.pt))
    (hP : IsColimit (P.mapCocone c)) : IsColimit (R.mapCocone c) := by
  have : ∀ j, IsIso ((Functor.whiskerLeft K β).app j) := h
  have : IsIso (Functor.whiskerLeft K β) := NatIso.isIso_of_isIso_app _
  refine IsColimit.equivOfNatIsoOfIso (asIso (Functor.whiskerLeft K β)) _ _ ?_ hP
  exact Cocone.ext (asIso (β.app c.pt)) fun j ↦ by simp

end CategoryTheory
