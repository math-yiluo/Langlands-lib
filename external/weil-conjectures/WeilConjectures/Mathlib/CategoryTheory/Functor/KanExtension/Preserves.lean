/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import WeilConjectures.Mathlib.CategoryTheory.NatIso

/-!

# Exactness of left Kan extension along a fully faithful functor with empty fibers

Let `L : C ⥤ D` be a fully faithful functor such that every object `Y` of `D` is either in
the essential image of `L` or has empty comma category `CostructuredArrow L Y`. Then left
Kan extension along `L` is computed by

* `(L.lan.obj F).obj (L.obj X) ≅ F.obj X` in the first case, since the unit of the Kan
  extension is an isomorphism for fully faithful `L`;
* an initial object in the second case, being a colimit over an empty category.

In particular, if the initial object of `H` is a zero object, left Kan extension along `L`
preserves every limit that exists in `H`
(`CategoryTheory.Functor.preservesLimitsOfShape_lan_of_essImage_or_isEmpty`). This is the
abstract form of the statement that extension by zero along an open immersion is left
exact.

## Main results

- `CategoryTheory.Limits.preservesLimitsOfShape_of_isTerminal_obj`: a functor all of whose
  values are terminal preserves all limits.
- `CategoryTheory.Functor.isInitialLanObjObj`: the left Kan extension is initial at an
  object with empty comma category.
- `CategoryTheory.Functor.evaluationObjIsoLanCompEvaluation`: for fully faithful `L`,
  evaluating the left Kan extension at `L.obj X` is evaluation at `X`.
- `CategoryTheory.Functor.preservesLimitsOfShape_lan_of_essImage_or_isEmpty`: the exactness
  statement.
- `CategoryTheory.Functor.isIso_lanAdjunction_counit_app_of_isZero`: the counit of the Kan
  extension adjunction is invertible at a functor vanishing at the objects with empty comma
  category.
- `CategoryTheory.Functor.lanCompEvaluationIsoColimOfFinal`: if `s : K ⥤ CostructuredArrow L Y`
  is final, evaluating the left Kan extension at `Y` is the colimit over `K`.
- `CategoryTheory.Functor.preservesFiniteLimits_lan_of_final`: left Kan extension is left exact
  if every comma category `CostructuredArrow L Y` receives a final functor from a discrete
  category and coproducts are exact (`AB4`). This is the abstract form of the exactness of
  extension by zero along an étale morphism, which is pointwise a direct sum.

-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

namespace Limits

variable {C : Type u₁} [Category.{v₁} C] {H : Type u₂} [Category.{v₂} H]

/-- A functor whose values are all terminal objects preserves all limits: both the lift and
its uniqueness are supplied by terminality of the values. -/
lemma preservesLimitsOfShape_of_isTerminal_obj {F : C ⥤ H} (hF : ∀ X, IsTerminal (F.obj X))
    (J : Type*) [Category* J] : PreservesLimitsOfShape J F where
  preservesLimit := ⟨fun {c} _ ↦ ⟨{
    lift s := (hF c.pt).from s.pt
    fac _ _ := (hF _).hom_ext _ _
    uniq _ _ _ := (hF _).hom_ext _ _ }⟩⟩

end Limits

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H] (L : C ⥤ D)

section

variable [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F]

/-- If the comma category `CostructuredArrow L Y` is empty, the left Kan extension of any
functor along `L` is initial at `Y`: it is a colimit over an empty category. -/
noncomputable def isInitialLanObjObj (F : C ⥤ H) {Y : D} (hY : IsEmpty (CostructuredArrow L Y)) :
    IsInitial ((L.lan.obj F).obj Y) :=
  have := hY
  isColimitEquivIsInitialOfIsEmpty _ _ (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F Y)

variable [L.Full] [L.Faithful]

/-- For a fully faithful `L`, evaluating the left Kan extension along `L` at `L.obj X` is
evaluation at `X`; the isomorphism is the unit of the Kan extension. -/
@[simps! hom_app]
noncomputable def evaluationObjIsoLanCompEvaluation (X : C) :
    (evaluation C H).obj X ≅ L.lan ⋙ (evaluation D H).obj (L.obj X) :=
  NatIso.ofComponents (fun F ↦ asIso ((L.lanUnit.app F).app X))
    fun {_ _} φ ↦ congr_app (L.lanUnit.naturality φ) X

end

/-- Left Kan extension along a fully faithful functor `L` preserves every limit that exists
in the target category, provided every object of `D` is either in the essential image of `L`
or has empty comma category, and the initial object of `H` is a zero object.

This is the abstract form of the left exactness of extension by zero along an open
immersion: on the presheaf level, the extension of `F` is `F` on objects lying over the open
subobject and zero elsewhere. -/
lemma preservesLimitsOfShape_lan_of_essImage_or_isEmpty [L.Full] [L.Faithful] [HasZeroMorphisms H]
    [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F]
    (hL : ∀ Y : D, (∃ X : C, Nonempty (L.obj X ≅ Y)) ∨ IsEmpty (CostructuredArrow L Y))
    (J : Type*) [Category* J] [HasLimitsOfShape J H] :
    PreservesLimitsOfShape J (L.lan : (C ⥤ H) ⥤ D ⥤ H) := by
  refine preservesLimitsOfShape_of_evaluation _ _ fun Y ↦ ?_
  rcases hL Y with ⟨X, ⟨e⟩⟩ | hY
  · exact preservesLimitsOfShape_of_natIso
      (L.evaluationObjIsoLanCompEvaluation X ≪≫ isoWhiskerLeft L.lan ((evaluation D H).mapIso e))
  · exact preservesLimitsOfShape_of_isTerminal_obj
      (fun F ↦ (L.isInitialLanObjObj F hY).isZero.isTerminal) J

/-- Left Kan extension along a fully faithful functor with empty fibers is left exact.
See `CategoryTheory.Functor.preservesLimitsOfShape_lan_of_essImage_or_isEmpty`. -/
lemma preservesFiniteLimits_lan_of_essImage_or_isEmpty [L.Full] [L.Faithful] [HasZeroMorphisms H]
    [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F] [HasFiniteLimits H]
    (hL : ∀ Y : D, (∃ X : C, Nonempty (L.obj X ≅ Y)) ∨ IsEmpty (CostructuredArrow L Y)) :
    PreservesFiniteLimits (L.lan : (C ⥤ H) ⥤ D ⥤ H) where
  preservesFiniteLimits _ := L.preservesLimitsOfShape_lan_of_essImage_or_isEmpty hL _

/-- Let `L` be fully faithful such that every object of `D` is in the essential image of `L` or
has empty comma category. The counit `L.lan (L ⋙ G) ⟶ G` of the Kan extension adjunction is
invertible at a functor `G` vanishing at the objects with empty comma category: it is the
inverse of the invertible unit on the essential image, and a morphism of zero objects
elsewhere. -/
lemma isIso_lanAdjunction_counit_app_of_isZero [L.Full] [L.Faithful] [HasZeroMorphisms H]
    [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F]
    (hL : ∀ Y : D, (∃ X : C, Nonempty (L.obj X ≅ Y)) ∨ IsEmpty (CostructuredArrow L Y))
    (G : D ⥤ H) (hG : ∀ Y : D, IsEmpty (CostructuredArrow L Y) → IsZero (G.obj Y)) :
    IsIso ((L.lanAdjunction H).counit.app G) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  rcases hL Y with ⟨X, ⟨e⟩⟩ | hY
  · have : IsIso (((L.lanAdjunction H).counit.app G).app (L.obj X)) := by
      rw [← IsIso.inv_eq_of_hom_inv_id (L.lanUnit_app_app_lanAdjunction_counit_app_app G X)]
      infer_instance
    exact NatTrans.isIso_app_of_iso _ e.symm
  · exact ⟨⟨(hG Y hY).to_ _, (L.isInitialLanObjObj _ hY).isZero.eq_of_src _ _,
      (hG Y hY).eq_of_src _ _⟩⟩

section Final

variable [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F]

/-- If `s : K ⥤ CostructuredArrow L Y` is final, evaluating the left Kan extension along `L` at
`Y` is the colimit over `K` of the composition of `s` with the projection: the pointwise left
Kan extension is a colimit over `CostructuredArrow L Y`, which may be computed along `s`. -/
noncomputable def lanCompEvaluationIsoColimOfFinal {K : Type*} [Category* K] {Y : D}
    (s : K ⥤ CostructuredArrow L Y) [s.Final] [HasColimitsOfShape K H] :
    L.lan ⋙ (evaluation D H).obj Y ≅
      (whiskeringLeft _ _ H).obj (s ⋙ CostructuredArrow.proj L Y) ⋙ colim :=
  NatIso.ofComponents (fun F ↦
    ((Final.isColimitWhiskerEquiv s _).symm
      (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F Y)).coconePointUniqueUpToIso
      (colimit.isColimit _))
    (fun {F₁ F₂} φ ↦ by
      apply ((Final.isColimitWhiskerEquiv s _).symm
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F₁ Y)).hom_ext
      intro k
      have h₁ := fun (F : C ⥤ H) ↦ IsColimit.comp_coconePointUniqueUpToIso_hom
        ((Final.isColimitWhiskerEquiv s _).symm
          (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F Y)) (colimit.isColimit _) k
      have h₂ := congr_app (L.lanUnit.naturality φ) (s.obj k).left
      dsimp only [Cocone.whisker_ι, NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
        whiskeringLeft_obj_obj, colim_obj, colim_map, evaluation_obj_map,
        Functor.whiskerLeft_app] at h₁ h₂ ⊢
      erw [reassoc_of% (h₁ F₁), ι_colimMap]
      have h₃ := h₁ F₂
      simp only [colimit.cocone_ι] at h₃
      erw [← h₃]
      have key : (L.leftKanExtensionUnit F₁).app (s.obj k).left ≫
          (L.lan.map φ).app (L.obj (s.obj k).left) =
            φ.app (s.obj k).left ≫ (L.leftKanExtensionUnit F₂).app (s.obj k).left := h₂.symm
      have nat := (L.lan.map φ).naturality (s.obj k).hom
      erw [Category.assoc, reassoc_of% nat]
      exact ((Category.assoc _ _ _).symm.trans ((key =≫ _).trans (Category.assoc _ _ _))).trans
        (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm))

/-- Left Kan extension along `L` is left exact if every comma category `CostructuredArrow L Y`
receives a final functor from a discrete category `Discrete ι` and coproducts indexed by such
`ι` are exact (`AB4`): evaluated at `Y`, the left Kan extension is then a coproduct of
evaluations, `(L.lan.obj F).obj Y ≅ ∐ᵢ F.obj (s i).left`.

This is the abstract form of the left exactness of extension by zero along an étale
morphism: on the presheaf level, the extension of `F` is `⨁ₛ F(V, s)` over the lifts `s`. -/
lemma preservesFiniteLimits_lan_of_final [HasFiniteLimits H] [HasCoproducts.{w} H]
    [AB4OfSize.{w} H]
    (hL : ∀ Y : D, ∃ (ι : Type w) (s : Discrete ι ⥤ CostructuredArrow L Y), s.Final) :
    PreservesFiniteLimits (L.lan : (C ⥤ H) ⥤ D ⥤ H) where
  preservesFiniteLimits J _ _ := by
    refine preservesLimitsOfShape_of_evaluation _ _ fun Y ↦ ?_
    obtain ⟨ι, s, _⟩ := hL Y
    exact preservesLimitsOfShape_of_natIso (L.lanCompEvaluationIsoColimOfFinal s).symm

end Final

end Functor

end CategoryTheory
