import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas
import Langlands.AbelianScheme.KernelBaseChange

/-! # Translations and base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (G : GroupScheme S)

/-- A translation on the base change, read through the pullback adjunction on points. -/
lemma baseChangePointsEquiv_translation (σ : Over.mk (𝟙 S') ⟶ ((baseChange b).obj G).X) :
    baseChangePointsEquiv b G ((baseChange b).obj G).X (translation ((baseChange b).obj G) σ) =
      ((Over.map b).map (Over.mkIdTerminal.from _) ≫
          baseChangePointsEquiv b G (Over.mk (𝟙 S')) σ) *
        baseChangePointsEquiv b G _ (𝟙 _) := by
  have h := points_translation ((baseChange b).obj G) σ _ (𝟙 _)
  rw [Category.id_comp] at h
  rw [h, map_mul, baseChangePointsEquiv_naturality]

/-- The restriction of a section over `S` to a section of the base change. -/
def baseChangeSection (σ : Over.mk (𝟙 S) ⟶ G.X) :
    Over.mk (𝟙 S') ⟶ ((baseChange b).obj G).X :=
  (baseChangePointsEquiv b G (Over.mk (𝟙 S'))).symm (Over.mkIdTerminal.from _ ≫ σ)

/-- Translation by a restricted section lies over translation by the section. -/
lemma translation_baseChangeSection (σ : Over.mk (𝟙 S) ⟶ G.X) :
    (translation ((baseChange b).obj G) (baseChangeSection b G σ)).left ≫
        pullback.fst G.X.hom b =
      pullback.fst G.X.hom b ≫ (translation G σ).left := by
  have h := baseChangePointsEquiv_translation b G (baseChangeSection b G σ)
  rw [baseChangeSection, MulEquiv.apply_symm_apply, ← Category.assoc,
    Over.mkIdTerminal.hom_ext (_ ≫ Over.mkIdTerminal.from _) (Over.mkIdTerminal.from _),
    ← points_translation] at h
  exact congrArg (fun k ↦ k.left) h

open Langlands.AlgebraicGeometry.Picard

/-- Restricting a translate to the base change gives the translate of the restriction. -/
def fibreTranslationIso (σ : Over.mk (𝟙 S) ⟶ G.X) (F : LineBundle G.X.left) :
    (LineBundle.pullback (pullback.fst G.X.hom b)).obj
        ((LineBundle.pullback (translation G σ).left).obj F) ≅
      (LineBundle.pullback (translation ((baseChange b).obj G)
          (baseChangeSection b G σ)).left).obj
        ((LineBundle.pullback (pullback.fst G.X.hom b)).obj F) :=
  LineBundle.pullbackCompEqIso _ _ (translation_baseChangeSection b G σ).symm F ≪≫
    (LineBundle.pullbackCompEqIso _ _ rfl F).symm

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Pulling back along a translation by a section preserves the geometric-fibre
Picard-zero condition. -/
lemma isGeometricallyPicardZero_pullback_translation {F : LineBundle A.X.left}
    (hF : IsGeometricallyPicardZero A F) (σ : Over.mk (𝟙 S) ⟶ A.X) :
    IsGeometricallyPicardZero A
      ((LineBundle.pullback (GroupScheme.translation A.toGrp σ).left).obj F) := by
  intro K _ _ s
  have h := hF K s
  obtain ⟨e⟩ := h (GroupScheme.baseChangeSection s A.toGrp σ)
  exact GroupScheme.isTranslationInvariant_of_iso _
    (e.symm ≪≫ (GroupScheme.fibreTranslationIso s A.toGrp σ F).symm) h

/-- Over an algebraically closed field, the geometric-fibre Picard-zero condition
gives translation invariance on the abelian scheme itself. -/
lemma isTranslationInvariant_of_isGeometricallyPicardZero (K : Type u) [Field K]
    [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K))) {F : LineBundle A.X.left}
    (hF : IsGeometricallyPicardZero A F) :
    GroupScheme.IsTranslationInvariant A.toGrp F := by
  intro σ
  obtain ⟨e⟩ := hF K (𝟙 _) (GroupScheme.baseChangeSection (𝟙 _) A.toGrp σ)
  exact ⟨LineBundle.isoOfPullbackIso (pullback.fst A.X.hom (𝟙 _))
    (GroupScheme.fibreTranslationIso (𝟙 _) A.toGrp σ F ≪≫ e)⟩

end Langlands.AbelianScheme
