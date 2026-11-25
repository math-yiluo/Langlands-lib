/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import WeilConjectures.AlgebraicGeometry.OpenModuleImageSectionRestriction

/-! Sectionwise gluing and its assembly for an arbitrary open union. -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Mathlib's two-open sheaf pullback, with named union and intersection opens. -/
private theorem ordinary_gluing_pullback
    (X : Scheme.{u}) (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (A B S D : X.Opens) (hs : S = A ⊔ B) (hi : D = A ⊓ B) :
    IsPullback
      ((forget AddCommGrpCat).map (M.val.presheaf.map
        (homOfLE (show A ≤ S by rw [hs]; exact le_sup_left)).op))
      ((forget AddCommGrpCat).map (M.val.presheaf.map
        (homOfLE (show B ≤ S by rw [hs]; exact le_sup_right)).op))
      ((forget AddCommGrpCat).map (M.val.presheaf.map
        (homOfLE (show D ≤ A by rw [hi]; exact inf_le_left)).op))
      ((forget AddCommGrpCat).map (M.val.presheaf.map
        (homOfLE (show D ≤ B by rw [hi]; exact inf_le_right)).op)) := by
  subst S D
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.val.presheaf, M.isSheaf⟩
  exact (IsPullback.of_isLimit (F.isLimitPullbackCone A B)).map (forget AddCommGrpCat)

/-- Sectionwise amalgamation of direct-image restrictions.

Source: Stacks Project, Tags 01EB and 08BV.
(blueprint: lem-pc-open-union-module-image-pullback-core-sectionwise)
The two-open sheaf axiom, after the section-restriction comparison, gives the
existence and uniqueness of the amalgamated section at each test open. -/
theorem schemeOpenUnionModuleImage_sectionwise_gluing
    (X : Scheme.{u}) (U V : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    ∀ T : X.Opens,
      ∀ b : ((schemeOpenModuleImage X U).obj M).val.obj (.op T),
      ∀ c : ((schemeOpenModuleImage X V).obj M).val.obj (.op T),
      (((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M).val.app (.op T) b =
        ((schemeOpenModuleImageRestriction X
          (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M).val.app (.op T) c) →
      ∃! a : ((schemeOpenModuleImage X (U ⊔ V)).obj M).val.obj (.op T),
        ((schemeOpenModuleImageRestriction X
          (homOfLE (le_sup_left : U ≤ U ⊔ V))).app M).val.app (.op T) a = b ∧
        ((schemeOpenModuleImageRestriction X
          (homOfLE (le_sup_right : V ≤ U ⊔ V))).app M).val.app (.op T) a = c := by
  classical
  intro T b c hbc
  let P (A : X.Opens) := A.ι ''ᵁ (A.ι ⁻¹ᵁ T)
  let e (A : X.Opens) :
      ((schemeOpenModuleImage X A).obj M).val.obj (.op T) ≃ M.val.obj (.op (P A)) :=
    ((SheafOfModules.evaluation (moduleRings X.toRingedSpace) (.op T) ⋙ forget _).mapIso
      ((Scheme.Modules.pushforward A.ι).mapIso
        ((Scheme.Modules.overFunctorEquiv A).app M))).toEquiv
  have er {W A : X.Opens} (i : W ⟶ A)
      (a : ((schemeOpenModuleImage X A).obj M).val.obj (.op T)) :
      e W (((schemeOpenModuleImageRestriction X i).app M).val.app (.op T) a) =
        M.val.map (homOfLE (show P W ≤ P A by
          dsimp [P]
          simp only [Scheme.Hom.image_preimage_eq_opensRange_inf,
            Scheme.Opens.opensRange_ι]
          exact inf_le_inf_right T (leOfHom i))).op (e A a) :=
    schemeOpenModuleImage_section_restriction X i M T a
  have hs : P (U ⊔ V) = P U ⊔ P V := by
    simp only [P, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_sup_right]
  have hi : P (U ⊓ V) = P U ⊓ P V := by
    simp only [P, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    simp only [inf_assoc, inf_left_comm, inf_idem]
  have hp := ordinary_gluing_pullback X M (P U) (P V) (P (U ⊔ V)) (P (U ⊓ V)) hs hi
  have hc : M.val.map (homOfLE (show P (U ⊓ V) ≤ P U by rw [hi]; exact inf_le_left)).op
      (e U b) =
      M.val.map (homOfLE (show P (U ⊓ V) ≤ P V by rw [hi]; exact inf_le_right)).op
        (e V c) := by
    rw [← er (homOfLE inf_le_left), ← er (homOfLE inf_le_right), hbc]
  obtain ⟨a, ha₁, ha₂⟩ := Types.exists_of_isPullback hp (e U b) (e V c) hc
  refine ⟨(e (U ⊔ V)).symm a, ⟨?_, ?_⟩, ?_⟩
  · apply (e U).injective
    rw [er, Equiv.apply_symm_apply]
    exact ha₁
  · apply (e V).injective
    rw [er, Equiv.apply_symm_apply]
    exact ha₂
  · intro a' ha'
    apply (e (U ⊔ V)).injective
    rw [Equiv.apply_symm_apply]
    apply Types.ext_of_isPullback hp
    · exact (er (homOfLE (le_sup_left : U ≤ U ⊔ V)) a').symm.trans
        ((congrArg (e U) ha'.1).trans ha₁.symm)
    · exact (er (homOfLE (le_sup_right : V ≤ U ⊔ V)) a').symm.trans
        ((congrArg (e V) ha'.2).trans ha₂.symm)

/-- Transported restrictions compose, by the section-restriction comparison. -/
private theorem imageRestriction_comp
    (X : Scheme.{u}) {W A B : X.Opens} (i : W ⟶ A) (j : A ⟶ B)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (schemeOpenModuleImageRestriction X j).app M ≫
      (schemeOpenModuleImageRestriction X i).app M =
        (schemeOpenModuleImageRestriction X (i ≫ j)).app M := by
  ext T a
  obtain ⟨T⟩ := T
  let e := (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (.op T)).mapIso
    ((Scheme.Modules.pushforward W.ι).mapIso ((Scheme.Modules.overFunctorEquiv W).app M))
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  change (((Scheme.Modules.pushforward W.ι).map
      ((Scheme.Modules.overFunctorEquiv W).hom.app M)).val.app (.op T)) _ =
    (((Scheme.Modules.pushforward W.ι).map
      ((Scheme.Modules.overFunctorEquiv W).hom.app M)).val.app (.op T)) _
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [schemeOpenModuleImage_section_restriction,
    schemeOpenModuleImage_section_restriction, schemeOpenModuleImage_section_restriction,
    ← M.val.map_comp_apply]
  congr 1

/-- Sectionwise amalgamations assemble into the categorical pullback.

Source: Stacks Project, Tags 01EB and 08BV.
(blueprint: lem-pc-open-union-module-image-pullback-core-assembly)
The sectionwise existence and uniqueness data is natural in the test open and
therefore assembles to a morphism of module sheaves.  Its two composites are
the prescribed restrictions, and sectionwise uniqueness gives the pullback
universal property. -/
theorem schemeOpenUnionModuleImage_isPullback_of_sectionwise
    (X : Scheme.{u}) (U V : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (h : ∀ T : X.Opens,
      ∀ b : ((schemeOpenModuleImage X U).obj M).val.obj (.op T),
      ∀ c : ((schemeOpenModuleImage X V).obj M).val.obj (.op T),
      (((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M).val.app (.op T) b =
        ((schemeOpenModuleImageRestriction X
          (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M).val.app (.op T) c) →
      ∃! a : ((schemeOpenModuleImage X (U ⊔ V)).obj M).val.obj (.op T),
        ((schemeOpenModuleImageRestriction X
          (homOfLE (le_sup_left : U ≤ U ⊔ V))).app M).val.app (.op T) a = b ∧
        ((schemeOpenModuleImageRestriction X
          (homOfLE (le_sup_right : V ≤ U ⊔ V))).app M).val.app (.op T) a = c) :
    IsPullback
      ((schemeOpenModuleImageRestriction X
        (homOfLE (le_sup_left : U ≤ U ⊔ V))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (le_sup_right : V ≤ U ⊔ V))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M) := by
  classical
  let f := (schemeOpenModuleImageRestriction X
    (homOfLE (le_sup_left : U ≤ U ⊔ V))).app M
  let g := (schemeOpenModuleImageRestriction X
    (homOfLE (le_sup_right : V ≤ U ⊔ V))).app M
  let i := (schemeOpenModuleImageRestriction X
    (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M
  let j := (schemeOpenModuleImageRestriction X
    (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M
  have w : f ≫ i = g ≫ j := by
    dsimp [f, g, i, j]
    rw [imageRestriction_comp, imageRestriction_comp]
    congr 2
  have ht (T : X.Opensᵒᵖ) :
      IsPullback (f.val.app T) (g.val.app T) (i.val.app T) (j.val.app T) := by
    apply IsPullback.of_map_of_faithful (forget _)
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · exact congrArg (fun k ↦ (forget _).map (k.val.app T)) w
    · intro a a' haa
      obtain ⟨z, hz, hu⟩ := h T.unop (f.val.app T a) (g.val.app T a)
        (ConcreteCategory.congr_hom
          (congrArg (fun k ↦ k.val.app T) w) a)
      exact (hu a ⟨rfl, rfl⟩).trans (hu a' ⟨haa.1.symm, haa.2.symm⟩).symm
    · intro b c hbc
      obtain ⟨a, ha, _⟩ := h T.unop b c hbc
      exact ⟨a, ha⟩
  apply IsPullback.of_map_of_faithful (SheafOfModules.forget.{u} (moduleRings X.toRingedSpace))
  apply IsPullback.of_isLimit' ⟨congrArg (fun k ↦ k.val) w⟩
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro T
  exact (PullbackCone.isLimitMapConeEquiv _ _).symm (ht T).isLimit

end AlgebraicGeometry
