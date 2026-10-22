import Langlands.Geometry.EtaleAutomorphism
import Langlands.Geometry.EtaleDerivedSections
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Restriction along an étale morphism

Composition of structure morphisms gives a continuous and cocontinuous functor
between small étale sites. Its precomposition functor restricts étale sheaves.
-/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleAutomorphism

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- Composition of an étale structure morphism with `f`. -/
abbrev siteMap : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (inferInstance : Etale f)

instance siteMap_preservesPullbacks : PreservesLimitsOfShape WalkingCospan (siteMap f) := by
  let FX := MorphismProperty.Over.forget (@Etale) ⊤ X ⋙ Over.forget X
  have : PreservesLimitsOfShape WalkingCospan (siteMap f ⋙ FX) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (MorphismProperty.Over.forget (@Etale) ⊤ Y ⋙ Over.forget Y))
  have : ReflectsLimitsOfShape WalkingCospan FX :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves (siteMap f) FX

/-- Composition carries covering families to covering families and preserves
pairwise pullbacks. -/
instance siteMap_isContinuous :
    (siteMap f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology := by
  have : PreservesLimitsOfShape WalkingCospan
      (MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale f)) :=
    siteMap_preservesPullbacks f
  change Functor.IsContinuous
    (MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale f))
    (Scheme.smallGrothendieckTopology (Q := @Etale) (@Etale) Y)
    (Scheme.smallGrothendieckTopology (Q := @Etale) (@Etale) X)
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology Y le_rfl,
    Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X le_rfl,
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  intro U S hS
  have hforget :
      MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale f) ⋙
          MorphismProperty.Over.forget (@Etale) ⊤ X ⋙ Over.forget X =
        MorphismProperty.Over.forget (@Etale) ⊤ Y ⋙ Over.forget Y := by
    fapply CategoryTheory.Functor.ext
    · intro U
      rfl
    · intro U V a
      simp
  simpa only [Precoverage.over, ← Precoverage.comap_comp, hforget] using hS

/-- A covering arrow into an object over `Y` has an étale source over `Y`. -/
instance siteMap_isCocontinuous :
    (siteMap f).IsCocontinuous Y.smallEtaleTopology X.smallEtaleTopology where
  cover_lift {U S} hS := by
    rw [mem_smallEtaleTopology_iff] at hS ⊢
    intro x
    obtain ⟨V, a, v, ha, hv⟩ := hS x
    let V' : Y.Etale := MorphismProperty.Over.mk ⊤ (a.left ≫ U.hom) inferInstance
    let a' : V' ⟶ U := MorphismProperty.Over.homMk a.left
    let e : (siteMap f).obj V' ⟶ V :=
      MorphismProperty.Over.homMk (𝟙 V.left) (by
        dsimp [V']
        rw [Category.id_comp, Category.assoc]
        exact a.w.symm)
    refine ⟨V', a', v, ?_, hv⟩
    have hcomp : (siteMap f).map a' = e ≫ a := by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.id_comp a.left).symm
    change S ((siteMap f).map a')
    rw [hcomp]
    exact S.downward_closed ha e

variable (A : Type*) [Category A]

/-- Restriction of sheaves along an étale morphism: on an étale `Y`-scheme,
evaluate the original sheaf on its composite structure morphism to `X`. -/
def restriction : Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  (siteMap f).sheafPushforwardContinuous A Y.smallEtaleTopology X.smallEtaleTopology

/-- Successive restrictions identify with restriction along the composite. -/
def restrictionComp {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g] :
    restriction f A ⋙ restriction g A ≅ restriction (g ≫ f) A :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight
      (NatIso.op (MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
        (inferInstance : Etale f))) F.obj))
    (fun {F G} φ => by
      apply Sheaf.hom_ext
      ext U
      exact (φ.hom.naturality _).symm)

/-- Restriction along the identity identifies with the identity functor. -/
def restrictionId :
    restriction (𝟙 X) A ≅ 𝟭 (Sheaf X.smallEtaleTopology A) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight
      (NatIso.op (MorphismProperty.Over.mapId ⊤ X)).symm F.obj ≪≫ F.obj.leftUnitor))
    (fun {F G} φ => by
      apply Sheaf.hom_ext
      ext U
      dsimp
      simp only [Category.comp_id]
      exact (φ.hom.naturality _).symm)

/-- Restrict a section over the terminal object of the small étale site. -/
def terminalSectionsMap :
    (sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale)) ⟶
      restriction f A ⋙
        (sheafSections Y.smallEtaleTopology A).obj (op (⊤_ Y.Etale)) where
  app F := F.obj.map (terminal.from ((siteMap f).obj (⊤_ Y.Etale))).op
  naturality _ _ φ := (φ.hom.naturality _).symm

/-- The maps on terminal-object sections respect composition of morphisms. -/
theorem terminalSectionsMap_comp {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g]
    (F : Sheaf X.smallEtaleTopology A) :
    (terminalSectionsMap f A).app F ≫
        (terminalSectionsMap g A).app ((restriction f A).obj F) ≫
        ((sheafSections Z.smallEtaleTopology A).obj (op (⊤_ Z.Etale))).map
          ((restrictionComp f A g).hom.app F) =
      (terminalSectionsMap (g ≫ f) A).app F := by
  dsimp [terminalSectionsMap, restrictionComp]
  erw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact terminalIsTerminal.hom_ext _ _

/-- Identity restriction induces the identity on sections after identification. -/
theorem terminalSectionsMap_id (F : Sheaf X.smallEtaleTopology A) :
    (terminalSectionsMap (𝟙 X) A).app F ≫
        ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).map
          ((restrictionId A).hom.app F) =
      𝟙 ((sheafSections X.smallEtaleTopology A).obj (op (⊤_ X.Etale))).obj F := by
  dsimp [terminalSectionsMap, restrictionId]
  simp only [Category.comp_id]
  erw [← F.obj.map_comp]
  trans F.obj.map (𝟙 _)
  · congr 1
    apply Quiver.Hom.unop_inj
    exact terminalIsTerminal.hom_ext _ _
  · exact F.obj.map_id _

section Linear

variable (R : Type u) [CommRing R]

instance restriction_additive : (restriction f (ModuleCat.{u} R)).Additive where
  map_add := by
    intros
    apply Sheaf.hom_ext
    rfl

instance restriction_linear : (restriction f (ModuleCat.{u} R)).Linear R where
  map_smul φ r := by
    apply Sheaf.hom_ext
    rfl

/-- The induced map on the published global-section functors. -/
def sectionsMap :
    EtaleDerivedSections.sections X R ⟶
      restriction f (ModuleCat.{u} R) ⋙ EtaleDerivedSections.sections Y R :=
  (EtaleDerivedSections.sectionsIso X R).hom ≫
    terminalSectionsMap f (ModuleCat.{u} R) ≫
    Functor.whiskerLeft (restriction f (ModuleCat.{u} R))
      (EtaleDerivedSections.sectionsIso Y R).inv

end Linear

end Langlands.Geometry.EtalePullback
