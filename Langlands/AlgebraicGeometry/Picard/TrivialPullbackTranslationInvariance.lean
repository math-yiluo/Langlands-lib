import Langlands.AbelianScheme.KernelCharacterShearInvariance
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero

/-! # Translation invariance from invariance of the kernel character -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

variable {X Y : Scheme.{u}}

/-- Pulling back along an isomorphism of schemes and then along its inverse returns the
original line bundle. -/
def pullbackInvPullbackIso (p : X ⟶ Y) [IsIso p] (M : LineBundle Y) :
    (pullback (inv p)).obj ((pullback p).obj M) ≅ M :=
  (pullbackComp (inv p) p).app M ≪≫
    eqToIso (congrArg (fun g ↦ (pullback g).obj M) (IsIso.inv_hom_id p)) ≪≫
      (pullbackId Y).app M

/-- Pullback along an isomorphism of schemes reflects isomorphisms of line bundles. -/
lemma nonempty_iso_of_pullback_iso (p : X ⟶ Y) [IsIso p] {M N : LineBundle Y}
    (e : (pullback p).obj M ≅ (pullback p).obj N) : Nonempty (M ≅ N) :=
  ⟨(pullbackInvPullbackIso p M).symm ≪≫ (pullback (inv p)).mapIso e ≪≫
    pullbackInvPullbackIso p N⟩

end Langlands.AlgebraicGeometry.Picard.LineBundle

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- The second projection from the relative space over the base itself. -/
abbrev baseRelativeSnd (B : AbelianScheme S) :
    (relativeSpace B.X.hom).obj (Over.mk (𝟙 S)) ⟶ B.X.left :=
  pullback.snd (Over.mk (𝟙 S)).hom B.X.hom

instance (B : AbelianScheme S) : IsIso (baseRelativeSnd B) :=
  haveI : IsIso (Over.mk (𝟙 S)).hom := inferInstanceAs (IsIso (𝟙 S))
  inferInstance

/-- Over the base itself, the shear by a section is translation by that section. -/
lemma shear_baseRelativeSnd (B : AbelianScheme S) (x : Over.mk (𝟙 S) ⟶ B.X) :
    shear B (𝟙 (Over.mk (𝟙 S))) x ≫ baseRelativeSnd B =
      baseRelativeSnd B ≫ (translation B.toGrp x).left := by
  rw [shear_snd]
  change _ = (relativeSnd B (Over.mk (𝟙 S))).left ≫ _
  rw [← Over.comp_left, points_translation,
    Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from _) (relativeFst B (Over.mk (𝟙 S)))]

/-- An ordinary trivial homomorphism pullback gives a trivial homomorphism pullback of the
line bundle moved to the relative space over the base itself. -/
lemma hasTrivialHomPullback_baseRelativeSnd {A B : AbelianScheme S} (f : A ⟶ B)
    (L : LineBundle B.X.left)
    (hL : Nonempty ((Scheme.Modules.pullback (hom f)).obj L.obj ≅
      SheafOfModules.unit A.X.left.ringCatSheaf)) :
    HasTrivialHomPullback f (Over.mk (𝟙 S))
      ((LineBundle.pullback (baseRelativeSnd B)).obj L) := by
  obtain ⟨α⟩ := hL
  exact ⟨squarePullbackIso (hom f) ((homFamilySpaceMap f).app (Over.mk (𝟙 S)))
      (baseRelativeSnd A) (baseRelativeSnd B) (homFamilySpaceMap_snd f (Over.mk (𝟙 S))) L.obj ≪≫
    (Scheme.Modules.pullback (baseRelativeSnd A)).mapIso α ≪≫
      pullbackUnitIso (baseRelativeSnd A)⟩

/-- A line bundle with trivial homomorphism pullback is invariant under translation by
every section of the target which lifts to the source, provided the class character over
the base itself is injective. -/
theorem nonempty_translation_pullback_iso {A B : AbelianScheme S} (f : A ⟶ B)
    (hinj : Function.Injective
      (trivialHomPullbackClassCharacter f (T := Over.mk (𝟙 S)) (universalGlobalFunctions A)))
    (L : LineBundle B.X.left)
    (hL : Nonempty ((Scheme.Modules.pullback (hom f)).obj L.obj ≅
      SheafOfModules.unit A.X.left.ringCatSheaf))
    (a : Over.mk (𝟙 S) ⟶ A.X) :
    Nonempty ((LineBundle.pullback (translation B.toGrp (a ≫ (groupHom f).hom.hom)).left).obj L ≅
      L) := by
  obtain ⟨e⟩ := nonempty_shear_pullback_iso f a (universalGlobalFunctions A) hinj
    ((LineBundle.pullback (baseRelativeSnd B)).obj L)
    (hasTrivialHomPullback_baseRelativeSnd f L hL)
  apply LineBundle.nonempty_iso_of_pullback_iso (baseRelativeSnd B)
  exact ((LineBundle.pullbackComp (baseRelativeSnd B)
      (translation B.toGrp (a ≫ (groupHom f).hom.hom)).left).app L) ≪≫
    eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj L)
      (shear_baseRelativeSnd B (a ≫ (groupHom f).hom.hom)).symm) ≪≫
    ((LineBundle.pullbackComp (shear B (𝟙 (Over.mk (𝟙 S))) (a ≫ (groupHom f).hom.hom))
      (baseRelativeSnd B)).app L).symm ≪≫ e

/-- If every section of the target lifts to the source and the class character over the
base itself is injective, then a line bundle with trivial homomorphism pullback is
translation invariant. -/
theorem isTranslationInvariant_of_trivialHomPullback {A B : AbelianScheme S} (f : A ⟶ B)
    (hlift : ∀ x : Over.mk (𝟙 S) ⟶ B.X, ∃ a : Over.mk (𝟙 S) ⟶ A.X,
      a ≫ (groupHom f).hom.hom = x)
    (hinj : Function.Injective
      (trivialHomPullbackClassCharacter f (T := Over.mk (𝟙 S)) (universalGlobalFunctions A)))
    (L : LineBundle B.X.left)
    (hL : Nonempty ((Scheme.Modules.pullback (hom f)).obj L.obj ≅
      SheafOfModules.unit A.X.left.ringCatSheaf)) :
    IsTranslationInvariant B.toGrp L := by
  intro x
  obtain ⟨a, rfl⟩ := hlift x
  exact nonempty_translation_pullback_iso f hinj L hL a

end Langlands.AbelianScheme
