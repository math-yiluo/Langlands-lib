import Langlands.GroupScheme.Torus.ResidueFiberScalarExtension
import Langlands.GroupScheme.Rational.TorusDominationBaseChange
import Langlands.GroupScheme.SchemeActionOrbit

/-! # Pointed torus domination from diagonalizable parametrizations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace PointedTorusDomination

variable {S : Scheme.{u}} {X : Over S} {H : GroupScheme S}

/-- Translate the image of a specified source section to the group identity. -/
def pointedNormalization (x : 𝟙_ (Over S) ⟶ X) (p : X ⟶ H.X) : X ⟶ H.X :=
  p ≫ (SchemeAction.translationIso (ModObj.regular H.X) (x ≫ p)⁻¹).hom

/-- The specified source section maps to the identity after normalization. -/
theorem pointedNormalization_point (x : 𝟙_ (Over S) ⟶ X) (p : X ⟶ H.X) :
    x ≫ pointedNormalization x p = 1 := by
  rw [pointedNormalization, ← Category.assoc, SchemeAction.translationIso,
    SchemeAction.comp_translation]
  change (toUnit (𝟙_ (Over S)) ≫ (x ≫ p)⁻¹) * (x ≫ p) = 1
  simp

/-- Translation preserves the dominance of the actual scheme morphism. -/
theorem pointedNormalization_isDominant
    (x : 𝟙_ (Over S) ⟶ X) (p : X ⟶ H.X) [IsDominant p.left] :
    IsDominant (pointedNormalization x p).left := by
  have : IsIso
      (SchemeAction.translationIso (ModObj.regular H.X) (x ≫ p)⁻¹).hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map
      (SchemeAction.translationIso (ModObj.regular H.X) (x ≫ p)⁻¹).hom))
  change IsDominant (p.left ≫
    (SchemeAction.translationIso (ModObj.regular H.X) (x ≫ p)⁻¹).hom.left)
  infer_instance

end PointedTorusDomination

namespace Diagonalizable

variable (k : Type u) [Field k] (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (H : GroupScheme (Spec (CommRingCat.of k)))

/-- A dominant morphism from a finitely generated diagonalizable group to an
affine geometrically integral group gives pointed split-torus domination after
a finite separable field extension. -/
theorem exists_finiteSeparable_hasPointedSplitTorusDomination
    [IsAffineHom H.X.hom] [GeometricallyIntegral H.X.hom]
    (p : (groupScheme (CommRingCat.of k) Λ).X ⟶ H.X) [IsDominant p.left] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (_ : Module.Finite k L) (_ : Algebra.IsSeparable k L),
      HasPointedSplitTorusDomination ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj H) := by
  classical
  obtain ⟨I, A, hI, hA, hfin, ⟨e⟩⟩ :=
    exists_splitFiniteIso (CommRingCat.of k) Λ
  let D := splitTorus (Spec (CommRingCat.of k)) I
  let q : D.X ⊗ (groupScheme (CommRingCat.of k) A).X ⟶ H.X :=
    e.inv.hom.hom ≫ p
  have : IsIso e.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
  have : IsDominant q.left := by
    change IsDominant (e.inv.hom.hom.left ≫ p.left)
    infer_instance
  have : IsAffineHom D.X.hom :=
    isAffineHom_splitTorus_spec (CommRingCat.of k) I
  have : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨P, hP⟩ := exists_isDominant_residueFiberMorphism k A D.X H.X q
  let b := Spec.map (CommRingCat.ofHom (algebraMap k P.asIdeal.ResidueField))
  let DL := (GroupScheme.baseChange b).obj D
  let HL := (GroupScheme.baseChange b).obj H
  let r : DL.X ⟶ HL.X := residueFiberMorphism k A D.X H.X q P
  have : IsDominant r.left := hP
  refine ⟨P.asIdeal.ResidueField, inferInstance, inferInstance, inferInstance,
    inferInstance, DL,
    PointedTorusDomination.pointedNormalization (1 : 𝟙_ _ ⟶ DL.X) r,
    (isSplitTorus_splitTorus I).baseChange b,
    PointedTorusDomination.pointedNormalization_isDominant _ r, ?_⟩
  exact PointedTorusDomination.pointedNormalization_point _ r

end Diagonalizable

end Langlands.GroupScheme
