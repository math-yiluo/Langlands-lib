/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import Mathlib.Algebra.Category.Ring.Limits
/-! # The supported coefficient ring limit as an abelian sheaf
Source: diagonal tower limit proof (1), ordinary coefficient limit.
(blueprint: lem-sfb-diagonal-supported-coefficient-limit).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- Forget the multiplication on coefficient sheaves, then apply closed direct image.
Source: diagonal tower limit proof (1)
(blueprint: lem-sfb-diagonal-supported-coefficient-limit). -/
abbrev diagonalSupportedCoefficientFunctor (Y : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology (ProjectiveLine Y)) CommRingCat.{u + 1} ⥤
      DiagonalAb (diagonalSurface Y) :=
  sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) ⋙
    lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)

/-- The actual supported finite coefficient tower, with quotient ring transitions.
Source: diagonal tower limit proof (1)
(blueprint: lem-sfb-diagonal-supported-coefficient-limit). -/
abbrev diagonalSupportedCoefficientTower (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :=
  Scheme.purTwistZlTower (ProjectiveLine Y) l ⋙ diagonalSupportedCoefficientFunctor Y

/-- The canonical integer-cast map into an additive coefficient sheaf.
Source: diagonal tower system proof (3), coefficient-unit normalization
(blueprint: lem-sfb-diagonal-supported-coefficient-limit). -/
def diagonalCoefficientIntegerMap (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R := by
  let J := Scheme.ProEt.topology X
  let Q := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R
  let P := (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let t : P ⟶ Q.obj :=
    { app V := AddCommGrpCat.ofHom
        ((Int.castAddHom (R.obj.obj V)).comp AddEquiv.ulift.toAddMonoidHom)
      naturality := by
        intro V W f
        ext n
        exact (map_intCast (R.obj.map f).hom n.down).symm }
  exact ⟨sheafifyLift J t Q.property⟩

/-- Send an integer to its cast in the finite coefficient sheaf and push it forward.
Source: diagonal tower system proof (3), quotient-unit normalization
(blueprint: lem-sfb-diagonal-supported-coefficient-limit). -/
def diagonalSupportedFiniteGenerator (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ) :
    diagonalIntegralSource Y ⟶ (diagonalSupportedCoefficientTower l Y).obj (op n) :=
  (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).map
    (diagonalCoefficientIntegerMap (ProjectiveLine Y) (Scheme.purTwistFiniteRing _ l n))

private theorem integerMap_sections (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (V : X.ProEtᵒᵖ) (n : ℤ) :
    (diagonalCoefficientIntegerMap X R).hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V
          (ULift.up n)) = (n : R.obj.obj V) := by
  change ((toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (diagonalCoefficientIntegerMap X R).hom).app V) (ULift.up n) = _
  unfold diagonalCoefficientIntegerMap
  rw [toSheafify_sheafifyLift]
  rfl

private theorem integerMap_naturality (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (f : R ⟶ S) :
    diagonalCoefficientIntegerMap X R ≫
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map f =
      diagonalCoefficientIntegerMap X S := by
  apply (sheafToPresheaf _ _).map_injective
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj S).property
  ext V n
  obtain ⟨n⟩ := n
  change (f.hom.app V) ((diagonalCoefficientIntegerMap X R).hom.app V
    ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V
        (ULift.up n))) = _
  erw [integerMap_sections, integerMap_sections]
  exact map_intCast (f.hom.app V).hom n

private def completedUnderlyingIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    (diagonalForget l (diagonalSurface Y)).obj
      ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y)) ≅
      (diagonalSupportedCoefficientFunctor Y).obj
        (Scheme.purTwistZlCompletion (ProjectiveLine Y) l) := by
  dsimp only [diagonalForget, diagonalCompletedRestriction, diagonalCompletedSource,
    diagonalSupportedCoefficientFunctor]
  exact ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by ext U x; rfl, by ext U x; rfl⟩

private instance coefficientLimits (Y : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (diagonalSupportedCoefficientFunctor Y) := by
  let J := Scheme.ProEt.topology (ProjectiveLine Y)
  let U := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
  let G := sheafCompose J U
  have : PreservesLimitsOfShape ℕᵒᵖ
      (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)) :=
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (diagonalImmersion Y)).rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : PreservesLimitsOfShape ℕᵒᵖ G := by
    let V := sheafToPresheaf J AddCommGrpCat.{u + 1}
    have : PreservesLimitsOfShape ℕᵒᵖ (G ⋙ V) :=
      inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
        (sheafToPresheaf J CommRingCat.{u + 1} ⋙
          (Functor.whiskeringRight _ _ _).obj U))
    exact preservesLimitsOfShape_of_reflects_of_preserves G V
  exact inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
    (G ⋙ lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)))

private theorem completedGenerator_eq (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    diagonalCompletedGenerator l Y ≫ (completedUnderlyingIso l Y).hom =
      (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).map
        (diagonalCoefficientIntegerMap (ProjectiveLine Y)
          (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)) := by
  have h : diagonalCompletedGenerator l Y =
      (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).map
        (diagonalCoefficientIntegerMap (ProjectiveLine Y)
          (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)) ≫
          (completedUnderlyingIso l Y).inv := by
    apply (diagonalCompletedGenerator_existsUnique l Y).unique
    · unfold diagonalCompletedGenerator
      exact (diagonalCompletedGenerator_existsUnique l Y).exists.choose_spec
    · intro U n
      let V := op ((Scheme.proEtaleBaseChange (diagonalImmersion Y)).obj U.unop)
      change HEq ((diagonalCoefficientIntegerMap (ProjectiveLine Y)
        (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)).hom.app V
          ((toSheafify (Scheme.ProEt.topology (ProjectiveLine Y))
            ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V (ULift.up n)))
                (n • (1 : (Scheme.purTwistZlCompletion (ProjectiveLine Y) l).obj.obj V))
      have hz := zsmul_one (R :=
        (Scheme.purTwistZlCompletion (ProjectiveLine Y) l).obj.obj V) n
      exact heq_of_eq ((integerMap_sections (ProjectiveLine Y)
        (Scheme.purTwistZlCompletion (ProjectiveLine Y) l) V n).trans hz.symm)
  erw [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Forgetting the completed supported unit identifies it with the limit of the
supported finite coefficient rings, with the canonical integer unit.

Source: blueprint latest, `sk-prop-diagonal-tower-limit.proof.md`, paragraph (1),
ordinary coefficient limit; Stacks Tag 099L.
(blueprint: lem-sfb-diagonal-supported-coefficient-limit).

Proof: the underlying abelian sheaf of the ringed direct image defining
`diagonalCompletedSource` is closed direct image of the additive sheaf of the
completed ring on the diagonal. Restricting its scalar action changes no
underlying additive sections. Forgetting ring structure preserves limits,
because ring operations on a limit are componentwise; closed direct image,
being a right adjoint, also preserves limits. Apply these two preservation
comparisons to the defining finite-ring limit of `purTwistZlCompletion`.
The resulting isomorphism's projection is the additive direct image of the
finite ring projection. The completed integer generator is uniquely determined
by taking each locally constant integer to that integer times one. Ring
projections preserve integer casts, so its composite with this projection is
exactly `diagonalSupportedFiniteGenerator`. This works for n=0 and the empty
scheme, without invertibility of l or any derived hypothesis. -/
theorem diagonal_supported_coefficient_limit (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    ∃ e : (diagonalForget l (diagonalSurface Y)).obj
        ((diagonalCompletedRestriction l (diagonalSurface Y)).obj
          (diagonalCompletedSource l Y)) ≅ limit (diagonalSupportedCoefficientTower l Y),
      ∀ n : ℕ, diagonalCompletedGenerator l Y ≫ e.hom ≫
        limit.π (diagonalSupportedCoefficientTower l Y) (op n) =
          diagonalSupportedFiniteGenerator l Y n := by
  let F := diagonalSupportedCoefficientFunctor Y
  let H := Scheme.purTwistZlTower (ProjectiveLine Y) l
  let e := completedUnderlyingIso l Y ≪≫ preservesLimitIso F H
  refine ⟨e, ?_⟩
  intro n
  dsimp only [e]
  erw [Iso.trans_hom, Category.assoc, preservesLimitIso_hom_π, ← Category.assoc,
    completedGenerator_eq]
  change (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).map
    (diagonalCoefficientIntegerMap _ _) ≫
      (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).map _ = _
  erw [← Functor.map_comp, integerMap_naturality]
  rfl
end AlgebraicGeometry.ProEtale
