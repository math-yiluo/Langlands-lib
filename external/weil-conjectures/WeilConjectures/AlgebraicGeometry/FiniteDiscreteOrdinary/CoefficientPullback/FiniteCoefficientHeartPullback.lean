/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed

/-! # The constructed inverse-image comparison on coefficient hearts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

section Mate
variable {C D E F : Type*}
  [Category C] [Category D] [Category E] [Category F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
  {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Inverse mates of isomorphisms are isomorphisms when the vertical functors are
 equivalences. Source: the iterated-mate conjugation identity
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
theorem inverseMate_isIso [G.IsEquivalence] [H.IsEquivalence]
    (β : TwoSquare R₁ H G R₂) [IsIso β] :
    IsIso ((mateEquiv adj₁ adj₂).symm β) := by
  let aG : G ⊣ G.asEquivalence.inverse := G.asEquivalence.toAdjunction
  let aH : H ⊣ H.asEquivalence.inverse := H.asEquivalence.toAdjunction
  have : IsIso aG.unit := by
    simp only [aG, Equivalence.toAdjunction_unit]
    infer_instance
  have : IsIso aH.counit := by
    simp only [aH, Equivalence.toAdjunction_counit]
    infer_instance
  have : IsIso β := by
    infer_instance
  have hβ : IsIso (mateEquiv aH aG β) := by
    dsimp only [mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk]
    infer_instance
  let α := (mateEquiv adj₁ adj₂).symm β
  have hh := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ aG aH α
  have hα : mateEquiv adj₁ adj₂ α = β := Equiv.apply_symm_apply _ _
  have : IsIso (conjugateEquiv (adj₁.comp aH) (aG.comp adj₂) α) := by
    rw [← hh, hα]
    exact hβ
  exact conjugateEquiv_of_iso (adj₁.comp aH) (aG.comp adj₂) α
end Mate

variable (A : Type u) [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A]
variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

/-- Scalar restriction followed by the concrete normalized section encoding.
Source: the heart functor of coefficientEncoding
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
@[irreducible]
def heart (e : Mon.mk R ≅ Mon.mk (coefficient A)) (T : Scheme.{u}) (E : Encoding A T) :=
  Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.inv.hom T) ⋙ sectionEncoding A T E.ringIso ⋙ fixedRestriction A T

omit [IsCommMonObj R] in
/-- The concrete heart functor equals the one specified by the supplied equivalences.
Source: the two normalization equations of Encoding
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
theorem heart_eq (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    heart A R e T E = Mod.comap (coefficientMap e.inv.hom T) ⋙
      E.ordinary.functor ⋙ E.fixed.functor := by
  simp only [heart, E.ordinary_functor, E.fixed_functor]

/-- The normalized heart encoding is additive.
Source: the supplied additive equivalences and scalar restriction
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
instance heart_additive (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) : (heart A R e T E).Additive := by
  rw [heart_eq]
  infer_instance

/-- The heart encoding is an equivalence, by scalar restriction along an isomorphism.
Source: restriction of scalars along an isomorphism
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
instance heart_isEquivalence (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) : (heart A R e T E).IsEquivalence := by
  have : IsIso e.inv.hom := by
    change IsIso ((Mon.forget _).map e.inv)
    infer_instance
  have : IsIso (coefficientMap e.inv.hom T) := by
    dsimp [coefficientMap]
    infer_instance
  have : (Mod.comap (coefficientMap e.inv.hom T)).IsEquivalence :=
    (inferInstance : (Mod.comapEquivalenceOfIsIso
      (coefficientMap e.inv.hom T)).functor.IsEquivalence)
  rw [heart_eq]
  infer_instance

/-- The identity on sections, as an isomorphism of fixed-scalar sheaves.
Source: Stacks 03D3 and normalized section-action reconstruction
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
def sectionHeartPushIso (T U : Scheme.{u}) (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) (M : Internal A U) :
    (sectionEncoding A T eT.ringIso ⋙ fixedRestriction A T).obj
      ((CondensedRing.lowerStar (coefficient A) f).obj M) ≅
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
      ((sectionEncoding A U eU.ringIso ⋙ fixedRestriction A U).obj M) := by
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun V ↦ ?_) ?_)
  · refine (show (((sectionEncoding A T eT.ringIso ⋙ fixedRestriction A T).obj
        ((CondensedRing.lowerStar (coefficient A) f).obj M)).obj.obj V : Type (u + 1)) ≃ₗ[
          ULift.{u + 1} A]
        (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
          ((sectionEncoding A U eU.ringIso ⋙ fixedRestriction A U).obj M)).obj.obj V) from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := sectionPushforward_smul A T U f eT eU M V }).toModuleIso
  · intro V V' g
    ext m
    rfl

/-- The identity-on-sections direct-image comparison is natural in the internal module.
Source: Stacks 03D3 and normalized section-action reconstruction
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
def encodingHeartPush (T U : Scheme.{u}) (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.lowerStar (coefficient A) f ⋙
        sectionEncoding A T eT.ringIso ⋙ fixedRestriction A T ≅
      (sectionEncoding A U eU.ringIso ⋙ fixedRestriction A U) ⋙
        lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f :=
  NatIso.ofComponents (sectionHeartPushIso A T U f eT eU) (by
    intro M N g
    ext V m
    dsimp [sectionHeartPushIso, CondensedRing.lowerStar]
    rfl)

/-- The direct-image comparison is restriction of scalars followed by the identity
on normalized sections. Source: coefficient-map naturality and normalized section actions
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
@[irreducible] def heartPush (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    CondensedRing.lowerStar R f ⋙ heart A R e Y EY ≅
      heart A R e X EX ⋙ lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f := by
  unfold heart
  exact
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.comapLowerStarIso e.inv.hom f)
        (sectionEncoding A Y EY.ringIso ⋙ fixedRestriction A Y) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Mod.comap (coefficientMap e.inv.hom X))
        (encodingHeartPush A Y X f EY EX) ≪≫
      (Functor.associator _ _ _).symm

/-- Conjugate the specified direct-image comparison under the geometric adjunctions.
The construction uses only proved equivalences and the identity-on-sections comparison.
Source: Stacks 03D3; uniqueness of adjoints
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
@[irreducible] def heartPull (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    CondensedRing.upperStar R f ⋙ heart A R e X EX ≅
      heart A R e Y EY ⋙ upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f := by
  let β : TwoSquare (CondensedRing.lowerStar R f) (heart A R e X EX)
      (heart A R e Y EY) (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f) :=
    (heartPush A R e f EX EY).hom
  have : IsIso β := inferInstanceAs (IsIso (heartPush A R e f EX EY).hom)
  have := inverseMate_isIso (CondensedRing.upperStarLowerStarAdjunction R f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f) β
  exact (asIso ((mateEquiv (CondensedRing.upperStarLowerStarAdjunction R f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)).symm
      β)).symm

/-- The inverse of heartPull is precisely the mate of the sectionwise heartPush.
Source: the definition by inverse mates
(blueprint: lem-sfb-finite-coefficient-heart-pullback). -/
theorem heartPull_mate (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    mateEquiv (CondensedRing.upperStarLowerStarAdjunction R f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
      ((heartPull A R e f EX EY).inv) =
    (heartPush A R e f EX EY).hom := by
  unfold heartPull
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback
