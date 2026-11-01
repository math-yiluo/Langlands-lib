import Langlands.AbelianScheme.RelativeIntegralActionLocusGeometry

/-! # The actual universal integral action on its equation locus -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Opposite

universe u uI uO

namespace Langlands.AbelianScheme

open Langlands.GroupScheme.Cartier

variable {S : Scheme.{u}} (B : Langlands.AbelianScheme S)
    {I : Type uI} [Fintype I] {O : Type uO} [Ring O] (b : Basis I ℤ O)
    (E : Over S)
    (e : (locallyNoetherianTestInclusion S).op ⋙
        relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
          forget AddCommGrpCat.{u} ≅
      (locallyNoetherianTestInclusion S).op ⋙ yoneda.obj E)
    (hpow : IsLocallyNoetherian (∏ᶜ fun _ : I => E).left)

/-- Classification commutes with the actual canonical relative endomorphism restriction. -/
theorem relativeIntegralActionLocusHomEquiv_comp
    {T T' : ObjectProperty.FullSubcategory
      (fun T : Over S => IsLocallyNoetherian T.left)}
    (f : T ⟶ T') (g : T'.obj ⟶ relativeIntegralActionLocus B b E e hpow) :
    relativeIntegralActionLocusHomEquiv B b E e hpow T (f.hom ≫ g) =
      (relativeEndRestrict B f.hom).comp
        (relativeIntegralActionLocusHomEquiv B b E e hpow T' g) := by
  apply (integralActionEquiv b ((baseChange T.obj.hom).obj B)).injective
  apply Subtype.ext
  funext i
  simp only [integralActionEquiv_apply, RingHom.comp_apply,
    relativeIntegralActionLocusHomEquiv_apply_basis]
  have h := e.inv.naturality_apply (CD := fun X => X) f.op
    ((g ≫ relativeIntegralActionLocusInclusion B b E e hpow) ≫
      Pi.π (fun _ : I => E) i)
  change e.inv.app (op T)
      (f.hom ≫ ((g ≫ relativeIntegralActionLocusInclusion B b E e hpow) ≫
        Pi.π (fun _ : I => E) i)) =
    (relativeEndRestrict B f.hom)
      (e.inv.app (op T')
        ((g ≫ relativeIntegralActionLocusInclusion B b E e hpow) ≫
          Pi.π (fun _ : I => E) i)) at h
  simpa only [Category.assoc] using h

variable [IsLocallyNoetherian S] [LocallyOfFiniteType E.hom] [IsSeparated E.hom]

/-- The actual integral action obtained by classifying the identity of the equation locus. -/
def relativeIntegralActionUniversal :
    O →+* CategoryTheory.End
      ((baseChange (relativeIntegralActionLocusTest E B b e).obj.hom).obj B) :=
  relativeIntegralActionLocusHomEquiv B b E e
    (relativeEndomorphismPower_isLocallyNoetherian (I := I) E)
    (relativeIntegralActionLocusTest E B b e) (𝟙 _)

/-- Every classified action is the canonical restriction of the actual universal action. -/
theorem relativeIntegralActionUniversal_restrict
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))
    (f : T.obj ⟶ (relativeIntegralActionLocusTest E B b e).obj) :
    (relativeEndRestrict B f).comp (relativeIntegralActionUniversal B b E e) =
      relativeIntegralActionLocusHomEquiv B b E e
        (relativeEndomorphismPower_isLocallyNoetherian (I := I) E) T f := by
  simpa only [relativeIntegralActionUniversal, Category.comp_id (obj := Over S),
    ObjectProperty.homMk_hom] using
    (relativeIntegralActionLocusHomEquiv_comp B b E e
      (relativeEndomorphismPower_isLocallyNoetherian (I := I) E)
      (ObjectProperty.homMk (X := T) (Y := relativeIntegralActionLocusTest E B b e) f)
      (𝟙 _)).symm

/-- Actual maps into the locus classify all actions by restriction of its universal action. -/
def relativeIntegralActionUniversalHomEquiv
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left)) :
    (T.obj ⟶ (relativeIntegralActionLocusTest E B b e).obj) ≃
      (O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B)) :=
  relativeIntegralActionLocusHomEquiv B b E e
    (relativeEndomorphismPower_isLocallyNoetherian (I := I) E) T

/-- The displayed universal classification has its literal canonical restriction formula. -/
theorem relativeIntegralActionUniversalHomEquiv_apply
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))
    (f : T.obj ⟶ (relativeIntegralActionLocusTest E B b e).obj) :
    relativeIntegralActionUniversalHomEquiv B b E e T f =
      (relativeEndRestrict B f).comp (relativeIntegralActionUniversal B b E e) :=
  (relativeIntegralActionUniversal_restrict B b E e T f).symm

/-- Every actual integral action has a unique actual classifying morphism. -/
theorem relativeIntegralActionUniversal_existsUnique
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))
    (a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B)) :
    ∃! f : T.obj ⟶ (relativeIntegralActionLocusTest E B b e).obj,
      (relativeEndRestrict B f).comp (relativeIntegralActionUniversal B b E e) = a := by
  let eqv := relativeIntegralActionUniversalHomEquiv B b E e T
  refine ⟨eqv.symm a, ?_, ?_⟩
  · exact (relativeIntegralActionUniversalHomEquiv_apply B b E e T (eqv.symm a)).symm.trans
      (eqv.apply_symm_apply a)
  · intro f hf
    apply eqv.injective
    rw [Equiv.apply_symm_apply]
    exact (relativeIntegralActionUniversalHomEquiv_apply B b E e T f).trans hf

end Langlands.AbelianScheme
