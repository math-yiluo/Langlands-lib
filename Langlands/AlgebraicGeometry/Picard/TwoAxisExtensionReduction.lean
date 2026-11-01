import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedClassPresheaf
import Langlands.AlgebraicGeometry.Picard.SelfProductBaseChange
import Langlands.AlgebraicGeometry.Picard.ValuationRingTwoAxisExtensionStatement

/-! # Actual bundle extension from surjectivity of two-axis classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace TwoAxisFamily

open Langlands.AbelianScheme

variable {S T : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- The canonical test-scheme map to the identity test scheme. -/
def toBase (b : T ⟶ S) : Over.mk b ⟶ Over.mk (𝟙 S) :=
  Over.homMk b (by simp)

/-- Projection from each direct base-changed self-product to the original one. -/
abbrev productToBase (T : Over S) :
    (mumfordProduct (abelian A T)).left ⟶ (mumfordProduct A).left :=
  mumfordProductBaseChangeMap A T.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The family maps commute with the canonical projections to the original product. -/
@[reassoc]
lemma productMap_toBase {T U : Over S} (h : T ⟶ U) :
    productMap A h ≫ productToBase A U = productToBase A T := by
  apply pullback.hom_ext
  · simp only [productToBase, mumfordProductBaseChangeMap, selfProductBaseChangeMap,
      pullback.map, Category.assoc, pullback.lift_fst]
    change productMap A h ≫
        (pullback.fst (abelian A U).X.hom (abelian A U).X.hom ≫
          pullback.fst A.X.hom U.hom) =
      pullback.fst (abelian A T).X.hom (abelian A T).X.hom ≫
        pullback.fst A.X.hom T.hom
    rw [productMap_fst_assoc, carrierMap_fst]
  · simp only [productToBase, mumfordProductBaseChangeMap, selfProductBaseChangeMap,
      pullback.map, Category.assoc, pullback.lift_snd]
    change productMap A h ≫
        (pullback.snd (abelian A U).X.hom (abelian A U).X.hom ≫
          pullback.fst A.X.hom U.hom) =
      pullback.snd (abelian A T).X.hom (abelian A T).X.hom ≫
        pullback.fst A.X.hom T.hom
    rw [productMap_snd_assoc, carrierMap_fst]

/-- The actual self-product at the identity test scheme is canonically the
original self-product. -/
def productIdentityIso :
    (mumfordProduct (abelian A (Over.mk (𝟙 S)))).left ≅
      (mumfordProduct A).left :=
  mumfordProductBaseChangeIso A (𝟙 S) ≪≫
    asIso (pullback.fst (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) (𝟙 S))

@[simp]
lemma productIdentityIso_hom :
    (productIdentityIso A).hom = productToBase A (Over.mk (𝟙 S)) :=
  mumfordProductBaseChangeIso_hom_fst A (𝟙 S)

/-- The canonical product map followed by the inverse identity comparison is
exactly the presheaf's family map. -/
lemma productToBase_comp_identity_inv (b : T ⟶ S) :
    mumfordProductBaseChangeMap A b ≫ (productIdentityIso A).inv =
      productMap A (toBase b) := by
  apply (cancel_mono (productIdentityIso A).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    productIdentityIso_hom, productMap_toBase]
  rfl

end TwoAxisFamily

namespace TwoAxisRigidifiedLineBundle

open Langlands.AbelianScheme TwoAxisFamily Langlands.Scheme.Modules

variable {S T : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- Surjectivity on compatible isomorphism classes supplies an actual
representative and an actual compatible pullback isomorphism. -/
theorem exists_pullback_iso_of_classesPullback_surjective
    {T U : Over S} (h : T ⟶ U)
    (hsurj : Function.Surjective (classesPullback A h)) (L : relative A T) :
    ∃ M : relative A U, Nonempty ((relativePullback A h).obj M ≅ L) := by
  obtain ⟨c, hc⟩ := hsurj (Quotient.mk _ L)
  revert hc
  refine Quotient.inductionOn c (fun M hc => ?_)
  exact ⟨M, Quotient.exact hc⟩

/-- Class extension along the specified test map yields an actual bundle
extension along the canonical product map. -/
theorem actualBundleExtension_of_classesPullback_surjective (b : T ⟶ S)
    (hsurj : Function.Surjective (classesPullback A (toBase b)))
    (D : LineBundle (mumfordProduct ((baseChange b).obj A)).left)
    (hα : Nonempty ((Scheme.Modules.pullback
      (mumfordSection ((baseChange b).obj A))).obj D.obj ≅
        structureSheaf ((baseChange b).obj A).X.left))
    (hβ : Nonempty ((Scheme.Modules.pullback
      (twoAxisSecond ((baseChange b).obj A))).obj D.obj ≅
        structureSheaf ((baseChange b).obj A).X.left)) :
    ∃ E : LineBundle (mumfordProduct A).left,
      Nonempty (((LineBundle.pullback (mumfordProductBaseChangeMap A b)).obj E).obj ≅
        D.obj) := by
  obtain ⟨ρ⟩ := nonempty_twoAxisRigidification ((baseChange b).obj A) D hα hβ
  let L : relative A (Over.mk b) := ofLineBundle D ρ
  obtain ⟨M, ⟨i⟩⟩ :=
    exists_pullback_iso_of_classesPullback_surjective A (toBase b) hsurj L
  let N : LineBundle (mumfordProduct (abelian A (Over.mk (𝟙 S)))).left :=
    (forget _ _ _ _ _).obj M
  refine ⟨(LineBundle.pullback (productIdentityIso A).inv).obj N, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp (mumfordProductBaseChangeMap A b)
      (productIdentityIso A).inv).app N.obj ≪≫
    (Scheme.Modules.pullbackCongr (productToBase_comp_identity_inv A b)).app N.obj ≪≫
    (LineBundle.forget _).mapIso ((forget _ _ _ _ _).mapIso i)

end TwoAxisRigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard
open TwoAxisFamily TwoAxisRigidifiedLineBundle

/-- A uniform proof of surjectivity for the specified compatible-class
restrictions would prove the exact published two-axis bundle target. -/
theorem valuationRingTwoAxisExtension_of_classesPullback_surjective
    (hsurj : ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
      (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
      (A : AbelianScheme (Spec (CommRingCat.of R))),
      Function.Surjective (classesPullback A
        (toBase (Spec.map (CommRingCat.ofHom (algebraMap R K)))))) :
    ValuationRingTwoAxisExtensionStatement.{u} := by
  intro R _ _ _ K _ _ _ A
  dsimp only
  intro D hα hβ
  exact actualBundleExtension_of_classesPullback_surjective A
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) (hsurj R K A) D hα hβ

end Langlands.AbelianScheme
