import Langlands.AlgebraicGeometry.Picard.SelfProductBaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-! # Actual bundle extension when the valuation base is a field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace LineBundle

variable {X Y : Scheme.{u}} (q : X ⟶ Y) [IsIso q]

/-- Extend an actual line bundle across a scheme isomorphism by inverse pullback. -/
def extensionAlongIso (D : LineBundle X) : LineBundle Y :=
  (pullback (inv q)).obj D

/-- Restricting the inverse-pullback extension recovers the original module sheaf. -/
def extensionAlongIsoRestrictionIso (D : LineBundle X) :
    ((pullback q).obj (extensionAlongIso q D)).obj ≅ D.obj :=
  (Scheme.Modules.pullbackComp q (inv q)).app D.obj ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id q)).app D.obj ≪≫
      (Scheme.Modules.pullbackId X).app D.obj

end LineBundle

/-- The canonical map of self-products is an isomorphism for an isomorphic base change. -/
theorem isIso_selfProductBaseChangeMap {S T X : Scheme.{u}}
    (p : X ⟶ S) (b : T ⟶ S) [IsIso b] :
    IsIso (selfProductBaseChangeMap p b) := by
  unfold selfProductBaseChangeMap
  infer_instance

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry

/-- A chosen fraction-field map is an isomorphism if the original domain is a field. -/
theorem isIso_fractionFieldSpecMap_of_isField
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : IsField R) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : IsIso (CommRingCat.ofHom (algebraMap R K)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨IsFractionRing.injective R K, IsFractionRing.surjective_iff_isField.mpr hR⟩
  infer_instance

end Langlands.AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Every generic self-product bundle extends when the original domain is a field,
without any axis-triviality premise. -/
theorem selfProductLineBundleExtension_of_isField
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : IsField R) (A : AbelianScheme (Spec (CommRingCat.of R)))
    (D : LineBundle (mumfordProduct
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A)).left) :
    ∃ E : LineBundle (mumfordProduct A).left,
      Nonempty (((LineBundle.pullback
        (mumfordProductBaseChangeMap A
          (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj E).obj ≅ D.obj) := by
  have := Langlands.AlgebraicGeometry.isIso_fractionFieldSpecMap_of_isField R K hR
  let q := mumfordProductBaseChangeMap A
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have : IsIso q :=
    isIso_selfProductBaseChangeMap A.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  exact ⟨LineBundle.extensionAlongIso q D,
    ⟨LineBundle.extensionAlongIsoRestrictionIso q D⟩⟩

end Langlands.AbelianScheme
