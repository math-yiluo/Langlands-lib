import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedClassPresheaf
import Langlands.AlgebraicGeometry.Picard.TwoAxisCarrierIsoAbelian
import Langlands.AlgebraicGeometry.Picard.CartesianSelfProduct
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Base change of the two-axis class presheaf: cartesian squares and carriers -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

namespace TwoAxisFamily

open Langlands.AbelianScheme

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- The carrier map of a test-scheme map is a base change of that map. -/
theorem carrierMap_isPullback {T U : Over S} (h : T ⟶ U) :
    IsPullback (carrierMap A h) (abelian A T).X.hom (abelian A U).X.hom h.left := by
  refine IsPullback.of_right (h₁₂ := pullback.fst A.X.hom U.hom)
    (v₁₃ := A.X.hom) (h₂₂ := U.hom) ?_ (carrierMap_snd A h)
    (IsPullback.of_hasPullback A.X.hom U.hom)
  rw [carrierMap_fst, Over.w h]
  exact IsPullback.of_hasPullback A.X.hom T.hom

/-- The self-product map of a test-scheme map is a base change of that map. -/
theorem productMap_isPullback {T U : Over S} (h : T ⟶ U) :
    IsPullback (productMap A h) (mumfordProduct (abelian A T)).hom
      (mumfordProduct (abelian A U)).hom h.left :=
  cartesianSelfProductMap_isPullback (abelian A T).X.hom (abelian A U).X.hom
    (carrierMap A h) h.left (carrierMap_snd A h) (carrierMap_isPullback A h)

end TwoAxisFamily

namespace TwoAxisRigidifiedLineBundle

open Langlands.AbelianScheme TwoAxisFamily

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

lemma classesPullback_mk {T U : Over S} (h : T ⟶ U) (L : relative A U) :
    classesPullback A h ⟦L⟧ = ⟦(relativePullback A h).obj L⟧ :=
  rfl

/-- Pullback of classes is contravariantly functorial. -/
lemma classesPullback_comp {T U V : Over S} (h : T ⟶ U) (k : U ⟶ V) (x : Classes A V) :
    classesPullback A (h ≫ k) x = classesPullback A h (classesPullback A k x) := by
  induction x using Quotient.inductionOn with
  | h L => exact Quotient.sound ⟨((relativePullbackComp A h k).app L).symm⟩

/-- Two classes over a test scheme agree as soon as their actual line bundles are isomorphic. -/
theorem mk_eq_mk_of_carrierIso {T : Over S} {L M : relative A T}
    (e : L.obj.carrier ≅ M.obj.carrier) : (⟦L⟧ : Classes A T) = ⟦M⟧ :=
  Quotient.sound (nonempty_iso_of_carrierIso (abelian A T) e)

/-- Equal classes have isomorphic actual line bundles. -/
theorem nonempty_carrierIso_of_mk_eq_mk {T : Over S} {L M : relative A T}
    (H : (⟦L⟧ : Classes A T) = ⟦M⟧) : Nonempty (L.obj.carrier ≅ M.obj.carrier) := by
  obtain ⟨e⟩ := Quotient.exact H
  exact ⟨(TwoAxisRigidifiedModule.forget _ _ _ _ _).mapIso ((ObjectProperty.ι _).mapIso e)⟩

/-- The class of a representative is equal to the class of a pullback exactly when the
actual line bundles are isomorphic. -/
theorem classesPullback_mk_eq_iff {T U : Over S} (h : T ⟶ U) (L : relative A U)
    (M : relative A T) :
    classesPullback A h ⟦L⟧ = ⟦M⟧ ↔
      Nonempty ((Scheme.Modules.pullback (productMap A h)).obj L.obj.carrier ≅
        M.obj.carrier) :=
  ⟨fun H ↦ nonempty_carrierIso_of_mk_eq_mk A H,
    fun ⟨e⟩ ↦ mk_eq_mk_of_carrierIso A (L := (relativePullback A h).obj L) e⟩

end TwoAxisRigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- The structure map of the self-product of an abelian scheme is smooth. -/
instance mumfordProduct_smooth : Smooth (mumfordProduct A).hom := by
  change Smooth (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  infer_instance

/-- The structure map of the self-product of an abelian scheme is proper. -/
instance mumfordProduct_isProper : IsProper (mumfordProduct A).hom := by
  change IsProper (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  infer_instance

/-- The structure map of the self-product of an abelian scheme is flat. -/
instance mumfordProduct_flat : Flat (mumfordProduct A).hom := by
  change Flat (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  infer_instance

/-- The structure map of the self-product of an abelian scheme is geometrically connected. -/
instance mumfordProduct_geometricallyConnected :
    GeometricallyConnected (mumfordProduct A).hom := by
  change GeometricallyConnected (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
  exact GeometricallyConnected.comp _ _

/-- The structure map of the self-product of an abelian scheme is geometrically integral. -/
instance mumfordProduct_geometricallyIntegral :
    GeometricallyIntegral (mumfordProduct A).hom := by
  rw [GeometricallyIntegral.iff_geometricallyIntegral_fiber]
  intro s
  have hs : Smooth ((mumfordProduct A).hom.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hc : GeometricallyConnected ((mumfordProduct A).hom.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact smoothGeometricIntegrality _ _ _ hs hc

/-- Global functions on every affine base change of the self-product of an abelian scheme over
an affine base are the functions on the base. -/
theorem mumfordProduct_appTop_bijective {R : Type u} [CommRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))) (B : Type u) [CommRing B]
    [Algebra R B] :
    Function.Bijective
      (pullback.snd (mumfordProduct A).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop := by
  have := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions _ _
    (pullback.snd (mumfordProduct A).hom (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    inferInstance inferInstance inferInstance ⊤
  exact ConcreteCategory.bijective_of_isIso
    ((pullback.snd (mumfordProduct A).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).app ⊤)

end Langlands.AbelianScheme
