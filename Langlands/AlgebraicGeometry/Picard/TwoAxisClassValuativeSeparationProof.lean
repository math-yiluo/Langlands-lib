import Langlands.AlgebraicGeometry.Picard.GenericLineBundleInjectivity
import Langlands.AlgebraicGeometry.Picard.TwoAxisValuationClassSurjectivity
import Langlands.AlgebraicGeometry.Picard.MumfordProductGenericExtension
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassMurreConditionsStatement
import Langlands.CommutativeAlgebra.IntegralFibreProjectivityProof

/-! # Valuative separation (F6) for the two-axis class presheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

namespace TwoAxisRigidifiedLineBundle

open Langlands.AbelianScheme TwoAxisFamily

section Carrier

variable {S X Y Z : Scheme.{u}} {e : S ⟶ X} {t : S ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
  {h : e ≫ i = t ≫ j}

/-- The isomorphism of actual line bundles underlying an isomorphism of two-axis-rigidified
line bundles. -/
def carrierIso {L M : TwoAxisRigidifiedLineBundle e t i j h} (φ : L ≅ M) :
    L.obj.carrier ≅ M.obj.carrier :=
  (TwoAxisRigidifiedModule.forget e t i j h).mapIso ((ObjectProperty.ι _).mapIso φ)

end Carrier

section Separation

/-! The self-product structure morphism of an abelian scheme is smooth, universally closed,
separated and has geometrically connected fibres; these local instances are copied from
`MumfordProductGenericExtension`, where they are also local. -/

local instance {T : Scheme.{u}} (C : Langlands.AbelianScheme T) :
    Smooth (mumfordProduct C).hom := by
  change Smooth (pullback.fst C.X.hom C.X.hom ≫ C.X.hom)
  infer_instance

local instance {T : Scheme.{u}} (C : Langlands.AbelianScheme T) :
    UniversallyClosed (mumfordProduct C).hom := by
  change UniversallyClosed (pullback.fst C.X.hom C.X.hom ≫ C.X.hom)
  infer_instance

local instance {T : Scheme.{u}} (C : Langlands.AbelianScheme T) :
    IsSeparated (mumfordProduct C).hom := by
  change IsSeparated (pullback.fst C.X.hom C.X.hom ≫ C.X.hom)
  infer_instance

local instance {T : Scheme.{u}} (C : Langlands.AbelianScheme T) :
    GeometricallyConnected (mumfordProduct C).hom := by
  change GeometricallyConnected (pullback.fst C.X.hom C.X.hom ≫ C.X.hom)
  exact GeometricallyConnected.comp (pullback.fst C.X.hom C.X.hom) C.X.hom

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

/-- Pulling back along the self-product base-change map agrees with pulling back along the
product map of the composite test object, followed by the comparison `compProductInv`. -/
def compPullbackIso {T : Over S} {W : Scheme.{u}} (b : W ⟶ T.left)
    (N : (mumfordProduct (abelian A T)).left.Modules) :
    (Scheme.Modules.pullback (mumfordProductBaseChangeMap (abelian A T) b)).obj N ≅
      (Scheme.Modules.pullback (compProductInv A b)).obj
        ((Scheme.Modules.pullback (productMap A (compTestHom b))).obj N) :=
  ((Scheme.Modules.pullbackId _).app
      ((Scheme.Modules.pullback (mumfordProductBaseChangeMap (abelian A T) b)).obj N)).symm ≪≫
    (Scheme.Modules.pullbackCongr (compProductInv_hom A b).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp (compProductInv A b) (compProductHom A b)).app _).symm ≪≫
    (Scheme.Modules.pullback (compProductInv A b)).mapIso
      ((Scheme.Modules.pullbackComp (compProductHom A b)
          (mumfordProductBaseChangeMap (abelian A T) b)).app N ≪≫
        (Scheme.Modules.pullbackCongr (compProductHom_baseChangeMap A b)).app N)

/-- Over any valuation ring mapping to the base, class restriction from the valuation ring to
its supplied fraction field is injective. -/
theorem classesPullback_injective_valuationRing (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (i₂ : Spec (CommRingCat.of R) ⟶ S) :
    Function.Injective (classesPullback A
      (compTestHom (T := Over.mk i₂) (Spec.map (CommRingCat.ofHom (algebraMap R K))))) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h L =>
  induction y using Quotient.inductionOn with
  | h M =>
  obtain ⟨φ⟩ := Quotient.exact hxy
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let B := abelian A (Over.mk i₂)
  let P := productMap A (compTestHom (T := Over.mk i₂) b)
  let q := mumfordProductBaseChangeMap B b
  let φc : (Scheme.Modules.pullback P).obj L.obj.carrier ≅
      (Scheme.Modules.pullback P).obj M.obj.carrier :=
    carrierIso φ
  let θ := compPullbackIso A (T := Over.mk i₂) b
  let ψ : (Scheme.Modules.pullback q).obj L.obj.carrier ≅
      (Scheme.Modules.pullback q).obj M.obj.carrier :=
    θ L.obj.carrier ≪≫
      (Scheme.Modules.pullback (compProductInv A (T := Over.mk i₂) b)).mapIso φc ≪≫
      (θ M.obj.carrier).symm
  obtain ⟨f⟩ := nonempty_iso_of_generic_iso (mumfordProduct B).hom K q
    ((mumfordProductBaseChangeIso B b).hom ≫ pullback.snd _ _)
    (isPullback_mumfordProduct_generic K B)
    (affineClosedFibreSectionProjectivity_of_integralFibreProjectivity (mumfordProduct B).hom
      Langlands.CommutativeAlgebra.integralFibreProjectivity)
    (mumfordProduct_generic_app_injective K B) L.property M.property ψ
  obtain ⟨g⟩ := nonempty_iso_of_carrierIso B (L := L) (M := M) f
  exact Quotient.sound ⟨g⟩

end Separation

end TwoAxisRigidifiedLineBundle

open TwoAxisRigidifiedLineBundle in
/-- **Valuative separation (F6).** For every abelian scheme over the spectrum of a noetherian
ring, the two-axis class presheaf is injective on restriction from a discrete valuation ring to
its fraction field. -/
theorem noetherianTwoAxisClassValuativeSeparation :
    NoetherianTwoAxisClassValuativeSeparationStatement.{u} := by
  intro R _ _ A V _ _ _ f
  exact classesPullback_injective_valuationRing A V (FractionRing V) f

end Langlands.AlgebraicGeometry.Picard
