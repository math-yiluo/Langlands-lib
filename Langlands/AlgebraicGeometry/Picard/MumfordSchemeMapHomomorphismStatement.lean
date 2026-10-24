import Langlands.AlgebraicGeometry.Picard.MumfordMap
import Langlands.AlgebraicGeometry.Picard.DualSchemeTensor
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The homomorphism equations for the actual Mumford map -/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The constructed Mumford map preserves the actual unit and multiplication.
This fixed-data predicate is defined over every base scheme. -/
def MumfordSchemeMapHomomorphism
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
    (hA : HasDualScheme A) : Prop :=
  let f := mumfordSchemeMap preservation square A L M evaluation hA
  (η[A.X] ≫ f =
    (Over.homMk (MonoidalCategory.tensorUnit (Over S)).hom :
      MonoidalCategory.tensorUnit (Over S) ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) ∧
  (μ[A.X] ≫ f =
    prod.lift (CartesianMonoidalCategory.fst A.X A.X ≫ f)
      (CartesianMonoidalCategory.snd A.X A.X ≫ f) ≫
        dualTensor stability A hA preservation)

/-- The actual Mumford classifying morphism is a homomorphism over a
quasi-separated base, retaining the source's convention on schemes. -/
def RelativeMumfordSchemeMapHomomorphismStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (L : RigidifiedLineBundle (unitSection A)) (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left)
    (hA : HasDualScheme A),
    MumfordSchemeMapHomomorphism preservation stability square A L M evaluation hA

end Langlands.AbelianScheme
