import Langlands.Geometry.Building.IntegerValuationOneStabilizerBounded
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness

/-! # Boundedness of one-stabilizers over the unramified field -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.MaximalUnramified

private instance oneStabilizerBoundednessAffine
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom] : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Input statement: for supplied building data over the actual inertia fixed field `K`,
the image `j(Z(K)^1)` of the norm-one subgroup of the centralizer `Z = Z_G(S)` is
algebraically bounded in `G`. This is an unproved input proposition. -/
def CentralizerNormOneBoundedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (C : BuildingData F G),
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    IsAlgebraicallyBounded (inertiaFixedField F) G.X
      (rationalPoints.map C.centralizer.j ''
        (characterValuationKernel (valuation F) C.centralizer.Z :
          Set (rationalPoints C.centralizer.Z)))

/-- Input statement: for supplied building data over the actual inertia fixed field `K`,
every depth-zero filtration subgroup `U_{a,x,0}` of a relative root group at a point `x` of
the apartment is algebraically bounded in `G`. This is an unproved input proposition. -/
def ZeroRootFiltrationBoundedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (C : BuildingData F G) (x : C.Apartment),
    ∀ a ∈ relativeRoots C.i,
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    IsAlgebraicallyBounded (inertiaFixedField F) G.X
      (C.filtration x a 0 : Set (rationalPoints G))

/-- The boundedness half of KP Theorem 4.2.15(1) over the actual inertia fixed field `K`:
every one-stabilizer `K_y = G(K)^1 ∩ G(K)_y` of a point of the reduced building is
algebraically bounded. -/
def OneStabilizerBoundedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom] (C : BuildingData F G) (y : C.ReducedBuilding),
    letI := ValuativeRel.ofValuation (fixedFieldValued F).v
    IsAlgebraicallyBounded (inertiaFixedField F) G.X
      (C.oneStabilizer y : Set (rationalPoints G))

/-- The two input statements give boundedness of every one-stabilizer over `K`. -/
theorem oneStabilizerBounded_of_centralizer_of_zeroRootFiltration
    (hZ : CentralizerNormOneBoundedStatement.{u})
    (hU : ZeroRootFiltrationBoundedStatement.{u}) :
    OneStabilizerBoundedStatement.{u} := by
  intro F _ _ _ _ G _ C y
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  exact C.isAlgebraicallyBounded_oneStabilizer (hZ F G C) (fun x a ha => hU F G C x a ha) y

end Langlands.Geometry.Building.MaximalUnramified
