import Langlands.Geometry.Building.KPUnramifiedApartmentLift

/-! # Remaining fields of the concrete unramified comparison -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

private instance unramifiedComparisonFieldsAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

/-- Root comparison along a special-torus apartment lift, including both
filtration containment and descent to the double-root filtration block. -/
def UnramifiedComparisonRootFieldStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ (t : P.UnramifiedComparisonTorus) (L : t.ApartmentLift)
      (a : relativeRoots P.i),
      ∃ (Ψ : Set (characterLattice L.buildingData.S)) (ν : V L.buildingData.S),
        P.IsUnramifiedRootComparison L.buildingData L.e a Ψ ν

/-- The downstairs centralizer lies in an upstairs pairing Levi, and the
upstairs valuations on the roots of that Levi are constant along the lift. -/
def UnramifiedComparisonLeviFieldStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ (t : P.UnramifiedComparisonTorus) (L : t.ApartmentLift),
      ∃ ν : V L.buildingData.S,
        (∀ z : rationalPoints P.centralizer.Z,
          rationalExtend F (UnramifiedClosure F) G (rationalPoints.map P.centralizer.j z) ∈
            L.buildingData.pairingLeviSpan ν) ∧
        ∀ (y y' : P.Apartment), ∀ b ∈ L.buildingData.zeroPairingRoots ν,
          (L.e y).val b = (L.e y').val b

/-- At each lifted point, the depth-zero group restricts on the downstairs
centralizer to its canonical zero subgroup. -/
def UnramifiedComparisonZeroFieldStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ (t : P.UnramifiedComparisonTorus) (L : t.ApartmentLift) (y : P.Apartment),
      ((L.buildingData.moyPrasad L.centralizer_isTorus (L.e y) 0).comap
        (rationalExtend F (UnramifiedClosure F) G)).comap
          (rationalPoints.map P.centralizer.j) = P.centralizerZero

/-- The restrictions of all nonnegative-depth upstairs groups to the downstairs
centralizer are open in its rational-point topology. -/
def UnramifiedComparisonOpenFieldStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ (t : P.UnramifiedComparisonTorus) (L : t.ApartmentLift),
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : IsAffine P.centralizer.Z.X.left := by
        have : IsClosedImmersion P.centralizer.j.hom.hom.left :=
          P.centralizer.isClosedSubgroup
        exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
      letI : TopologicalSpace (rationalPoints P.centralizer.Z) :=
        rationalPointTopology F P.centralizer.Z.X
      ∀ (y : P.Apartment) (r : ℝ≥0),
        IsOpen ((((L.buildingData.moyPrasad L.centralizer_isTorus (L.e y) r).comap
          (rationalExtend F (UnramifiedClosure F) G)).comap
            (rationalPoints.map P.centralizer.j) : Subgroup _) :
          Set (rationalPoints P.centralizer.Z))

set_option maxHeartbeats 1000000 in
/-- The four remaining field targets, special-torus existence and valuation
descent together suffice for the exact published comparison-existence target.
This is a conditional assembly theorem, not a proof of any of its inputs. -/
theorem unramifiedComparisonExistence_of_fields
    (hSpec : SpecialTorusExistenceStatement.{u})
    (hDesc : UnramifiedValuationDescentStatement.{u})
    (hRoot : UnramifiedComparisonRootFieldStatement.{u})
    (hLevi : UnramifiedComparisonLeviFieldStatement.{u})
    (hZero : UnramifiedComparisonZeroFieldStatement.{u})
    (hOpen : UnramifiedComparisonOpenFieldStatement.{u}) :
    UnramifiedComparisonExistenceStatement.{u} := by
  intro F _ _ _ _ G _ P hP
  obtain ⟨t, ⟨L⟩⟩ := exists_unramifiedApartmentLift hSpec hDesc P
  refine ⟨L.buildingData, L.centralizer_isTorus, L.e, ?_⟩
  exact
    { apartmentMap_smul := L.normalizer
      rootComparison := hRoot F G P hP t L
      levi := hLevi F G P hP t L
      comap_zero := hZero F G P hP t L
      isOpen := hOpen F G P hP t L }

end Langlands.Geometry.Building
