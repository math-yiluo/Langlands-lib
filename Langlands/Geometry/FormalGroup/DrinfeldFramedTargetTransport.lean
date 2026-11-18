import Langlands.Geometry.FormalGroup.DrinfeldFramedIdentityComparison

/-! # Actual target-isomorphism transport of framed formal atlases -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable (X : DrinfeldFramedAtlas Φ A)

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable (Y : SpecialAtlas.HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := A.obj) π)
variable {h : X.target.val.atlas.opens = Y.val.atlas.opens}

/-- The same actual fixed frame on the two equal reduced target covers. -/
def targetTransportSourceIso (_t : X.target.val.Iso Y.val h) :
    BasicAtlas.OrderAction.Iso X.source.order
      (SpecialAtlas.quotientFrame Φ.val X.residueMap Y.val).order
      (BasicAtlas.reductionOpens_eq h) :=
  BasicAtlas.globalCoverOrderIsoOfCoverEq (Φ.val.order.map X.residueMap)
    X.target.val.reduction.atlas.opens Y.val.reduction.atlas.opens
    X.target.val.reduction.atlas.covers Y.val.reduction.atlas.covers
    (BasicAtlas.reductionOpens_eq h)

set_option maxHeartbeats 1000000 in
/-- Replace the actual target using an integral isomorphism, transporting both whole rational framing maps. -/
def transportTarget (t : X.target.val.Iso Y.val h) : DrinfeldFramedAtlas Φ A where
  residueMap := X.residueMap
  target := Y
  rho := X.rho.isoTransport (X.targetTransportSourceIso Y t) t.reduction
  height_zero := X.rho.isoTransport_height (X.targetTransportSourceIso Y t) t.reduction X.height_zero

@[simp]
theorem transportTarget_residueMap (t : X.target.val.Iso Y.val h) :
    (X.transportTarget Y t).residueMap = X.residueMap := rfl

@[simp]
theorem transportTarget_target (t : X.target.val.Iso Y.val h) :
    (X.transportTarget Y t).target = Y := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Source cover transport has complete identity formal series on every original reduced test. -/
theorem targetTransportSourceIso_hom_coordinates (t : X.target.val.Iso Y.val h)
    (C : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : Y.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj C b.val)) :
    ((X.targetTransportSourceIso Y t).hom.val.hom C b hb).toHom.toCoordinateMap = CoordinateMap.id :=
  BasicAtlas.globalCoverOrderIsoOfCoverEq_hom_coordinates _ _ _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The specified source and target maps give the whole global rational framing square. -/
theorem transportTarget_rho (t : X.target.val.Iso Y.val h) :
    X.rho.trans (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) t.reduction) =
      (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.targetTransportSourceIso Y t)).trans
        (X.transportTarget Y t).rho := by
  change X.rho.trans (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) t.reduction) =
    (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := K) (X.targetTransportSourceIso Y t)).trans
      (X.rho.isoTransport (X.targetTransportSourceIso Y t) t.reduction)
  simp only [BasicAtlas.OrderAction.QuasiIsogeny.isoTransport,
    ← BasicAtlas.OrderAction.QuasiIsogeny.trans_assoc,
    BasicAtlas.OrderAction.QuasiIsogeny.self_trans_symm,
    BasicAtlas.OrderAction.QuasiIsogeny.refl_trans]

/-- The exact target comparison induced by the specified actual integral target isomorphism. -/
def targetTransportTargetComparison (t : X.target.val.Iso Y.val h) :
    SpecialAtlas.Comparison X.target.val Y.val :=
  BasicAtlas.OrderAction.Comparison.ofIso t (BasicAtlas.CoverRefinement.refl _)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Target transport compares in the original framed relation, with its original all-test square proved. -/
def targetTransportComparison (t : X.target.val.Iso Y.val h) :
    Comparison X (X.transportTarget Y t) where
  targetComparison := X.targetTransportTargetComparison Y t
  residue_eq := rfl
  square := ReducedFramingSquare.of_induced_global_square
    (X := X) (Y := X.transportTarget Y t) rfl
    (SpecialAtlas.reductionComparison (X.targetTransportTargetComparison Y t))
    t.reduction (X.targetTransportSourceIso Y t)
    (SpecialAtlas.inducedBy_reduction (X.targetTransportTargetComparison Y t) t
      (BasicAtlas.OrderAction.Comparison.inducedBy_ofIso t (BasicAtlas.CoverRefinement.refl _)))
    (X.targetTransportSourceIso_hom_coordinates Y t) (X.transportTarget_rho Y t)

/-- The original induced target comparison is retained exactly. -/
@[simp]
theorem targetTransportComparison_targetComparison (t : X.target.val.Iso Y.val h) :
    (X.targetTransportComparison Y t).targetComparison = X.targetTransportTargetComparison Y t := rfl

/-- Canonical actual target transport retains the SAME original framed comparison class. -/
theorem comparisonClassOf_transportTarget (t : X.target.val.Iso Y.val h) :
    comparisonClassOf (X.transportTarget Y t) = comparisonClassOf X :=
  (comparisonClassOf_eq_of_comparison (X.targetTransportComparison Y t)).symm

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
