import Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement
import Langlands.Geometry.Building.Kottwitz.FundamentalGroupStatement

/-! # Inputs and formal reduction for reductive Kottwitz descent -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- The torus equivariance input over every coefficient-field tower used by the
reductive descent target. It makes no rational surjectivity assertion. -/
def GeneralTorusKottwitzEquivarianceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)]
    [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (σ : UnramifiedClosure F ≃ₐ[k] UnramifiedClosure F) (x : torusKPoints F k T),
    (torusKottwitz F k T hT
      (GaloisPoint.conjugate k (UnramifiedClosure F) T.toGrp σ x)).toAdd =
    torusGammaRepresentation k (UnramifiedClosure F) (SeparableClosure F) T σ
      (torusKottwitz F k T hT x).toAdd

/-- The rational restriction step is formal once equivariance of the selected
K-point map has been established. -/
def ReductiveKottwitzRationalRestrictionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    ReductiveKottwitzEquivariant F G hG →
    (∃! κ, IsReductiveKottwitzRestriction F G hG κ) ∧
    IsReductiveKottwitzRestriction F G hG (reductiveKottwitzRational F G hG)

/-- Cocenter comparison and point-surjective z-extensions reduce the exact
reductive descent target to five explicit inputs. -/
def ReductiveKottwitzDescentReductionStatement : Prop :=
  SimplyConnectedDerivedKottwitzStatement.{u} →
  ReductiveKottwitzExistenceStatement.{u} →
  FundamentalInertiaMapStatement.{u} →
  TorusInertiaComparisonStatement.{u} →
  GeneralTorusKottwitzEquivarianceStatement.{u} →
  ReductiveKottwitzDescentStatement.{u}

end Langlands.Geometry.Building.Kottwitz
