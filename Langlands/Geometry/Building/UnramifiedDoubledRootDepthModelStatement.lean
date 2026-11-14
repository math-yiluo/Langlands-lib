import Langlands.Geometry.Building.KPUnramifiedApartmentLift
import Langlands.Geometry.Building.RootDepthTorusRestriction
import Langlands.GroupScheme.LocalUnramifiedIntegralCocycle
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability

/-! # Integral models for doubled-root depth subgroups of apartment lifts -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance doubledRootDepthModelAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

/-- Internal model prerequisite for depth-preserving doubled-root correction.
The comparison concerns all points over the maximal unramified extension. -/
def UnramifiedDoubledRootDepthModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ (t : P.UnramifiedComparisonTorus) (L : t.ApartmentLift)
      (y : P.Apartment) (a : relativeRoots P.i),
      2 • a.val ∈ relativeRoots P.i →
      ∀ (U : GroupScheme (Spec (CommRingCat.of F))) (q : U ⟶ G),
        (RelativeRoot.subgroup P.i (2 • a.val)).IsRepresentedBy q →
        IsClosedSubgroup q →
        ∀ s : ℝ≥0, ∃ M : IntegralModel 𝒪[F] F U,
          M.IsSmooth ∧
          ConnectedSpace
            ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left ∧
          ∀ x : rationalPoints (baseChanged F (UnramifiedClosure F) U),
            M.HasIntegralCoordinates (UnramifiedClosure F)
                (baseChangeCoeffEquiv F (UnramifiedClosure F) U x) ↔
              rationalPoints.map
                  ((GroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map q) x ∈
                torusRestrictedRootDepthSubgroup
                  (L.apartment.isRootDatumValuation_of_mem (L.e y).mem)
                  ((CommGroupScheme.baseChange
                    (algebraBaseMap F (UnramifiedClosure F))).map t.f)
                  (characterLattice.baseChange
                    (algebraBaseMap F (UnramifiedClosure F)) P.S (2 • a.val)) s

end Langlands.Geometry.Building
