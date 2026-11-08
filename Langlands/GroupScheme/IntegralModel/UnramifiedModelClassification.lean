import Langlands.GroupScheme.IntegralModel.LocalReductivity
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.IntegerBuildingModelIsoTransport
import Langlands.GroupScheme.Reductive.StrictHenselianGenericIsoStatement

/-! # Strictly Henselian classification for the original unramified model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance unramifiedModelClassificationAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedModelClassificationScalarTower : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- Reductivity of the original good local model persists on its actual
maximal-unramified integer base change. -/
theorem isReductive_baseChangeUnramified
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group)) :
    IsReductive M.baseChangeUnramified.group :=
  (M.isReductive_of_reductive_localField hG hSpecial).baseChange
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))

/-- Instantiate a supplied strict-Henselian classification theorem on the actual
unramified integer ring and both original generic identifications. The resulting
integral isomorphism is abstract, with no prescribed generic map. -/
def unramifiedModelGroupIso
    (hclassification : StrictHenselianGenericIsoStatement.{u})
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hN : IsReductive N.group) :
    N.group ≅ M.baseChangeUnramified.group := by
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  exact Classical.choice (hclassification (fixedFieldIntegers F) (inertiaFixedField F)
    N.group M.baseChangeUnramified.group hN
    (M.isReductive_baseChangeUnramified hG hSpecial)
    ⟨N.genericIso ≪≫ M.baseChangeUnramified.genericIso.symm⟩)

/-- The actual generic automorphism determined by the classified integral
isomorphism and the two supplied generic identifications. -/
def unramifiedModelGenericIso
    (hclassification : StrictHenselianGenericIsoStatement.{u})
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hN : IsReductive N.group) :
    baseChanged F (inertiaFixedField F) G ≅ baseChanged F (inertiaFixedField F) G :=
  N.inducedGenericIso M.baseChangeUnramified
    (M.unramifiedModelGroupIso hclassification hG hSpecial N hN)

/-- A compatible model isomorphism over precisely the induced generic
automorphism, retaining the original unramified model. -/
def unramifiedModelIso
    (hclassification : StrictHenselianGenericIsoStatement.{u})
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hN : IsReductive N.group) :
    N.Iso M.baseChangeUnramified
      (M.unramifiedModelGenericIso hclassification hG hSpecial N hN) :=
  Iso.ofGroupIso N M.baseChangeUnramified
    (M.unramifiedModelGroupIso hclassification hG hSpecial N hN)

section Building

variable [IsAffineHom G.X.hom]

private instance unramifiedAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- Classification plus an actual source comparison identifies the original
unramified-model image on the same transported integer-building quotient. -/
theorem integralPoints_eq_oneStabilizer_classifiedUnramified
    (hclassification : StrictHenselianGenericIsoStatement.{u})
    (hG : IsConnectedReductive G)
    (hSpecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group))
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hN : IsReductive N.group)
    (B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (x : B.ReducedBuilding) (hpoints : N.integralPoints = B.oneStabilizer x) :
    M.baseChangeUnramified.integralPoints =
      (B.mapIso (M.unramifiedModelGenericIso hclassification hG hSpecial N hN)).oneStabilizer
        (B.mapIsoReducedBuildingEquiv
          (M.unramifiedModelGenericIso hclassification hG hSpecial N hN) x) :=
  (M.unramifiedModelIso hclassification hG hSpecial N hN
    ).integralPoints_eq_oneStabilizer_mapIso B x hpoints

end Building

end Langlands.GroupScheme.IntegralModel
