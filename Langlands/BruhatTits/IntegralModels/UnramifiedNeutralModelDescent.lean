import Langlands.BruhatTits.IntegralModels.RelativeComponentConstruction
import Langlands.BruhatTits.IntegralModels.RelativeComponentFunctoriality
import Langlands.Geometry.Building.UnramifiedFixedPointStabilizer

/-! # Exact unramified descent of supplied neutral integral models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.IntegralModel
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- Actual full and neutral unramified recovery, with the pulled-back inclusion
square. Both generic identifications are over the identity of the original group. -/
structure UnramifiedComponentModelRecovery
    (D : RelativeComponentModelData ↥𝒪[F] F G)
    (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G)) where
  fullIso : D.full.baseChangeUnramified.Iso E.full (CategoryTheory.Iso.refl _)
  neutralIso : D.neutral.baseChangeUnramified.Iso E.neutral (CategoryTheory.Iso.refl _)
  inclusion_comm : neutralIso.iso.hom ≫ E.inclusion.hom =
    (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map
      D.inclusion.hom ≫ fullIso.iso.hom

namespace UnramifiedComponentModelRecovery

variable (D : RelativeComponentModelData ↥𝒪[F] F G)
  (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))

/-- A supplied full-model recovery recovers the actual neutral model and its
inclusion, without a separate coefficient-stability assumption on neutral points. -/
def ofFull (e : D.full.baseChangeUnramified.Iso E.full (CategoryTheory.Iso.refl _)) :
    UnramifiedComponentModelRecovery D E where
  fullIso := e
  neutralIso := D.baseChangeNeutralIso (fixedFieldIntegers F) (inertiaFixedField F) E e
  inclusion_comm :=
    D.baseChangeNeutralIso_hom_comp (fixedFieldIntegers F) (inertiaFixedField F) E e

variable {D E} (e : UnramifiedComponentModelRecovery D E)

include e

/-- Literal equality of the original upstairs full-model image subgroups. -/
theorem full_integralPoints_eq :
    D.full.baseChangeUnramified.integralPoints = E.full.integralPoints :=
  e.fullIso.integralPoints_eq

/-- Literal equality of the original upstairs neutral-model image subgroups. -/
theorem neutral_integralPoints_eq :
    D.neutral.baseChangeUnramified.integralPoints = E.neutral.integralPoints :=
  e.neutralIso.integralPoints_eq

/-- The original downstairs full-model image is the exact inverse image of the
supplied upstairs full-model image under rational scalar extension. -/
theorem full_integralPoints_eq_comap :
    D.full.integralPoints = E.full.integralPoints.comap
      (rationalExtend F (inertiaFixedField F) G) := by
  rw [D.full.integralPoints_eq_comap_baseChangeUnramified, e.full_integralPoints_eq]

/-- The same exact inverse-image assertion holds for the neutral model. -/
theorem neutral_integralPoints_eq_comap :
    D.neutral.integralPoints = E.neutral.integralPoints.comap
      (rationalExtend F (inertiaFixedField F) G) := by
  rw [D.neutral.integralPoints_eq_comap_baseChangeUnramified, e.neutral_integralPoints_eq]

/-- Neutral coefficient stability follows from the recovered model. -/
theorem neutral_galois_stable
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    {g : rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hg : g ∈ E.neutral.integralPoints) :
    rationalConjugate F (inertiaFixedField F) G σ g ∈ E.neutral.integralPoints :=
  galois_stable_of_iso_baseChangeUnramified D.neutral e.neutralIso σ hg

end UnramifiedComponentModelRecovery

/-- Conditional on smooth full-model descent, a supplied stable full model and
its relative component descend together with exact compatible recovery. -/
theorem exists_unramified_componentModelRecovery
    (hdescent : UnramifiedSmoothModelDescentStatement.{u})
    (hG : GeometricallyConnected G.X.hom)
    (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ g ∈ E.full.integralPoints,
        rationalConjugate F (inertiaFixedField F) G σ g ∈ E.full.integralPoints) :
    ∃ D : RelativeComponentModelData ↥𝒪[F] F G,
      Nonempty (UnramifiedComponentModelRecovery D E) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hdescent F G E.full E.full_smooth hstable
  let D := M.relativeComponentModelDataOfSmooth hM hG
  refine ⟨D, ⟨UnramifiedComponentModelRecovery.ofFull D E ?_⟩⟩
  simpa only [D, IntegralModel.relativeComponentModelDataOfSmooth_full] using e

/-- At any fixed point of an actual semilinear action, a supplied full model
with the character-kernel stabilizer as its image admits the same conditional
full and neutral descent. -/
theorem exists_unramified_componentModelRecovery_of_fixedPoint
    (hdescent : UnramifiedSmoothModelDescentStatement.{u})
    (hG : GeometricallyConnected G.X.hom)
    {Y : Type u}
    [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    (ρ : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* Equiv.Perm Y)
    (hρ : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (z : Y),
      ρ σ (g • z) = rationalConjugate F (inertiaFixedField F) G σ g • ρ σ z)
    (y : Y) (hy : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, ρ σ y = y)
    (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (himage : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        MulAction.stabilizer (rationalPoints (baseChanged F (inertiaFixedField F) G)) y) :
    ∃ D : RelativeComponentModelData ↥𝒪[F] F G,
      Nonempty (UnramifiedComponentModelRecovery D E) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_descent_of_fixedPoint_integralPoints
    hdescent G ρ hρ y hy E.full E.full_smooth himage
  let D := M.relativeComponentModelDataOfSmooth hM hG
  refine ⟨D, ⟨UnramifiedComponentModelRecovery.ofFull D E ?_⟩⟩
  simpa only [D, IntegralModel.relativeComponentModelDataOfSmooth_full] using e

/-- Exact full and neutral recovery from the smooth-model descent assertion,
for supplied component data with a coefficient-stable full-model image. -/
def UnramifiedNeutralModelDescentStatement : Prop :=
  UnramifiedSmoothModelDescentStatement.{u} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    GeometricallyConnected G.X.hom →
    ∀ E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G),
    (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ g ∈ E.full.integralPoints,
        rationalConjugate F (inertiaFixedField F) G σ g ∈ E.full.integralPoints) →
    ∃ D : RelativeComponentModelData ↥𝒪[F] F G,
      Nonempty (UnramifiedComponentModelRecovery D E)

/-- Proof using actual smooth full-model descent and relative-component recovery. -/
theorem unramifiedNeutralModelDescent : UnramifiedNeutralModelDescentStatement.{u} := by
  intro hdescent F _ _ _ _ G hG E hstable
  exact exists_unramified_componentModelRecovery hdescent hG E hstable

end Langlands.BruhatTits.IntegralModels
