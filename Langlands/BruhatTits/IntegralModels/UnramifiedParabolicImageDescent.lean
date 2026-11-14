import Langlands.BruhatTits.IntegralModels.UnramifiedComponentModelComparison
import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.IntegralModel.UnramifiedSpecialFibreImage

/-! # Parabolic images of recovered neutral models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.IntegralModel
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

local instance recoveredImage_integerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance recoveredImage_integerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

namespace UnramifiedComponentModelRecovery

variable {D₀ D₁ : RelativeComponentModelData ↥𝒪[F] F G}
  {E₀ E₁ : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G)}
  (e₀ : UnramifiedComponentModelRecovery D₀ E₀)
  (e₁ : UnramifiedComponentModelRecovery D₁ E₁)

/-- The recovery identifies the actual neutral special fibres over the
residue field of the maximal-unramified integers. -/
def neutralSpecialFibreIso :
    D₀.neutral.baseChangeUnramified.specialFibre ≅ E₀.neutral.specialFibre :=
  (GroupScheme.baseChange (IntegralModel.residueBaseMap (fixedFieldIntegers F))).mapIso
    e₀.neutralIso.iso

/-- The neutral recovery square remains commutative on the actual special
fibres, for any supplied downstairs and upstairs comparisons. -/
theorem neutral_specialFibre_comparison_comm
    (φ : RelativeComponentModelHom D₀ D₁) (ψ : RelativeComponentModelHom E₀ E₁) :
    (φ.neutral.baseChangeCoefficients (fixedFieldIntegers F)
        (inertiaFixedField F)).specialFibreMap ≫ e₁.neutralSpecialFibreIso.hom =
      e₀.neutralSpecialFibreIso.hom ≫ ψ.neutralSpecialFibreMap := by
  simpa only [Functor.map_comp, neutralSpecialFibreIso, Functor.mapIso_hom,
    IntegralModel.Hom.specialFibreMap, IntegralModel.Hom.baseChangeCoefficients_hom] using
    congrArg
      (GroupScheme.baseChange (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
      (e₀.neutral_comparison_comm e₁ φ ψ)

/-- The actual image of the extended downstairs comparison is the actual
image of the supplied upstairs comparison, through the recovery square. -/
def specialFibreImageIso
    (φ : RelativeComponentModelHom D₀ D₁) (ψ : RelativeComponentModelHom E₀ E₁) :
    SchematicImage.image (φ.neutral.baseChangeCoefficients (fixedFieldIntegers F)
      (inertiaFixedField F)).specialFibreMap ≅ ψ.specialFibreImage :=
  SchematicImage.isoOfIsoSquare _ _
    e₀.neutralSpecialFibreIso e₁.neutralSpecialFibreIso
    (e₀.neutral_specialFibre_comparison_comm e₁ φ ψ)

/-- The recovered image isomorphism preserves its ambient inclusion. -/
theorem specialFibreImageIso_hom_comp
    (φ : RelativeComponentModelHom D₀ D₁) (ψ : RelativeComponentModelHom E₀ E₁) :
    (e₀.specialFibreImageIso e₁ φ ψ).hom ≫ ψ.specialFibreImageInclusion =
      SchematicImage.inclusion (φ.neutral.baseChangeCoefficients (fixedFieldIntegers F)
        (inertiaFixedField F)).specialFibreMap ≫ e₁.neutralSpecialFibreIso.hom :=
  SchematicImage.isoOfIsoSquare_hom_comp _ _ _ _ _

include e₀ e₁ in
/-- Parabolicity of the supplied upstairs neutral-model image descends to
every compatible downstairs comparison with the specified recoveries. -/
theorem hasParabolicSpecialFibreImage
    (φ : RelativeComponentModelHom D₀ D₁) (ψ : RelativeComponentModelHom E₀ E₁)
    (hψ : ψ.HasParabolicSpecialFibreImage) :
    φ.HasParabolicSpecialFibreImage := by
  apply φ.neutral.isParabolic_specialFibreImage_of_unramified
  have hnat : ψ.neutralSpecialFibreMap ≫ e₁.neutralSpecialFibreIso.inv =
      e₀.neutralSpecialFibreIso.inv ≫
        (φ.neutral.baseChangeCoefficients (fixedFieldIntegers F)
          (inertiaFixedField F)).specialFibreMap := by
    apply (cancel_mono e₁.neutralSpecialFibreIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [e₀.neutral_specialFibre_comparison_comm e₁ φ ψ, Iso.inv_hom_id_assoc]
  exact SchematicImage.isParabolic_inclusion_of_isoSquare _ _
    e₀.neutralSpecialFibreIso.symm e₁.neutralSpecialFibreIso.symm hnat hψ

end UnramifiedComponentModelRecovery

end Langlands.BruhatTits.IntegralModels
