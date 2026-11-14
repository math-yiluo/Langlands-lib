import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralModelDescent
import Langlands.GroupScheme.IntegralModel.SmoothHomExtension

/-! # Coherent comparisons between recovered component models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

section IdentityBaseChange

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {M N : IntegralModel R K G}
  (φ : M.Hom N (𝟙 G))
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

/-- Pull back a generic-identity comparison, retaining literally its actual
pullback as the underlying map. -/
def Hom.baseChangeIdentity : (M.baseChange A L).Hom (N.baseChange A L)
    (𝟙 ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G)) where
  hom := (GroupScheme.baseChange (Spec.algebraMap R A)).map φ.hom
  generic_comm := by
    simpa only [Hom.baseChangeCoefficients_hom, CategoryTheory.Functor.map_id] using
      (φ.baseChangeCoefficients A L).generic_comm

end IdentityBaseChange

open Langlands.LocalGalois.Separable GaloisPointComparison

/-- Conditional generic-identity extension is equivalent to inclusion of the
actual unramified integral-point images. -/
theorem nonempty_identityHom_iff_unramified_integralPoints_le
    (hext : UnramifiedSmoothHomExtensionStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (M N : IntegralModel ↥𝒪[F] F G) (hM : M.IsSmooth) :
    Nonempty (M.Hom N (𝟙 G)) ↔
      M.baseChangeUnramified.integralPoints ≤ N.baseChangeUnramified.integralPoints := by
  constructor
  · rintro ⟨φ⟩ g hg
    simpa only [CategoryTheory.Functor.map_id, rationalPoints.map_apply,
      Grp.id_hom_hom, Category.comp_id] using φ.unramifiedIntegralPoints_map_le g hg
  · intro hle
    apply hext F G G (𝟙 G) M N hM
    intro g hg
    simpa only [CategoryTheory.Functor.map_id, rationalPoints.map_apply,
      Grp.id_hom_hom, Category.comp_id] using hle hg

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.GroupScheme.IntegralModel
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable

section Uniqueness

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {D E : RelativeComponentModelData R K G}

/-- The compatible full and neutral comparison package is unique. -/
instance : Subsingleton (RelativeComponentModelHom D E) where
  allEq φ ψ := by
    cases φ with
    | mk φf φn φc =>
      cases ψ with
      | mk ψf ψn ψc =>
        have hf : φf = ψf := Subsingleton.elim _ _
        have hn : φn = ψn := Subsingleton.elim _ _
        cases hf
        cases hn
        rfl

end Uniqueness

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

namespace UnramifiedComponentModelRecovery

variable {D₀ D₁ : RelativeComponentModelData ↥𝒪[F] F G}
  {E₀ E₁ : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G)}
  (e₀ : UnramifiedComponentModelRecovery D₀ E₀)
  (e₁ : UnramifiedComponentModelRecovery D₁ E₁)

include e₀ e₁

/-- Inclusion of recovered full-model images is exactly the criterion for a
compatible full and neutral comparison, conditional on unramified Hom extension. -/
theorem nonempty_comparison_iff
    (hext : UnramifiedSmoothHomExtensionStatement.{u}) :
    Nonempty (RelativeComponentModelHom D₀ D₁) ↔
      E₀.full.integralPoints ≤ E₁.full.integralPoints := by
  constructor
  · rintro ⟨φ⟩
    rw [← e₀.full_integralPoints_eq, ← e₁.full_integralPoints_eq]
    exact (nonempty_identityHom_iff_unramified_integralPoints_le hext
      D₀.full D₁.full D₀.full_smooth).mp ⟨φ.full⟩
  · intro hle
    have hle' : D₀.full.baseChangeUnramified.integralPoints ≤
        D₁.full.baseChangeUnramified.integralPoints := by
      rw [e₀.full_integralPoints_eq, e₁.full_integralPoints_eq]
      exact hle
    obtain ⟨φ⟩ := (nonempty_identityHom_iff_unramified_integralPoints_le hext
      D₀.full D₁.full D₀.full_smooth).mpr hle'
    exact ⟨RelativeComponentModelHom.ofFull φ⟩

/-- The analogous criterion for the actual neutral-model comparison alone. -/
theorem nonempty_neutralHom_iff
    (hext : UnramifiedSmoothHomExtensionStatement.{u}) :
    Nonempty (D₀.neutral.Hom D₁.neutral (𝟙 G)) ↔
      E₀.neutral.integralPoints ≤ E₁.neutral.integralPoints := by
  rw [nonempty_identityHom_iff_unramified_integralPoints_le hext
    D₀.neutral D₁.neutral D₀.neutral_smooth,
    e₀.neutral_integralPoints_eq, e₁.neutral_integralPoints_eq]

/-- Any supplied upstairs comparison and compatible downstairs comparison give
literally the same full-model map after recovery. -/
theorem full_comparison_comm
    (φ : RelativeComponentModelHom D₀ D₁) (ψ : RelativeComponentModelHom E₀ E₁) :
    (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map
        φ.full.hom ≫ e₁.fullIso.iso.hom = e₀.fullIso.iso.hom ≫ ψ.full.hom := by
  exact ((φ.full.baseChangeIdentity (fixedFieldIntegers F) (inertiaFixedField F)).comp
    e₁.fullIso.toHom).hom_eq (e₀.fullIso.toHom.comp ψ.full)

/-- The original neutral-model map is recovered simultaneously. -/
theorem neutral_comparison_comm
    (φ : RelativeComponentModelHom D₀ D₁) (ψ : RelativeComponentModelHom E₀ E₁) :
    (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map
        φ.neutral.hom ≫ e₁.neutralIso.iso.hom = e₀.neutralIso.iso.hom ≫ ψ.neutral.hom := by
  exact ((φ.neutral.baseChangeIdentity (fixedFieldIntegers F) (inertiaFixedField F)).comp
    e₁.neutralIso.toHom).hom_eq (e₀.neutralIso.toHom.comp ψ.neutral)

/-- A supplied actual upstairs comparison descends uniquely, conditional on
unramified Hom extension, and both recovery squares commute. -/
theorem existsUnique_comparison
    (hext : UnramifiedSmoothHomExtensionStatement.{u})
    (ψ : RelativeComponentModelHom E₀ E₁) :
    ∃! φ : RelativeComponentModelHom D₀ D₁,
      (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map
          φ.full.hom ≫ e₁.fullIso.iso.hom = e₀.fullIso.iso.hom ≫ ψ.full.hom ∧
        (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map
          φ.neutral.hom ≫ e₁.neutralIso.iso.hom = e₀.neutralIso.iso.hom ≫ ψ.neutral.hom := by
  obtain ⟨φ⟩ := (e₀.nonempty_comparison_iff e₁ hext).mpr ψ.full_integralPoints_le
  exact ⟨φ, ⟨e₀.full_comparison_comm e₁ φ ψ, e₀.neutral_comparison_comm e₁ φ ψ⟩,
    fun _ _ => Subsingleton.elim _ _⟩

end UnramifiedComponentModelRecovery

/-- Conditional coherent comparison for recovered full and neutral integral
models, retaining each actual upstairs map and both recovery squares. -/
def UnramifiedComponentModelComparisonStatement : Prop :=
  UnramifiedSmoothHomExtensionStatement.{u} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (D₀ D₁ : RelativeComponentModelData ↥𝒪[F] F G)
    (E₀ E₁ : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (e₀ : UnramifiedComponentModelRecovery D₀ E₀)
    (e₁ : UnramifiedComponentModelRecovery D₁ E₁)
    (ψ : RelativeComponentModelHom E₀ E₁),
    ∃! φ : RelativeComponentModelHom D₀ D₁,
      (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map
          φ.full.hom ≫ e₁.fullIso.iso.hom = e₀.fullIso.iso.hom ≫ ψ.full.hom ∧
        (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map
          φ.neutral.hom ≫ e₁.neutralIso.iso.hom = e₀.neutralIso.iso.hom ≫ ψ.neutral.hom

/-- Proof of coherent comparison using image inclusion and generic rigidity. -/
theorem unramifiedComponentModelComparison : UnramifiedComponentModelComparisonStatement.{u} := by
  intro hext F _ _ _ _ G D₀ D₁ E₀ E₁ e₀ e₁ ψ
  exact e₀.existsUnique_comparison e₁ hext ψ

end Langlands.BruhatTits.IntegralModels
