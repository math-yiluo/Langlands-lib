import Langlands.AlgebraicGeometry.Modules.PushforwardComparisonZero
import Langlands.Geometry.Analytic.EtaleCoveringPoints.Proof
import Langlands.Geometry.Analytic.EtaleFiniteSubcovers
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof
import Langlands.Sheaf.Equivariant.AnalyticEtaleFiniteGlobalSections

/-! # Degree-zero comparison on compact analytic étale sites -/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.AnalyticEtaleGlobalComparison

open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic Langlands.Sheaf.Equivariant.TwistedOver

open ExactBaseChange in
private theorem isIso_baseChangeNatTrans_zero
    {C₁ C₂ D₁ D₂ : Type*}
    [Category* C₁] [Abelian C₁] [HasInjectiveResolutions C₁]
    [Category* C₂] [Abelian C₂] [HasInjectiveResolutions C₂]
    [Category* D₁] [Abelian D₁] [Category* D₂] [Abelian D₂]
    {F₁ : C₁ ⥤ D₁} [F₁.Additive]
    {F₂ : C₂ ⥤ D₂} [F₂.Additive] [PreservesFiniteLimits F₂]
    {α : C₁ ⥤ C₂} [α.Additive] [PreservesFiniteLimits α] [α.PreservesHomology]
    {β : D₁ ⥤ D₂} [β.Additive] [PreservesFiniteLimits β] [β.PreservesHomology]
    (τ : F₁ ⋙ β ⟶ α ⋙ F₂) [IsIso τ] :
    IsIso (ExactBaseChange.baseChangeNatTrans τ 0) := by
  have : IsIso (compComparisonNatTrans α F₂ 0) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro A
    rw [compComparisonNatTrans_app]
    infer_instance
  have : IsIso (NatTrans.rightDerived τ 0) := by
    refine ⟨⟨NatTrans.rightDerived (inv τ) 0, ?_, ?_⟩⟩
    · rw [← NatTrans.rightDerived_comp, IsIso.hom_inv_id, NatTrans.rightDerived_id]
    · rw [← NatTrans.rightDerived_comp, IsIso.inv_hom_id, NatTrans.rightDerived_id]
  unfold ExactBaseChange.baseChangeNatTrans
  infer_instance

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- On a compact analytic space, the étale smooth-global-section inclusion is invertible. -/
theorem isIso_etaleGlobalInclusion_of_compactSpace (hX : IsCompactSpace X) :
    IsIso (etaleGlobalInclusion.{u, v, uL} ρ R) := by
  apply isIso_etaleGlobalInclusion_of_finiteBaseSubcovers
  exact exists_finite_twistedEtale_base_subcover ρ hX
    (fun U => etaleOpenMap K U.hom U.prop) (etaleCoveringPoints (K := K) X)

variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The canonical étale cohomology comparison in degree zero is invertible for compact `X`. -/
theorem isIso_etaleComparison_zero_of_compactSpace (hX : IsCompactSpace X) :
    IsIso (etaleComparison.{u, v, uL} ρ R 0) := by
  have := etale_hasSheafify.{u, v, uL} X R
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  have := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  have := etale_enoughInjectives.{u, v, uL} X R
  have := etaleGSheafRestriction_preservesFiniteLimits.{u, v, uL} ρ R
  have := etaleGSheafRestriction_preservesFiniteColimits.{u, v, uL} ρ R
  have := isIso_etaleGlobalInclusion_of_compactSpace.{u, v, uL, z} ρ R hX
  exact isIso_baseChangeNatTrans_zero (etaleGlobalInclusion.{u, v, uL} ρ R)

/-- The degree-zero isomorphism induced by the canonical comparison for compact `X`. -/
noncomputable def etaleComparisonZeroIsoOfCompactSpace (hX : IsCompactSpace X) :
    etaleGSheafCohomology.{u, v, uL} ρ R 0 ⋙ smoothForget R G ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCohomology.{u, v, uL} X R 0 := by
  haveI := isIso_etaleComparison_zero_of_compactSpace.{u, v, uL, z} ρ R hX
  exact asIso (etaleComparison.{u, v, uL} ρ R 0)

/-- The degree-zero isomorphism has the canonical comparison as its forward map. -/
theorem etaleComparisonZeroIsoOfCompactSpace_hom (hX : IsCompactSpace X) :
    (etaleComparisonZeroIsoOfCompactSpace.{u, v, uL, z} ρ R hX).hom =
      etaleComparison.{u, v, uL} ρ R 0 :=
  rfl

end Langlands.Cohomology.AnalyticEtaleGlobalComparison
