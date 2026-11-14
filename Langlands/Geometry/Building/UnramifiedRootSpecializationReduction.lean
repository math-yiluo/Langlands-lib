import Langlands.Geometry.Building.UnramifiedFixedResidueRootModelStatement
import Langlands.Geometry.Building.UnramifiedRootSpecializationStatement
import Langlands.Geometry.Building.UnramifiedFixedRootModelStatement
import Langlands.BruhatTits.IntegralModels.RootSpecializationConstruction

/-! # Root specialization from fixed-point models with surviving residue roots -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

/-- The implication from fixed-point models whose reductive quotients carry the
vanishing restricted roots to the structural root-specialization statement.
This proposition only names the implication; neither side is asserted. It is
proved below by `unramifiedRootSpecializationReduction`. -/
def UnramifiedRootSpecializationReductionStatement : Prop :=
  UnramifiedFixedResidueRootModelStatement.{u} → UnramifiedRootSpecializationStatement.{u}

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 5000000 in
/-- Fixed-point models whose reductive quotients carry the vanishing
restricted roots imply the exact structural root-specialization statement.
The specialization data are the actual construction
`IntegralTorusData.rootSpecializationData`, and reduction compatibility follows
from the exact integral and positive root-point identities. -/
theorem unramifiedRootSpecialization_of_fixedResidueRootModel
    (h : UnramifiedFixedResidueRootModelStatement.{u}) :
    UnramifiedRootSpecializationStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hfactor hiT hE D C hΩ
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  intro fixed φ P Q x hx
  obtain ⟨D₀, T₀, hT₀, Q₀, hclosed, hmax, hQ₀, hmaxQ, hpoints, hroots⟩ :=
    h F G hG S iS hiS T iT f hfactor hiT hE D C hΩ x hx
  refine ⟨D₀, T₀, hT₀, Q₀, hclosed, hmax, hQ₀, hmaxQ, ?_⟩
  intro ψ hψ hnonzero
  obtain ⟨a, ha, c, hc0, hforms⟩ := hroots ψ hψ hnonzero
  refine ⟨a, T₀.rootSpecializationData hT₀ Q₀ hQ₀ a ha, ?_, c, hc0, hforms⟩
  apply IntegralRootSpecializationData.reductionCompatible_of_neutral _ _ hQ₀
  · intro g hg hint
    exact ((hpoints a a.2 g hg).1).1 hint
  · intro g hg _ hpos
    exact ((hpoints a a.2 g hg).2).2 hpos

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 5000000 in
/-- The same statement also implies the published fixed-point root-model
statement, by forgetting the additional torus and root clauses. -/
theorem unramifiedFixedRootModel_of_fixedResidueRootModel
    (h : UnramifiedFixedResidueRootModelStatement.{u}) :
    UnramifiedFixedRootModelStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hfactor hiT hE D C hΩ fixed φ z hz
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  have hz' := h F G hG S iS hiS T iT f hfactor hiT hE D C hΩ z hz
  obtain ⟨D₀, T₀, hT₀, Q₀, hclosed, -, hQ₀, -, hpoints, -⟩ := hz'
  refine ⟨D₀, T₀, Q₀, ⟨hT₀, hclosed⟩, hQ₀, ?_⟩
  exact hpoints

/-- The named implication holds. -/
theorem unramifiedRootSpecializationReduction :
    UnramifiedRootSpecializationReductionStatement.{u} :=
  unramifiedRootSpecialization_of_fixedResidueRootModel

end Langlands.Geometry.Building
