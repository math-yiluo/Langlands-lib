import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
import Langlands.AllField.Representation.Geometric.RefinementFunctors
import Langlands.AllField.Representation.Jacquet.Parabolic
/-!
# Admissibility of irreducible quasicuspidal product-Levi representations
-/

noncomputable section

open Filter Topology

namespace Langlands.AllField.CuspidalSupport.LeviAdmissibility
open Langlands.CuspidalSupport.LeviAdmissibility hiding irreducibleQuasicuspidalLeviAdmissibility
open Langlands.AllField.CuspidalSupport.LeviAdmissibility
open Langlands.CuspidalSupport hiding CuspidalEmbeddingTheorem IrreducibleQuasicuspidalLeviAdmissibilityTheorem NormalizedQuasicuspidalEmbeddingTheorem ZeroRankCuspidalEmbeddingTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV

/-! ### Generic facts about irreducible and compact groups -/

section Generic

variable {G : Type*} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Generic

/-! ### The product Levi over a local field -/

section Levi

variable {K : Type uF} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable {n : ℕ} (B : BlockShape n)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Levi

/-- The published proposition family, from the published Cartan decomposition
`Langlands.GeneralLinear.Cartan.cartanDecomposition` and Schur's lemma in countable
dimension `Langlands.countableDimensionalSchur`. -/
theorem irreducibleQuasicuspidalLeviAdmissibility
    (F : Type uF) [Field F] (T : LocalFieldData F)
    {n : ℕ} (B : BlockShape n) :
    IrreducibleQuasicuspidalLeviAdmissibilityTheorem.{uF, uV} F T B := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  intro σ hirr hq
  exact isAdmissible_of_isLeviQuasicuspidal B σ.representation σ.isSmooth hirr hq

end Langlands.AllField.CuspidalSupport.LeviAdmissibility
