import Langlands.AllFieldBZ.Group.GL.RankMaps
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open Filter
open Topology
namespace Langlands.AllFieldBZ.CuspidalSupport.LeviAdmissibility
open Langlands.CuspidalSupport.LeviAdmissibility hiding irreducibleQuasicuspidalLeviAdmissibility
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
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
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) :
    IrreducibleQuasicuspidalLeviAdmissibilityTheorem.{uF, uV} F T B := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  intro σ hirr hq
  exact isAdmissible_of_isLeviQuasicuspidal B σ.representation σ.isSmooth hirr hq

end Langlands.AllFieldBZ.CuspidalSupport.LeviAdmissibility
