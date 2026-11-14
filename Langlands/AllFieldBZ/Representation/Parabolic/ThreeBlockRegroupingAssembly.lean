import Langlands.AllFieldBZ.Group.GL.AdjacentMergeShape
import Langlands.AllFieldBZ.Representation.Parabolic.OrderedProductRegroupingStatement
import Langlands.AllFieldBZ.Representation.Parabolic.RegroupingFactorEquivalences
import Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly

/-!
# All-field port of `Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass blockSum rankInclusion
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- The functor value of a factor family is its normalized product. -/
def normalizedProductInductionObjEquiv {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    Representation.Equiv ((T.normalizedProductInductionFunctor B).obj σ).representation
      (T.normalizedProductInduced B (fun i => (σ i).representation)) :=
  letI := T.topology
  Representation.Equiv.refl _

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding OrderedProductRegrouping
section EquivalenceAlgebra
universe uA uG uH uV uW uU

end EquivalenceAlgebra
end Langlands.AllFieldBZ.Parabolic
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding OrderedProductRegrouping
open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
open Langlands.Shahidi
section Pairs
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

end Pairs
section Regroupings
universe uF uW

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)
variable (regrouping : OrderedProductRegrouping.{uF, max uF uW} F T)
variable (C A B : ℕ) (hC : 0 < C) (hA : 0 < A) (hB : 0 < B)
variable (σ0 : letI := T.topology; SmoothRep.{0,uF,max uF uW} ℂ (GeneralLinear C F.Carrier))
variable (σ1 : letI := T.topology; SmoothRep.{0,uF,max uF uW} ℂ (GeneralLinear A F.Carrier))
variable (σ2 : letI := T.topology; SmoothRep.{0,uF,max uF uW} ℂ (GeneralLinear B F.Carrier))

end Regroupings
universe uF uW

end Langlands.AllFieldBZ.Parabolic
