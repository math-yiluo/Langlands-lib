import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.Representation.Geometric.ParabolicOrbitIntegralComparison
import Langlands.Representation.Aubert.CorrectedOrbitCutIntegrals

/-! Simultaneous transport of the actual compatible orbit measures across cuts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometric

open GeneralLinear Induction MeasureTheory MeasureTheory.Measure QuotientIntegration

universe uF

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B D C : BlockShape n) (w : Equiv.Perm (Fin n))
  (h : B.cuts ⊆ D.cuts) (hw : TypeASolomon.SourceIncreasing B w)

/-- The actual nested intersection equivalence, restricted from the common
actual target-radical coordinate on the kernels. -/
def parabolicOrbitNestedIntersectionCutEquiv :
    parabolicOrbitNestedIntersection F B C w ≃ₜ*
      parabolicOrbitNestedIntersection F D C w :=
  subgroupContinuousMulEquiv (parabolicOrbitNestedKernelCutEquiv F B D C w)
    (parabolicOrbitNestedIntersection F B C w)
    (parabolicOrbitNestedIntersection F D C w)
    (parabolicOrbitNestedKernelCutEquiv_mem F B D C w h hw)

omit [IsTopologicalRing F] in
@[simp]
theorem parabolicOrbitNestedIntersectionCutEquiv_val
    (x : parabolicOrbitNestedIntersection F B C w) :
    (parabolicOrbitNestedIntersectionCutEquiv F B D C w h hw x).val =
      parabolicOrbitNestedKernelCutEquiv F B D C w x.val := rfl

local instance (E : BlockShape n) : MeasurableSpace
    (parabolicOrbitStagesRetraction F E C w).ker := borel _
local instance (E : BlockShape n) : BorelSpace
    (parabolicOrbitStagesRetraction F E C w).ker := ⟨rfl⟩
local instance (E : BlockShape n) : MeasurableSpace
    (parabolicOrbitNestedIntersection F E C w) := borel _
local instance (E : BlockShape n) : BorelSpace
    (parabolicOrbitNestedIntersection F E C w) := ⟨rfl⟩
local instance (E : BlockShape n) : MeasurableSpace
    (QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F E C w)) := borel _
local instance (E : BlockShape n) : BorelSpace
    (QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F E C w)) := ⟨rfl⟩

/-- Push the three supplied measures through the actual kernel, intersection,
and quotient equivalences. This preserves the entire compatibility property. -/
def parabolicOrbitIntegralMeasures_cutMap
    (m : ParabolicOrbitIntegralMeasures F B C w) :
    ParabolicOrbitIntegralMeasures F D C w := by
  let := m.kernelHaar
  let := m.kernelRegular
  let := m.kernelRight
  let := m.intersectionHaar
  let := m.intersectionRegular
  let := m.intersectionRight
  let := m.quotientFinite
  let e := parabolicOrbitNestedKernelCutEquiv F B D C w
  let eI := parabolicOrbitNestedIntersectionCutEquiv F B D C w h hw
  let eQ := parabolicOrbitNestedQuotientCutHomeomorph F B D C w h hw
  exact
    { kernel := Measure.map e m.kernel
      intersection := Measure.map eI m.intersection
      quotient := Measure.map eQ m.quotient
      kernelHaar := e.isHaarMeasure_map m.kernel
      kernelRegular := Measure.Regular.map e.toHomeomorph
      kernelRight := isMulRightInvariant_map e m.kernel
      intersectionHaar := eI.isHaarMeasure_map m.intersection
      intersectionRegular := Measure.Regular.map eI.toHomeomorph
      intersectionRight := isMulRightInvariant_map eI m.intersection
      quotientFinite := IsFiniteMeasureOnCompacts.map m.quotient eQ
      compatible := isCompatible_map_equiv e
        (parabolicOrbitNestedIntersection F B C w)
        (parabolicOrbitNestedIntersection F D C w) eI (fun _ => rfl) eQ
        (fun _ => rfl) m.kernel m.intersection m.quotient m.compatible }

@[simp]
theorem parabolicOrbitIntegralMeasures_cutMap_kernel
    (m : ParabolicOrbitIntegralMeasures F B C w) :
    (parabolicOrbitIntegralMeasures_cutMap F B D C w h hw m).kernel =
      Measure.map (parabolicOrbitNestedKernelCutEquiv F B D C w) m.kernel := rfl

@[simp]
theorem parabolicOrbitIntegralMeasures_cutMap_intersection
    (m : ParabolicOrbitIntegralMeasures F B C w) :
    (parabolicOrbitIntegralMeasures_cutMap F B D C w h hw m).intersection =
      Measure.map (parabolicOrbitNestedIntersectionCutEquiv F B D C w h hw)
        m.intersection := rfl

@[simp]
theorem parabolicOrbitIntegralMeasures_cutMap_quotient
    (m : ParabolicOrbitIntegralMeasures F B C w) :
    (parabolicOrbitIntegralMeasures_cutMap F B D C w h hw m).quotient =
      Measure.map (parabolicOrbitNestedQuotientCutHomeomorph F B D C w h hw)
        m.quotient := rfl

end Langlands.Geometric
