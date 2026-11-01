import Langlands.Representation.Aubert.CorrectedOrbitCutMeasures

/-! One coherent family of actual orbital measures for every admissible source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometric

open GeneralLinear Induction MeasureTheory MeasureTheory.Measure QuotientIntegration

universe uF

variable (F : Type uF) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B D E C : BlockShape n) (w : Equiv.Perm (Fin n))

local instance (X : BlockShape n) : MeasurableSpace
    (parabolicOrbitStagesRetraction F X C w).ker := borel _
local instance (X : BlockShape n) : BorelSpace
    (parabolicOrbitStagesRetraction F X C w).ker := ⟨rfl⟩
local instance (X : BlockShape n) : MeasurableSpace
    (parabolicOrbitNestedIntersection F X C w) := borel _
local instance (X : BlockShape n) : BorelSpace
    (parabolicOrbitNestedIntersection F X C w) := ⟨rfl⟩
local instance (X : BlockShape n) : MeasurableSpace
    (QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F X C w)) := borel _
local instance (X : BlockShape n) : BorelSpace
    (QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F X C w)) := ⟨rfl⟩

/-- Equality of the three actual measures determines the supplied datum. -/
theorem ParabolicOrbitIntegralMeasures.ext
    {m m' : ParabolicOrbitIntegralMeasures F B C w}
    (hK : m.kernel = m'.kernel) (hI : m.intersection = m'.intersection)
    (hQ : m.quotient = m'.quotient) : m = m' := by
  cases m
  cases m'
  cases hK
  cases hI
  cases hQ
  rfl

omit [IsTopologicalRing F] in
/-- Successive cut-coordinate changes retain the same actual radical element. -/
theorem parabolicOrbitNestedKernelCutEquiv_comp
    (x : (parabolicOrbitStagesRetraction F B C w).ker) :
    parabolicOrbitNestedKernelCutEquiv F D E C w
        (parabolicOrbitNestedKernelCutEquiv F B D C w x) =
      parabolicOrbitNestedKernelCutEquiv F B E C w x := by
  exact Subtype.ext (Subtype.ext rfl)

variable (hBD : B.cuts ⊆ D.cuts) (hDE : D.cuts ⊆ E.cuts)
  (hwB : TypeASolomon.SourceIncreasing B w) (hwD : TypeASolomon.SourceIncreasing D w)

omit [IsTopologicalRing F] in
/-- The actual restricted intersection changes compose without rescaling. -/
theorem parabolicOrbitNestedIntersectionCutEquiv_comp
    (x : parabolicOrbitNestedIntersection F B C w) :
    parabolicOrbitNestedIntersectionCutEquiv F D E C w hDE hwD
        (parabolicOrbitNestedIntersectionCutEquiv F B D C w hBD hwB x) =
      parabolicOrbitNestedIntersectionCutEquiv F B E C w (hBD.trans hDE) hwB x := by
  apply Subtype.ext
  exact parabolicOrbitNestedKernelCutEquiv_comp F B D E C w x.val

omit [IsTopologicalRing F] in
/-- The actual quotient-coordinate changes compose on every quotient class. -/
theorem parabolicOrbitNestedQuotientCutHomeomorph_comp
    (q : QuotientIntegration.LeftQuotient (parabolicOrbitNestedIntersection F B C w)) :
    parabolicOrbitNestedQuotientCutHomeomorph F D E C w hDE hwD
        (parabolicOrbitNestedQuotientCutHomeomorph F B D C w hBD hwB q) =
      parabolicOrbitNestedQuotientCutHomeomorph F B E C w (hBD.trans hDE) hwB q := by
  induction q using Quotient.inductionOn with
  | h x =>
    exact congrArg (quotientMap (parabolicOrbitNestedIntersection F E C w))
      (parabolicOrbitNestedKernelCutEquiv_comp F B D E C w x)

/-- Transporting all three actual measures twice equals transport along the
composite cut inclusion. -/
theorem parabolicOrbitIntegralMeasures_cutMap_comp
    (m : ParabolicOrbitIntegralMeasures F B C w) :
    parabolicOrbitIntegralMeasures_cutMap F D E C w hDE hwD
        (parabolicOrbitIntegralMeasures_cutMap F B D C w hBD hwB m) =
      parabolicOrbitIntegralMeasures_cutMap F B E C w (hBD.trans hDE) hwB m := by
  apply ParabolicOrbitIntegralMeasures.ext F E C w
  · change Measure.map (parabolicOrbitNestedKernelCutEquiv F D E C w)
        (Measure.map (parabolicOrbitNestedKernelCutEquiv F B D C w) m.kernel) =
      Measure.map (parabolicOrbitNestedKernelCutEquiv F B E C w) m.kernel
    have hBDm : Measurable (parabolicOrbitNestedKernelCutEquiv F B D C w) :=
      (parabolicOrbitNestedKernelCutEquiv F B D C w).continuous.measurable
    have hDEm : Measurable (parabolicOrbitNestedKernelCutEquiv F D E C w) :=
      (parabolicOrbitNestedKernelCutEquiv F D E C w).continuous.measurable
    rw [Measure.map_map hDEm hBDm]
    exact congrArg (fun f => Measure.map f m.kernel)
      (funext (parabolicOrbitNestedKernelCutEquiv_comp F B D E C w))
  · change Measure.map (parabolicOrbitNestedIntersectionCutEquiv F D E C w hDE hwD)
        (Measure.map (parabolicOrbitNestedIntersectionCutEquiv F B D C w hBD hwB)
          m.intersection) =
      Measure.map (parabolicOrbitNestedIntersectionCutEquiv F B E C w (hBD.trans hDE) hwB)
        m.intersection
    have hBDm : Measurable (parabolicOrbitNestedIntersectionCutEquiv F B D C w hBD hwB) :=
      (parabolicOrbitNestedIntersectionCutEquiv F B D C w hBD hwB).continuous.measurable
    have hDEm : Measurable (parabolicOrbitNestedIntersectionCutEquiv F D E C w hDE hwD) :=
      (parabolicOrbitNestedIntersectionCutEquiv F D E C w hDE hwD).continuous.measurable
    rw [Measure.map_map hDEm hBDm]
    exact congrArg (fun f => Measure.map f m.intersection)
      (funext (parabolicOrbitNestedIntersectionCutEquiv_comp F B D E C w hBD hDE hwB hwD))
  · change Measure.map (parabolicOrbitNestedQuotientCutHomeomorph F D E C w hDE hwD)
        (Measure.map (parabolicOrbitNestedQuotientCutHomeomorph F B D C w hBD hwB)
          m.quotient) =
      Measure.map (parabolicOrbitNestedQuotientCutHomeomorph F B E C w (hBD.trans hDE) hwB)
        m.quotient
    have hBDm : Measurable (parabolicOrbitNestedQuotientCutHomeomorph F B D C w hBD hwB) :=
      (parabolicOrbitNestedQuotientCutHomeomorph F B D C w hBD hwB).continuous.measurable
    have hDEm : Measurable (parabolicOrbitNestedQuotientCutHomeomorph F D E C w hDE hwD) :=
      (parabolicOrbitNestedQuotientCutHomeomorph F D E C w hDE hwD).continuous.measurable
    rw [Measure.map_map hDEm hBDm]
    exact congrArg (fun f => Measure.map f m.quotient)
      (funext (parabolicOrbitNestedQuotientCutHomeomorph_comp F B D E C w hBD hDE hwB hwD))

end Langlands.Geometric

namespace Langlands.Geometric

open GeneralLinear

variable {n : ℕ} (w : Equiv.Perm (Fin n))

/-- The coarsest source shape on whose blocks the permutation increases. -/
def parabolicOrbitIncreasingBase : BlockShape n :=
  (BlockShape.cutEquiv n).symm (permutationDescents w)

theorem parabolicOrbitIncreasingBase_sourceIncreasing :
    TypeASolomon.SourceIncreasing (parabolicOrbitIncreasingBase w) w := by
  have h := (TypeASolomon.inverseIncreasing_iff (parabolicOrbitIncreasingBase w) w.symm).mpr
    (by simp [parabolicOrbitIncreasingBase])
  simpa only [Equiv.symm_symm] using h

theorem parabolicOrbitIncreasingBase_cuts_subset (B : BlockShape n)
    (hw : TypeASolomon.SourceIncreasing B w) :
    (parabolicOrbitIncreasingBase w).cuts ⊆ B.cuts := by
  have h := (TypeASolomon.inverseIncreasing_iff B w.symm).mp
    (by simpa only [Equiv.symm_symm] using hw)
  intro e he
  apply h e
  simpa only [parabolicOrbitIncreasingBase, BlockShape.cuts_cutEquiv_symm,
    Equiv.symm_symm] using he

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric Induction MeasureTheory QuotientIntegration

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (C : BlockShape n) (w : Equiv.Perm (Fin n))

/-- One choice at the coarsest increasing source supplies all actual orbit
measures for the given target and permutation. -/
def parabolicOrbitCoherentMeasures :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (B : BlockShape n), TypeASolomon.SourceIncreasing B w →
      ParabolicOrbitIntegralMeasures F.Carrier B C w := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let m := Classical.choice
    (T.parabolicOrbitIntegralMeasures_nonempty (parabolicOrbitIncreasingBase w) C w)
  intro B hw
  exact parabolicOrbitIntegralMeasures_cutMap F.Carrier (parabolicOrbitIncreasingBase w) B C w
    (parabolicOrbitIncreasingBase_cuts_subset w B hw)
    (parabolicOrbitIncreasingBase_sourceIncreasing w) m

/-- Every cut inclusion uses the same simultaneous transport in this family. -/
theorem parabolicOrbitCoherentMeasures_cutMap (B D : BlockShape n)
    (h : B.cuts ⊆ D.cuts) (hwB : TypeASolomon.SourceIncreasing B w)
    (hwD : TypeASolomon.SourceIncreasing D w) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    parabolicOrbitIntegralMeasures_cutMap F.Carrier B D C w h hwB
        (T.parabolicOrbitCoherentMeasures C w B hwB) =
      T.parabolicOrbitCoherentMeasures C w D hwD := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact parabolicOrbitIntegralMeasures_cutMap_comp F.Carrier
    (parabolicOrbitIncreasingBase w) B D C w
    (parabolicOrbitIncreasingBase_cuts_subset w B hwB) h
    (parabolicOrbitIncreasingBase_sourceIncreasing w) hwB _

end Langlands.PadicField.TopologicalData
