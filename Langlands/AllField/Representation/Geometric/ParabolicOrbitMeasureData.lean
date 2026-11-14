import Langlands.Representation.Geometric.ParabolicOrbitMeasureData
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.Geometric.ParabolicOrbitStagesCoefficient
import Langlands.AllField.Representation.Parabolic.UnipotentFiniteContainment
/-! Actual analytic inputs for the nested parabolic orbit quotient integral. -/

noncomputable section

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Induction hiding SmoothRep

universe uF



end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open _root_.MeasureTheory MeasureTheory.Measure
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric
open Langlands.QuotientIntegration
open scoped _root_.Topology

universe uF

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n))

/-- Every element of the actual nested kernel lies in a compact open subgroup. -/
theorem parabolicOrbitNestedKernel_compactOpenCover :
    letI := T.topology
    ∀ x : (parabolicOrbitStagesRetraction F B C w).ker,
      ∃ K : OpenSubgroup (parabolicOrbitStagesRetraction F B C w).ker,
        IsCompact (K : Set (parabolicOrbitStagesRetraction F B C w).ker) ∧
          x ∈ K := by
  classical
  let := T.topology
  let e := parabolicOrbitNestedRadicalEquiv F B C w
  intro x
  obtain ⟨K, hK, hx⟩ := Langlands.AllField.Parabolic.unipotentFiniteContainment F T C {e x}
  exact ⟨OpenSubgroup.comap e.toMonoidHom e.continuous K,
    e.toHomeomorph.isClosedEmbedding.isCompact_preimage hK,
    hx (e x) (Finset.mem_singleton_self _)⟩

/-- Compact open subgroups form a neighborhood basis in the actual nested kernel. -/
theorem parabolicOrbitNestedKernel_compactOpenBasis :
    letI := T.topology
    ∀ O : Set (parabolicOrbitStagesRetraction F B C w).ker,
      IsOpen O → (1 : (parabolicOrbitStagesRetraction F B C w).ker) ∈ O →
      ∃ K : OpenSubgroup (parabolicOrbitStagesRetraction F B C w).ker,
        IsCompact (K : Set (parabolicOrbitStagesRetraction F B C w).ker) ∧
          (K : Set (parabolicOrbitStagesRetraction F B C w).ker) ⊆ O := by
  let := T.topology
  let e := parabolicOrbitNestedRadicalEquiv F B C w
  intro O hO h1
  have hneigh : e.symm ⁻¹' O ∈ 𝓝 (1 : C.unipotentRadical F) :=
    (hO.preimage e.symm.continuous).mem_nhds (by simpa using h1)
  let K := T.unipotentRadicalCompactOpen C (e.symm ⁻¹' O) hneigh
  refine ⟨OpenSubgroup.comap e.toMonoidHom e.continuous K.val,
    e.toHomeomorph.isClosedEmbedding.isCompact_preimage K.property.1, ?_⟩
  intro x hx
  have := K.property.2 hx
  change e.symm (e x) ∈ O at this
  simpa only [e.symm_apply_apply] using this

/-- The actual target parabolic has the compact open basis needed by outer stages. -/
theorem parabolicOrbitParabolic_compactOpenBasis :
    letI := T.topology
    ∀ O : Set (C.parabolic F),
      IsOpen O → (1 : C.parabolic F) ∈ O →
      ∃ K : OpenSubgroup (C.parabolic F),
        IsCompact (K : Set (C.parabolic F)) ∧
          (K : Set (C.parabolic F)) ⊆ O := by
  let := T.topology
  intro O hO h1
  exact ⟨(T.parabolicCompactOpen C O (hO.mem_nhds h1)).val,
    (T.parabolicCompactOpen C O (hO.mem_nhds h1)).property⟩

/-- Actual two-sided Haar measures and a compatible locally finite quotient
measure exist for the nested kernel and its actual stabilizer intersection. -/
theorem parabolicOrbitNested_measureExists :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    let N := (parabolicOrbitStagesRetraction F B C w).ker
    let I := parabolicOrbitNestedIntersection F B C w
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace I := borel I
    letI : BorelSpace I := ⟨rfl⟩
    letI : MeasurableSpace (LeftQuotient I) := borel (LeftQuotient I)
    letI : BorelSpace (LeftQuotient I) := ⟨rfl⟩
    ∃ (μN : Measure N) (μI : Measure I),
      IsHaarMeasure μN ∧ μN.Regular ∧ IsMulRightInvariant μN ∧
      IsHaarMeasure μI ∧ μI.Regular ∧
      ∃ hI : IsMulRightInvariant μI,
        letI := hI
        ∃ ν : Measure (LeftQuotient I), IsFiniteMeasureOnCompacts ν ∧
          IsCompatible I μN μI ν := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let N := (parabolicOrbitStagesRetraction F B C w).ker
  let I := parabolicOrbitNestedIntersection F B C w
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace I := borel I
  let : BorelSpace I := ⟨rfl⟩
  let : MeasurableSpace (LeftQuotient I) := borel (LeftQuotient I)
  let : BorelSpace (LeftQuotient I) := ⟨rfl⟩
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace N :=
    (parabolicOrbitNestedRadicalEquiv F B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hI := isClosed_parabolicOrbitNestedIntersection F B C w
  let : LocallyCompactSpace I := hI.locallyCompactSpace
  have hu := Haar.compactOpenCoverUnimodularity
    (T.parabolicOrbitNestedKernel_compactOpenCover B C w)
  let μN : Measure N := haar
  let μI : Measure I := haar
  let : IsMulRightInvariant μN := hu.1 μN
  let : IsMulRightInvariant μI := hu.2 I hI μI
  obtain ⟨ν, hν⟩ := compatibleMeasureExists I hI μN μI
  let : ν.Regular := hν.regular
  exact ⟨μN, μI, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ν, inferInstance, hν⟩

end Langlands.LocalFieldData
