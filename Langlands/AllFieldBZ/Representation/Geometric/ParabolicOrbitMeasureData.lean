import Langlands.AllFieldBZ.Group.GL.CompactOpen
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicOrbitStagesCoefficient
import Langlands.AllFieldBZ.Representation.Parabolic.UnipotentFiniteContainment
import Langlands.Representation.Geometric.ParabolicOrbitMeasureData

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicOrbitMeasureData`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicOrbitMeasureData` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.GeneralLinear
open Langlands.Induction
universe uF

variable (F : Type uF) [CommRing F] [TopologicalSpace F]
  {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

variable [IsTopologicalRing F] [T2Space F]

end Langlands.AllFieldBZ.Geometric
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor padicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
open MeasureTheory
open MeasureTheory.Measure
open Langlands.QuotientIntegration
open scoped Topology
universe uF

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n))

/-- Every element of the actual nested kernel lies in a compact open subgroup. -/
theorem parabolicOrbitNestedKernel_compactOpenCover :
    letI := T.topology
    ∀ x : (parabolicOrbitStagesRetraction F.Carrier B C w).ker,
      ∃ K : OpenSubgroup (parabolicOrbitStagesRetraction F.Carrier B C w).ker,
        IsCompact (K : Set (parabolicOrbitStagesRetraction F.Carrier B C w).ker) ∧
          x ∈ K := by
  classical
  let := T.topology
  let e := parabolicOrbitNestedRadicalEquiv F.Carrier B C w
  intro x
  obtain ⟨K, hK, hx⟩ := Parabolic.unipotentFiniteContainment F T C {e x}
  exact ⟨OpenSubgroup.comap e.toMonoidHom e.continuous K,
    e.toHomeomorph.isClosedEmbedding.isCompact_preimage hK,
    hx (e x) (Finset.mem_singleton_self _)⟩

/-- Compact open subgroups form a neighborhood basis in the actual nested kernel. -/
theorem parabolicOrbitNestedKernel_compactOpenBasis :
    letI := T.topology
    ∀ O : Set (parabolicOrbitStagesRetraction F.Carrier B C w).ker,
      IsOpen O → (1 : (parabolicOrbitStagesRetraction F.Carrier B C w).ker) ∈ O →
      ∃ K : OpenSubgroup (parabolicOrbitStagesRetraction F.Carrier B C w).ker,
        IsCompact (K : Set (parabolicOrbitStagesRetraction F.Carrier B C w).ker) ∧
          (K : Set (parabolicOrbitStagesRetraction F.Carrier B C w).ker) ⊆ O := by
  let := T.topology
  let e := parabolicOrbitNestedRadicalEquiv F.Carrier B C w
  intro O hO h1
  have hneigh : e.symm ⁻¹' O ∈ 𝓝 (1 : C.unipotentRadical F.Carrier) :=
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
    ∀ O : Set (C.parabolic F.Carrier),
      IsOpen O → (1 : C.parabolic F.Carrier) ∈ O →
      ∃ K : OpenSubgroup (C.parabolic F.Carrier),
        IsCompact (K : Set (C.parabolic F.Carrier)) ∧
          (K : Set (C.parabolic F.Carrier)) ⊆ O := by
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
    let N := (parabolicOrbitStagesRetraction F.Carrier B C w).ker
    let I := parabolicOrbitNestedIntersection F.Carrier B C w
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
  let N := (parabolicOrbitStagesRetraction F.Carrier B C w).ker
  let I := parabolicOrbitNestedIntersection F.Carrier B C w
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace I := borel I
  let : BorelSpace I := ⟨rfl⟩
  let : MeasurableSpace (LeftQuotient I) := borel (LeftQuotient I)
  let : BorelSpace (LeftQuotient I) := ⟨rfl⟩
  let := T.unipotentRadicalLocallyCompactSpace C
  let : LocallyCompactSpace N :=
    (parabolicOrbitNestedRadicalEquiv F.Carrier B C w).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hI := isClosed_parabolicOrbitNestedIntersection F.Carrier B C w
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

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
