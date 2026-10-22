import Langlands.Global.ArchimedeanCompactMaximalityStatement
import Langlands.Group.UnitaryMatrixMaximality

noncomputable section

universe u

namespace Langlands.Global

open NumberField NumberField.InfinitePlace

variable (K : Type u) [Field K] (n : ℕ)

private def realProjection (v : {v : InfinitePlace K // IsReal v}) :
    InfiniteAdelicGL K n →* Matrix.GeneralLinearGroup (Fin n) ℝ :=
  (Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // IsReal v} => ℝ) v).comp
      (RingHom.fst _ _))).comp (archimedeanGLCoordinates K n).toMonoidHom

private def complexProjection (v : {v : InfinitePlace K // IsComplex v}) :
    InfiniteAdelicGL K n →* Matrix.GeneralLinearGroup (Fin n) ℂ :=
  (Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun _ : {v : InfinitePlace K // IsComplex v} => ℂ) v).comp
      (RingHom.snd _ _))).comp (archimedeanGLCoordinates K n).toMonoidHom

private theorem continuous_realProjection (v : {v : InfinitePlace K // IsReal v}) :
    Continuous (realProjection K n v) :=
  ((continuous_apply v).comp continuous_fst).generalLinearGroup_map.comp
    (archimedeanGLCoordinates K n).continuous

private theorem continuous_complexProjection (v : {v : InfinitePlace K // IsComplex v}) :
    Continuous (complexProjection K n v) :=
  ((continuous_apply v).comp continuous_snd).generalLinearGroup_map.comp
    (archimedeanGLCoordinates K n).continuous

private theorem realProjection_standard (v : {v : InfinitePlace K // IsReal v})
    (q : Matrix.unitaryGroup (Fin n) ℝ) :
    ∃ g ∈ standardInfiniteCompact K n, realProjection K n v g = Unitary.toUnits q := by
  let p : ArchimedeanCompactFactors K n := (fun _ => q, fun _ => 1)
  refine ⟨ArchimedeanCompactFactors.toInfiniteAdelicGL K n p, ⟨p, rfl⟩, ?_⟩
  apply Units.ext
  change (fun i j => ((archimedeanGLCoordinates K n
    (ArchimedeanCompactFactors.toInfiniteAdelicGL K n p)) i j).1 v) = q.val
  rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

private theorem complexProjection_standard (v : {v : InfinitePlace K // IsComplex v})
    (q : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ g ∈ standardInfiniteCompact K n, complexProjection K n v g = Unitary.toUnits q := by
  let p : ArchimedeanCompactFactors K n := (fun _ => 1, fun _ => q)
  refine ⟨ArchimedeanCompactFactors.toInfiniteAdelicGL K n p, ⟨p, rfl⟩, ?_⟩
  apply Units.ext
  change (fun i j => ((archimedeanGLCoordinates K n
    (ArchimedeanCompactFactors.toInfiniteAdelicGL K n p)) i j).2 v) = q.val
  rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

private theorem isCompact_realImage (U : Subgroup (InfiniteAdelicGL K n))
    (hU : IsCompact (U : Set (InfiniteAdelicGL K n)))
    (v : {v : InfinitePlace K // IsReal v}) :
    IsCompact (U.map (realProjection K n v) :
      Set (Matrix.GeneralLinearGroup (Fin n) ℝ)) := by
  rw [Subgroup.coe_map]
  exact hU.image (continuous_realProjection K n v)

private theorem isCompact_complexImage (U : Subgroup (InfiniteAdelicGL K n))
    (hU : IsCompact (U : Set (InfiniteAdelicGL K n)))
    (v : {v : InfinitePlace K // IsComplex v}) :
    IsCompact (U.map (complexProjection K n v) :
      Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) := by
  rw [Subgroup.coe_map]
  exact hU.image (continuous_complexProjection K n v)

private theorem unitary_mem_realImage (U : Subgroup (InfiniteAdelicGL K n))
    (hsub : standardInfiniteCompact K n ≤ U)
    (v : {v : InfinitePlace K // IsReal v}) (q : Matrix.unitaryGroup (Fin n) ℝ) :
    Unitary.toUnits q ∈ U.map (realProjection K n v) := by
  obtain ⟨x, hx, he⟩ := realProjection_standard K n v q
  exact ⟨x, hsub hx, he⟩

private theorem unitary_mem_complexImage (U : Subgroup (InfiniteAdelicGL K n))
    (hsub : standardInfiniteCompact K n ≤ U)
    (v : {v : InfinitePlace K // IsComplex v}) (q : Matrix.unitaryGroup (Fin n) ℂ) :
    Unitary.toUnits q ∈ U.map (complexProjection K n v) := by
  obtain ⟨x, hx, he⟩ := complexProjection_standard K n v q
  exact ⟨x, hsub hx, he⟩

private theorem real_unitary_of_local
    (hR : Langlands.Group.UnitaryMatrixCompactOvergroupStatement ℝ n)
    (U : Subgroup (InfiniteAdelicGL K n))
    (hU : IsCompact (U : Set (InfiniteAdelicGL K n)))
    (hsub : standardInfiniteCompact K n ≤ U)
    (g : InfiniteAdelicGL K n) (hg : g ∈ U)
    (v : {v : InfinitePlace K // IsReal v}) :
    ArchimedeanGL.realMatrix K n (archimedeanGLCoordinates K n g) v ∈
      Matrix.unitaryGroup (Fin n) ℝ :=
  hR (U.map (realProjection K n v)) (isCompact_realImage K n U hU v)
    (unitary_mem_realImage K n U hsub v) (realProjection K n v g)
    (Subgroup.mem_map_of_mem (realProjection K n v) hg)

private theorem complex_unitary_of_local
    (hC : Langlands.Group.UnitaryMatrixCompactOvergroupStatement ℂ n)
    (U : Subgroup (InfiniteAdelicGL K n))
    (hU : IsCompact (U : Set (InfiniteAdelicGL K n)))
    (hsub : standardInfiniteCompact K n ≤ U)
    (g : InfiniteAdelicGL K n) (hg : g ∈ U)
    (v : {v : InfinitePlace K // IsComplex v}) :
    ArchimedeanGL.complexMatrix K n (archimedeanGLCoordinates K n g) v ∈
      Matrix.unitaryGroup (Fin n) ℂ :=
  hC (U.map (complexProjection K n v)) (isCompact_complexImage K n U hU v)
    (unitary_mem_complexImage K n U hsub v) (complexProjection K n v g)
    (Subgroup.mem_map_of_mem (complexProjection K n v) hg)

private theorem maximality_of_local [NumberField K]
    (hR : Langlands.Group.UnitaryMatrixCompactOvergroupStatement ℝ n)
    (hC : Langlands.Group.UnitaryMatrixCompactOvergroupStatement ℂ n) :
    StandardInfiniteCompactMaximalityStatement K n := by
  intro U hU hsub
  apply le_antisymm _ hsub
  intro g hg
  exact (mem_standardInfiniteCompact_iff K n g).mpr
    ⟨real_unitary_of_local K n hR U hU hsub g hg,
     complex_unitary_of_local K n hC U hU hsub g hg⟩

/-- The standard orthogonal/unitary subgroup is maximal among compact subgroups
of the actual infinite adelic general linear group, in every natural rank. -/
theorem standardInfiniteCompactMaximality
    (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    StandardInfiniteCompactMaximalityStatement K n :=
  maximality_of_local K n
    (Langlands.Group.unitaryMatrixCompactOvergroup ℝ n)
    (Langlands.Group.unitaryMatrixCompactOvergroup ℂ n)

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    StandardInfiniteCompactMaximalityStatement K n :=
  @standardInfiniteCompactMaximality

end Langlands.Global
