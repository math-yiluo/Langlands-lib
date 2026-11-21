import Langlands.BaseChange.TwistedCharacter.CompactOpenHaarChart
import Langlands.BaseChange.GeneralLinearFiniteAlgebra
import Langlands.Group.GL.TriangularParabolic
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic
import Mathlib.Topology.Instances.Matrix

/-! # Haar density in full and upper triangular matrix coordinates -/

set_option autoImplicit false

noncomputable section

namespace Langlands.BaseChange

open Function Topology Set MeasureTheory HarishChandraSchwartz
open scoped ENNReal NNReal

universe u v

/-- The value map from the units of a finite algebra over a Hausdorff topological field is
an open embedding for the module topology. -/
theorem isOpenEmbedding_unitsVal_of_finiteAlgebra
    (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [ContinuousInv₀ F]
    [T1Space F]
    (A : Type v) [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
    [IsModuleTopology F A] :
    IsOpenEmbedding (Units.val : Aˣ → A) := by
  let ι := Fin (Module.finrank F A)
  let b := Module.finBasis F A
  let f : A →ₐ[F] Matrix ι ι F := Algebra.leftMulMatrix b
  have : IsModuleTopology F (Matrix ι ι F) :=
    inferInstanceAs (IsModuleTopology F (ι → ι → F))
  have : ContinuousAdd A := IsModuleTopology.toContinuousAdd F A
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f.toLinearMap
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr
      (Algebra.leftMulMatrix_injective b))
  have hg' : LeftInverse g f := fun a => DFunLike.congr_fun hg a
  have hfe : IsEmbedding f := hg'.isEmbedding
    (IsModuleTopology.continuous_of_linearMap g) hf
  have hval : IsOpenEmbedding (Units.val : (Matrix ι ι F)ˣ → Matrix ι ι F) := by
    refine ⟨Units.isEmbedding_val_mk' (f := Inv.inv) ?_
      (fun g => (Matrix.GeneralLinearGroup.coe_inv g).symm), ?_⟩
    · intro X hX
      have hd : X.det ≠ 0 := isUnit_iff_ne_zero.mp
        ((Matrix.isUnit_iff_isUnit_det X).mp hX)
      apply (continuousAt_matrix_inv X ?_).continuousWithinAt
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hd
    · have hrange : range (Units.val : (Matrix ι ι F)ˣ → Matrix ι ι F) =
          Matrix.det ⁻¹' ({0}ᶜ : Set F) := by
        ext X
        exact (Matrix.isUnit_iff_isUnit_det X).trans isUnit_iff_ne_zero
      rw [hrange]
      exact isClosed_singleton.isOpen_compl.preimage continuous_id.matrix_det
  have hfu : IsEmbedding (Units.map f.toMonoidHom) := hfe.units_map
  refine ⟨hfe.of_comp_iff.mp (hval.isEmbedding.comp hfu), ?_⟩
  have hrange : range (Units.val : Aˣ → A) =
      f ⁻¹' range (Units.val : (Matrix ι ι F)ˣ → Matrix ι ι F) := by
    ext a
    change IsUnit a ↔ IsUnit (Algebra.leftMulMatrix b a)
    rw [Algebra.leftMulMatrix_apply, LinearMap.isUnit_toMatrix_iff, Algebra.lmul_isUnit_iff]
  rw [hrange]
  exact hval.isOpen_range.preimage hf

section Matrix

variable (F : Type u) [Field F] (E : Type v) [CommRing E] [Algebra F E] (n : ℕ)

local notation "Mat" => Matrix (Fin n) (Fin n) E
local notation "Tri" => Matrix.blockTriangularSubalgebra F E (id : Fin n → Fin n)
local notation "P" => GeneralLinear.upperTriangularSubgroup n E

/-- Upper triangular invertible matrices are the units of the upper triangular algebra. -/
def upperTriangularUnitsEquiv : P ≃* Triˣ :=
  let S := (Tri : Subalgebra F Mat).toSubmonoid
  (MulEquiv.subgroupCongr (show P = S.units from
    Subgroup.ext fun _ =>
      ⟨fun hg => ⟨hg, (GeneralLinear.upperTriangularSubgroup n E).inv_mem hg⟩,
        fun hg => hg.1⟩)).trans
    S.unitsEquivUnitsType

variable [TopologicalSpace E] [Module.Finite F E] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [IsModuleTopology F E]

include F in
/-- Taking the entries of an invertible matrix is an open embedding. -/
theorem isOpenEmbedding_generalLinearVal :
    IsOpenEmbedding (Units.val : GeneralLinear n E → Mat) := by
  have := LocalFieldTopology.t2Space F
  have : Module.Finite F Mat := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
  have : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  exact isOpenEmbedding_unitsVal_of_finiteAlgebra F Mat

/-- Taking the entries of an upper triangular unit is an open embedding into the algebra
of upper triangular matrices. -/
theorem isOpenEmbedding_upperTriangularVal :
    IsOpenEmbedding (fun p : P => (upperTriangularUnitsEquiv F E n p : Tri)) := by
  have hval := isOpenEmbedding_generalLinearVal F E n
  have hel : IsEmbedding (Subtype.val : Tri → Mat) := IsEmbedding.subtypeVal
  refine ⟨hel.of_comp_iff.mp (hval.isEmbedding.comp IsEmbedding.subtypeVal), ?_⟩
  have hrange : range (fun p : P => (upperTriangularUnitsEquiv F E n p : Tri)) =
      Subtype.val ⁻¹' range (Units.val : GeneralLinear n E → Mat) := by
    ext a
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p : GeneralLinear n E), rfl⟩
    · rintro ⟨p, hp⟩
      have hp' : p ∈ P := by
        change p.val.IsUpperTriangular
        rw [hp]
        exact a.property
      exact ⟨⟨p, hp'⟩, Subtype.ext hp⟩
  rw [hrange]
  exact hval.isOpen_range.preimage continuous_subtype_val

variable (K : CompactOpenSubgroup (GeneralLinear n E))
variable (L : CompactOpenSubgroup ↥(GeneralLinear.upperTriangularSubgroup n E))

/-- The underlying full and upper triangular matrices of the two compact factors. -/
def compactMatrixHaarChart (q : ↥K.toSubgroup × ↥L.toSubgroup) : Mat × ↥Tri :=
  (q.1.val.val, (upperTriangularUnitsEquiv F E n q.2.val).val)

/-- The product of the two matrix value charts is an open embedding. -/
theorem isOpenEmbedding_compactMatrixHaarChart :
    IsOpenEmbedding (compactMatrixHaarChart F E n K L) :=
  ((isOpenEmbedding_generalLinearVal F E n).comp K.1.isOpen.isOpenEmbedding_subtypeVal).prodMap
    ((isOpenEmbedding_upperTriangularVal F E n).comp L.1.isOpen.isOpenEmbedding_subtypeVal)

variable [IsTopologicalRing E]

/-- Normalized Haar on the two compact open groups gives a locally constant density in
the full and upper triangular matrix chart, supported exactly on its image. -/
theorem exists_normalizedHaar_matrix_chartDensity
    [MeasurableSpace K.toSubgroup] [BorelSpace K.toSubgroup]
    [MeasurableSpace L.toSubgroup] [BorelSpace L.toSubgroup]
    [MeasurableSpace Mat] [BorelSpace Mat] [MeasurableSpace Tri] [BorelSpace Tri]
    (μ : Measure (Mat × Tri)) [μ.IsAddHaarMeasure] :
    letI : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp K.2
    letI : CompactSpace L.toSubgroup := isCompact_iff_compactSpace.mp L.2
    ∃ f : LocallyConstant (Mat × Tri) ℝ≥0, HasCompactSupport (f : Mat × Tri → ℝ≥0) ∧
      tsupport (f : Mat × Tri → ℝ≥0) = range (compactMatrixHaarChart F E n K L) ∧
      Measure.map (compactMatrixHaarChart F E n K L)
        ((normalizedHaar K.toSubgroup).prod (normalizedHaar L.toSubgroup)) =
        μ.withDensity (fun x => (f x : ℝ≥0∞)) := by
  let _ : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp K.2
  let _ : CompactSpace L.toSubgroup := isCompact_iff_compactSpace.mp L.2
  obtain ⟨hT2, hLC, hSC⟩ := finiteAlgebraTopology F E
  have : T2Space Mat := inferInstanceAs (T2Space (Fin n → Fin n → E))
  have : LocallyCompactSpace Mat := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  have : SecondCountableTopology Mat :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  have hclosed : IsClosed (Tri : Set Mat) := isClosed_setOfPred_blockTriangular
  have : LocallyCompactSpace Tri := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology Tri := IsEmbedding.subtypeVal.secondCountableTopology
  have : IsTopologicalRing Tri := IsTopologicalSemiring.toIsTopologicalRing inferInstance
  let i := K.toSubgroup.subtype
  let j := (upperTriangularUnitsEquiv F E n).toMonoidHom.comp L.toSubgroup.subtype
  have hi : IsOpenEmbedding (fun k => (i k : Mat)) :=
    (isOpenEmbedding_generalLinearVal F E n).comp K.1.isOpen.isOpenEmbedding_subtypeVal
  have hj : IsOpenEmbedding (fun p => (j p : Tri)) :=
    (isOpenEmbedding_upperTriangularVal F E n).comp L.1.isOpen.isOpenEmbedding_subtypeVal
  exact exists_normalizedHaar_prod_chartDensity i j hi hj μ

end Matrix

/-- The additive density comparison for the two compact open matrix factors used in the
twisted conjugation map. -/
def MatrixHaarChartStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type v) [CommRing E] [Algebra F E] [Module.Finite F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (n : ℕ)
    (K : CompactOpenSubgroup (GeneralLinear n E))
    (L : CompactOpenSubgroup ↥(GeneralLinear.upperTriangularSubgroup n E)),
    let M := Matrix (Fin n) (Fin n) E
    let U := Matrix.blockTriangularSubalgebra F E (id : Fin n → Fin n)
    ∀ [MeasurableSpace K.toSubgroup] [BorelSpace K.toSubgroup]
      [MeasurableSpace L.toSubgroup] [BorelSpace L.toSubgroup]
      [MeasurableSpace M] [BorelSpace M] [MeasurableSpace U] [BorelSpace U]
      (μ : Measure (M × U)) [μ.IsAddHaarMeasure],
      letI : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp K.2
      letI : CompactSpace L.toSubgroup := isCompact_iff_compactSpace.mp L.2
      ∃ f : LocallyConstant (M × U) ℝ≥0, HasCompactSupport (f : M × U → ℝ≥0) ∧
        tsupport (f : M × U → ℝ≥0) = range (compactMatrixHaarChart F E n K L) ∧
        Measure.map (compactMatrixHaarChart F E n K L)
          ((normalizedHaar K.toSubgroup).prod (normalizedHaar L.toSubgroup)) =
          μ.withDensity (fun x => (f x : ℝ≥0∞))

theorem matrixHaarChart : MatrixHaarChartStatement.{u, v} := by
  intro F _ _ _ _ E _ _ _ _ _ _ n K L M U _ _ _ _ _ _ _ _ μ _
  exact exists_normalizedHaar_matrix_chartDensity F E n K L μ

end Langlands.BaseChange
