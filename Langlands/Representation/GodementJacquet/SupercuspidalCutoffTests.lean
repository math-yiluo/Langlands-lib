import Langlands.Representation.GodementJacquet.SupercuspidalCoefficientTests
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.HarmonicAnalysis.Distribution.Subspace

/-! # Actual determinant-unit cutoff matrix tests -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) (d : ℕ)

private theorem determinantUnitMatrix_isOpenEmbedding :
    letI := T.topology
    Topology.IsOpenEmbedding (fun g : (T.determinantNorm d).ker =>
      (g.val.val : Matrix (Fin d) (Fin d) F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  exact (RankinSelberg.isOpenEmbedding_generalLinear_val d).comp
    (T.isOpen_ker_determinantNorm d).isOpenEmbedding_subtypeVal

/-- Extend a test on the determinant-unit subgroup by zero directly into the
full matrix space, using its actual open embedding. -/
def determinantUnitTestToMatrixTest :
    letI := T.topology
    SchwartzBruhat (T.determinantNorm d).ker →ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin d) (Fin d) F.Carrier) := by
  letI := T.topology
  letI := T.fieldT2
  let e := determinantUnitMatrix_isOpenEmbedding T d
  exact (SchwartzBruhat.extendZero e.isOpen_range).comp
    (Hecke.TestFunction.pullback e.isEmbedding.toHomeomorph.symm).toLinearMap

@[simp]
theorem determinantUnitTestToMatrixTest_apply :
    letI := T.topology
    ∀ (φ : SchwartzBruhat (T.determinantNorm d).ker)
      (g : (T.determinantNorm d).ker),
      determinantUnitTestToMatrixTest T d φ g.val.val = φ g := by
  let := T.topology
  let := T.fieldT2
  intro φ g
  let e := determinantUnitMatrix_isOpenEmbedding T d
  change SchwartzBruhat.extendZero e.isOpen_range
    ((Hecke.TestFunction.pullback e.isEmbedding.toHomeomorph.symm) φ) g.val.val = _
  rw [SchwartzBruhat.extendZero_apply_of_mem e.isOpen_range _
    (Set.mem_range_self g)]
  simp only [Hecke.TestFunction.pullback_apply,
    Topology.IsEmbedding.toHomeomorph_symm_apply]

theorem determinantUnitTestToMatrixTest_eq_zero :
    letI := T.topology
    ∀ (φ : SchwartzBruhat (T.determinantNorm d).ker)
      (A : Matrix (Fin d) (Fin d) F.Carrier),
      (¬ ∃ g : (T.determinantNorm d).ker, g.val.val = A) →
      determinantUnitTestToMatrixTest T d φ A = 0 := by
  let := T.topology
  let := T.fieldT2
  intro φ A hA
  exact SchwartzBruhat.extendZero_apply_of_not_mem
    (determinantUnitMatrix_isOpenEmbedding T d).isOpen_range _ hA

theorem tsupport_determinantUnitTestToMatrixTest_subset :
    letI := T.topology
    ∀ φ : SchwartzBruhat (T.determinantNorm d).ker,
      tsupport (determinantUnitTestToMatrixTest T d φ :
        Matrix (Fin d) (Fin d) F.Carrier → ℂ) ⊆
        Set.range (fun g : (T.determinantNorm d).ker => g.val.val) := by
  let := T.topology
  let := T.fieldT2
  intro φ
  exact SchwartzBruhat.tsupport_extendZero_subset
    (determinantUnitMatrix_isOpenEmbedding T d).isOpen_range _

variable {d} (hd : 0 < d)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The genuine compact coefficient on the determinant-unit subgroup, linear
in the representation vector. -/
def supercuspidalDeterminantUnitCoefficient :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear d F.Carrier) V),
      IsSupercuspidal ρ → ∀ (ℓ : Module.Dual ℂ V),
      IsSmoothVector ρ.dual ℓ →
      V →ₗ[ℂ] SchwartzBruhat (T.determinantNorm d).ker := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup d
  intro ρ hρ ℓ hℓ
  exact
    { toFun := fun v =>
        ⟨fun g => ℓ (ρ g.val v),
          (matrixCoefficient_isLocallyConstant ρ ℓ v (hρ.1.1 v)).comp_continuous
            continuous_subtype_val,
          hasCompactSupport_determinantUnit_coefficient T hd ρ hρ v ℓ hℓ⟩
      map_add' := by
        intro v w
        ext g
        exact congrFun ((matrixCoefficient ρ ℓ).map_add v w) g.val
      map_smul' := by
        intro c v
        ext g
        exact congrFun ((matrixCoefficient ρ ℓ).map_smul c v) g.val }

/-- The coefficient is cut off to determinant norm one and extended by zero
to singular matrices and to every other determinant shell. -/
def supercuspidalCutoffMatrixTest :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear d F.Carrier) V),
      IsSupercuspidal ρ → ∀ (ℓ : Module.Dual ℂ V),
      IsSmoothVector ρ.dual ℓ →
      V →ₗ[ℂ] SchwartzBruhat (Matrix (Fin d) (Fin d) F.Carrier) := by
  letI := T.topology
  intro ρ hρ ℓ hℓ
  exact (determinantUnitTestToMatrixTest T d).comp
    (supercuspidalDeterminantUnitCoefficient T hd ρ hρ ℓ hℓ)

@[simp]
theorem supercuspidalCutoffMatrixTest_apply :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear d F.Carrier) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ) (v : V)
      (g : (T.determinantNorm d).ker),
      supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ v g.val.val =
        ℓ (ρ g.val v) := by
  let := T.topology
  intro ρ hρ ℓ hℓ v g
  exact determinantUnitTestToMatrixTest_apply T d _ g

theorem supercuspidalCutoffMatrixTest_apply_of_not_mem :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear d F.Carrier) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ) (v : V)
      (g : GeneralLinear d F.Carrier), T.determinantNorm d g ≠ 1 →
      supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ v g.val = 0 := by
  let := T.topology
  intro ρ hρ ℓ hℓ v g hg
  apply determinantUnitTestToMatrixTest_eq_zero T d
  rintro ⟨a, ha⟩
  have h := Units.ext ha
  exact hg (h ▸ a.property)

theorem supercuspidalCutoffMatrixTest_singular :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear d F.Carrier) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ) (v : V)
      (A : Matrix (Fin d) (Fin d) F.Carrier), ¬ IsUnit A →
      supercuspidalCutoffMatrixTest T hd ρ hρ ℓ hℓ v A = 0 := by
  let := T.topology
  intro ρ hρ ℓ hℓ v A hA
  apply determinantUnitTestToMatrixTest_eq_zero T d
  rintro ⟨g, rfl⟩
  exact hA g.val.isUnit

end Langlands.GodementJacquet
