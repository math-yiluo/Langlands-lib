import Langlands.Representation.Classification.UnitaryGenericStatement
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Group.GL.OneBlockShape
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.FinCases

/-! # Elementary actual unitary inducing parameters

A single block at exponent zero and two copies of the same block at opposite
strict exponents provide the local parameters used in finite flattening.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual block family consisting of one supplied representation. -/
def singletonUnitaryBlocks {r : ℕ} (hr : 0 < r)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear ((CuspidalSupport.LeviAdmissibility.oneBlock r hr).size i) F.Carrier) :=
  fun _ => δ

/-- A square-integrable unitary block at exponent zero is valid local data. -/
theorem isUnitaryGenericDatum_singleton {r : ℕ} (hr : 0 < r)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier))
    (hδ : letI := T.topology
      Representation.IsIrreducible δ.representation ∧
        IsUnitarizable δ.representation ∧ T.IsSquareIntegrable δ.representation) :
    IsUnitaryGenericDatum F T (CuspidalSupport.LeviAdmissibility.oneBlock r hr)
      (singletonUnitaryBlocks F T hr δ) (fun _ => 0) := by
  let := T.topology
  refine ⟨fun _ => hδ, ?_, ?_⟩
  · intro i
    norm_num
  · refine ⟨Equiv.refl _, fun _ => rfl, ?_⟩
    intro i
    exact ⟨by simp, ⟨Iso.refl _⟩⟩

/-- The actual one-block induction at exponent zero is the original block. -/
def singletonUnitaryProductIso {r : ℕ} (hr : 0 < r)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    T.twistedProductInduced (CuspidalSupport.LeviAdmissibility.oneBlock r hr)
      (singletonUnitaryBlocks F T hr δ) (fun _ => 0) ≅ δ := by
  letI := T.topology
  let B := CuspidalSupport.LeviAdmissibility.oneBlock r hr
  let τ := fun _ : Fin B.length => (T.segmentFactor δ 0).representation
  let i0 : Fin B.length := ⟨0, Nat.one_pos⟩
  let e := T.singleBlockNormalizedProductEquiv B rfl τ
    (fun _ => (T.segmentFactor δ 0).isSmooth) i0
  have hτ : τ i0 = δ.representation := by
    change realPowerTwist (T.determinantNorm r) 0 δ.representation = _
    exact realPowerTwist_zero _ _
  let eτ := equivOfRepresentationEq hτ
  refine SmoothRep.mkIso (e.trans ?_)
  refine (Representation.Equiv.mk eτ.toLinearEquiv ?_).trans
    (T.castRankEquiv rfl δ)
  intro g
  exact eτ.isIntertwining' _

/-- The two actual unitary blocks are the very same supplied representation. -/
def pairedUnitaryBlocks {r : ℕ} (hr : 0 < r)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    ∀ i, SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear ((BlockShape.uniform 2 r hr).size i) F.Carrier) :=
  fun _ => δ

/-- The ordered opposite exponents `(alpha, -alpha)`. -/
def pairedUnitaryExponents (α : ℝ) : Fin 2 → ℝ :=
  fun i => if (i : ℕ) = 0 then α else -α

/-- Swapping the two occurrences supplies exact Hermitian parameter matching. -/
theorem hasHermitianSymmetricParameters_paired {r : ℕ} (hr : 0 < r)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier)) (α : ℝ) :
    HasHermitianSymmetricParameters F T (BlockShape.uniform 2 r hr)
      (pairedUnitaryBlocks F T hr δ) (pairedUnitaryExponents α) := by
  let := T.topology
  refine ⟨Fin.revPerm, fun _ => rfl, ?_⟩
  intro i
  constructor
  · change pairedUnitaryExponents α i = -pairedUnitaryExponents α (Fin.rev i)
    fin_cases i <;> simp [pairedUnitaryExponents, Fin.rev]
  · exact ⟨Iso.refl _⟩

/-- Strict complementary exponents and a unitary square-integrable block give
valid two-factor local data with all multiplicities retained. -/
theorem isUnitaryGenericDatum_paired {r : ℕ} (hr : 0 < r)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear r F.Carrier))
    (hδ : letI := T.topology
      Representation.IsIrreducible δ.representation ∧
        IsUnitarizable δ.representation ∧ T.IsSquareIntegrable δ.representation)
    (α : ℝ) (hα0 : 0 < α) (hα : α < (1 / 2 : ℝ)) :
    IsUnitaryGenericDatum F T (BlockShape.uniform 2 r hr)
      (pairedUnitaryBlocks F T hr δ) (pairedUnitaryExponents α) := by
  let := T.topology
  refine ⟨fun _ => hδ, ?_, hasHermitianSymmetricParameters_paired F T hr δ α⟩
  intro i
  fin_cases i <;> simp only [pairedUnitaryExponents, one_ne_zero,
    ↓reduceIte] <;> constructor <;> linarith

end Langlands.Classification
