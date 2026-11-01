import Langlands.Representation.GodementJacquet.InverseTransposeProductAnalytics
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.Representation.RankinSelberg.MultiplicativityStatement

/-!
# Canonical analytic inputs for the reversed inverse-transpose block family

These adapters identify the actual reversed family in the published matrix
analytic predicate, and transport its admissibility and scalar central action.
They do not supply the noncompact analytic-induction argument.
-/

noncomputable section

universe uF uV

namespace Langlands.GeneralLinear

/-- Inverse transpose sends a scalar matrix to the inverse scalar matrix. -/
theorem inverseTranspose_scalar {F : Type uF} [Field F] (n : ℕ) (z : Fˣ) :
    inverseTranspose n F (Matrix.GeneralLinearGroup.scalar (Fin n) z) =
      Matrix.GeneralLinearGroup.scalar (Fin n) z⁻¹ := by
  apply Units.ext
  change (((Matrix.GeneralLinearGroup.scalar (Fin n) z)⁻¹ :
    GeneralLinear n F).val).transpose = _
  rw [← map_inv (Matrix.GeneralLinearGroup.scalar (Fin n)) z]
  change (Matrix.scalar (Fin n) (↑(z⁻¹) : F)).transpose =
    Matrix.scalar (Fin n) (↑(z⁻¹) : F)
  simp

end Langlands.GeneralLinear

namespace Langlands.Classification

/-- The whole-carrier scalar central character of the inverse-transpose
pullback is the inverse of the original character. -/
theorem hasGLCentralCharacter_comp_inverseTranspose
    {F : Type uF} [Field F] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ (GeneralLinear n F) V} {ω : Fˣ →* ℂˣ}
    (h : HasGLCentralCharacter F n σ ω) :
    HasGLCentralCharacter F n
      (σ.comp (GeneralLinear.inverseTranspose n F).toMonoidHom) ω⁻¹ := by
  intro z v
  change σ (GeneralLinear.inverseTranspose n F
    (Matrix.GeneralLinearGroup.scalar (Fin n) z)) v = _
  rw [GeneralLinear.inverseTranspose_scalar]
  simpa using h z⁻¹ v

end Langlands.Classification

namespace Langlands.GodementJacquet

open HarmonicAnalysis RankinSelberg

/-- The complete reversed dependent family of actual inverse-transpose
pullback representations, on the original carriers in reversed order. -/
def reversedInverseTransposeBlocks {F : Type uF} [Field F] {k : ℕ}
    (m : Fin k → ℕ) {V : Fin k → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (V i)) :
    ∀ i : Fin k, Representation ℂ (GeneralLinear (m i.rev + 1) F) (V i.rev) :=
  fun i => (σ i.rev).comp (GeneralLinear.inverseTranspose (m i.rev + 1) F).toMonoidHom

/-- Reversal retains the sum of the actual positive block ranks. -/
theorem sum_reversedSuccBlocks {k t : ℕ} (m : Fin k → ℕ)
    (h : ∑ i, (m i + 1) = t + 1) :
    ∑ i : Fin k, (m i.rev + 1) = t + 1 :=
  (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h

/-- Admissibility is preserved for every member of the actual reversed
inverse-transpose family. -/
theorem isAdmissible_reversedInverseTransposeBlocks
    {F : Type uF} [Field F] [TopologicalSpace F] {k : ℕ}
    (m : Fin k → ℕ) {V : Fin k → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (V i))
    (hσ : ∀ i, IsAdmissible (σ i)) :
    ∀ i : Fin k, IsAdmissible (reversedInverseTransposeBlocks m σ i) :=
  fun i => isAdmissible_comp_continuousMulEquiv (σ i.rev)
    (GeneralLinear.inverseTransposeContinuous (m i.rev + 1) F) (hσ i.rev)

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance twoBlockReversalTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance twoBlockReversalValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance twoBlockReversalLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance twoBlockReversalGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance twoBlockReversalGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

/-- Each block's actual transformed analytic assertion is precisely the
ordinary assertion for the corresponding reversed pullback block. -/
theorem matrixAnalyticAssertions_reversedInverseTransposeBlocks
    {k : ℕ} (m : Fin k → ℕ) {V : Fin k → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (V i))
    (P : Fin k → Polynomial ℂ)
    (h : ∀ i, IotaMatrixAnalyticAssertions F (σ i) (P i)) :
    ∀ i : Fin k,
      MatrixAnalyticAssertions F (reversedInverseTransposeBlocks m σ i) (P i.rev) := by
  intro i
  exact (iotaMatrixAnalyticAssertions_iff_comp_inverseTranspose
    F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier (m i.rev)) (P i.rev)).mp (h i.rev)

/-- With canonical topology and Haar measure, the transformed assertion for
upper normalized induction is the ordinary assertion for upper normalized
induction of the complete reversed inverse-transpose block family. This
includes the reindexing of the proposed polynomial factors. -/
theorem iotaMatrixAnalyticAssertions_succBlocks_iff
    {k t : ℕ} (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Fin k → Type uV} [hadd : ∀ i, AddCommGroup (V i)]
    [hmod : ∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (V i))
    (hσ : ∀ i, IsSmooth (σ i)) (P : Fin k → Polynomial ℂ) :
    letI : ∀ i : Fin k, AddCommGroup (V i.rev) := fun i => hadd i.rev
    letI : ∀ i : Fin k, Module ℂ (V i.rev) := fun i => hmod i.rev
    IotaMatrixAnalyticAssertions F
        (F.canonicalNormalizedProductInduced (RankinSelberg.succBlockShape m h) σ)
        (∏ i, P i) ↔
      MatrixAnalyticAssertions F
        (F.canonicalNormalizedProductInduced
          (RankinSelberg.succBlockShape (fun i => m i.rev) (sum_reversedSuccBlocks m h))
          (V := fun i => V i.rev) (reversedInverseTransposeBlocks m σ))
        (∏ i : Fin k, P i.rev) := by
  let : ∀ i : Fin k, AddCommGroup (V i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin k, Module ℂ (V i.rev) := fun i => hmod i.rev
  have hP : (∏ i : Fin k, P i.rev) = ∏ i, P i :=
    Equiv.prod_comp Fin.revPerm P
  rw [hP]
  exact iotaMatrixAnalyticAssertions_product_iff F.canonicalTopologicalData
    (RankinSelberg.succBlockShape m h) σ hσ
    F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier t) (∏ i, P i)

end Padic
end Langlands.GodementJacquet
