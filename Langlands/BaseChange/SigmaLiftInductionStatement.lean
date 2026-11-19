import Langlands.BaseChange.Norm
import Langlands.BaseChange.TwistedCharacter
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.Group.GL.LocalFieldTopology

/-!
# Sigma-lifts and irreducible normalized parabolic induction

The proposition below states the existential-intertwiner version of
Henniart–Lemaire, II.4.4, Lemme. Its proof is a separate obligation.
-/

open scoped BigOperators

namespace Langlands.BaseChange

universe u v uV uW

/-- Sigma-lifts commute with normalized induction when both products are
irreducible, with the product of the inducing constants. -/
def SigmaLiftInductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l → 0 < n →
    ∀ (B : GeneralLinear.BlockShape n)
      (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
      (hπ : ∀ i, IsAdmissible (π i))
      (W : Fin B.length → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
      (P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i))
      (hP : ∀ i, IsAdmissible (P i))
      (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)) (c : Fin B.length → ℂ),
      (∀ i, (π i).IsIrreducible) → (∀ i, (P i).IsIrreducible) →
      (∀ i,
        haveI := LocalFieldTopology.generalLinear_t2Space F (B.size i)
        haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (B.size i)
        haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (B.size i)
        haveI := LocalFieldTopology.generalLinear_t2Space E (B.size i)
        haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E (B.size i)
        haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (B.size i)
        IsSigmaLift σ l (π i) (hπ i) (P i) (hP i) (A i) (c i)) →
      ((LocalFieldData.ofInstances F).normalizedProductInduced B π).IsIrreducible →
      ((LocalFieldData.ofInstances E).normalizedProductInduced B P).IsIrreducible →
      ∃ (hπ' : IsAdmissible ((LocalFieldData.ofInstances F).normalizedProductInduced B π))
        (hP' : IsAdmissible ((LocalFieldData.ofInstances E).normalizedProductInduced B P))
        (A' : SigmaIntertwiner σ n ((LocalFieldData.ofInstances E).normalizedProductInduced B P)),
        haveI := LocalFieldTopology.generalLinear_t2Space F n
        haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
        haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
        haveI := LocalFieldTopology.generalLinear_t2Space E n
        haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E n
        haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
        IsSigmaLift σ l ((LocalFieldData.ofInstances F).normalizedProductInduced B π) hπ'
          ((LocalFieldData.ofInstances E).normalizedProductInduced B P) hP' A' (∏ i, c i)

end Langlands.BaseChange
