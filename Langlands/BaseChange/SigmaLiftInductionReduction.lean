import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.BaseChange.SigmaLiftCharacterIdentityStatement

/-!
# Conditional reduction of σ-lift induction to induced character expansions

Use the σ-lift/Shintani equivalence on the factors and on the induced representations.
In between, compare finite expansions with common geometric coefficients, as in the
ordinary and twisted versions of Henniart–Lemaire II.4.5 (3). The expansions used here
are explicit premises, not theorems of this module.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.BaseChange

open GeneralLinear JacquetLanglands

/-- The paired part of the ordinary and twisted induced character formulas on associated
regular pairs, after factoring the Levi character into block characters. The two sums use
the same coefficients and associated block arguments. The geometric data may be chosen
before the representations and include the case of an empty sum. This formulation does
not specify the geometric index set or the discriminant weights of HL II.4.5 (3). -/
def SharedInducedCharacterExpansionStatement.{u, v, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l → 0 < n →
    ∀ (B : BlockShape n) (δ : GeneralLinear n E) (γ : GeneralLinear n F),
      IsNormAssociated σ l δ γ → IsRegularSemisimple γ →
      ∃ (k : ℕ) (d : Fin k → B.Levi E) (g : Fin k → B.Levi F) (w : Fin k → ℂ),
        (∀ j i, IsNormAssociated σ l (d j i) (g j i) ∧ IsRegularSemisimple (g j i)) ∧
        (∀ (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
          (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
          (hπ : ∀ i, IsAdmissible (π i)),
          (∀ i, (π i).IsIrreducible) →
          ((LocalFieldData.ofInstances F).normalizedProductInduced B π).IsIrreducible →
          ∀ (a : Fin k → Fin B.length → ℂ),
            (∀ j i,
              haveI := LocalFieldTopology.generalLinear_t2Space F (B.size i)
              haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (B.size i)
              haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (B.size i)
              HasCharacterValue (π i) (hπ i) (g j i) (a j i)) →
            haveI := LocalFieldTopology.generalLinear_t2Space F n
            haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
            haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
            HasCharacterValue ((LocalFieldData.ofInstances F).normalizedProductInduced B π)
              (isAdmissible_normalizedProductInduced B π hπ) γ (∑ j, w j * ∏ i, a j i)) ∧
        (∀ (W : Fin B.length → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
          (P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i))
          (hP : ∀ i, IsAdmissible (P i)) (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)),
          (∀ i, (P i).IsIrreducible) →
          ((LocalFieldData.ofInstances E).normalizedProductInduced B P).IsIrreducible →
          ∀ (b : Fin k → Fin B.length → ℂ),
            (∀ j i,
              haveI := LocalFieldTopology.generalLinear_t2Space E (B.size i)
              haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E (B.size i)
              haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (B.size i)
              HasTwistedCharacterValue (P i) (hP i) (A i).toLinearMap (d j i) (b j i)) →
            haveI := LocalFieldTopology.generalLinear_t2Space E n
            haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E n
            haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
            HasTwistedCharacterValue ((LocalFieldData.ofInstances E).normalizedProductInduced B P)
              (isAdmissible_normalizedProductInduced B P hP)
              (inducedSigmaIntertwiner σ B A).toLinearMap δ (∑ j, w j * ∏ i, b j i))

/-- The two instances of the character-identity equivalence and the common finite character
expansion imply the Library's exact σ-lift induction statement. The induced carriers lie
in the maxima of the respective field and factor-carrier universes. -/
def SigmaLiftInductionReductionStatement.{u, v, uV, uW} : Prop :=
  SigmaLiftCharacterIdentityStatement.{u, v, uV, uW} →
  SigmaLiftCharacterIdentityStatement.{u, v, max u uV, max v uW} →
  SharedInducedCharacterExpansionStatement.{u, v, uV, uW} →
  SigmaLiftInductionStatement.{u, v, uV, uW}

/-- Compare the common character expansions by factoring out the product of the inducing
scalars, then use the reverse character-identity equivalence for the induced representations. -/
theorem sigmaLiftInductionReduction : SigmaLiftInductionReductionStatement.{u, v, uV, uW} := by
  intro hBlock hInduced hExpansion F _ _ _ _ _ E _ _ _ _ _ _ σ l n hE hn B V _ _ π hπ
    W _ _ P hP A c hirrπ hirrP hLift hirrπ' hirrP'
  have hFactor (i : Fin B.length) :=
    (hBlock F E σ l (B.size i) hE (π i) (hπ i) (P i) (hP i)
      (hirrπ i) (hirrP i) (A i) (c i)).mp (hLift i)
  let π' := (LocalFieldData.ofInstances F).normalizedProductInduced B π
  let P' := (LocalFieldData.ofInstances E).normalizedProductInduced B P
  let hπ' : IsAdmissible π' := isAdmissible_normalizedProductInduced B π hπ
  let hP' : IsAdmissible P' := isAdmissible_normalizedProductInduced B P hP
  let A' := inducedSigmaIntertwiner σ B A
  refine ⟨hπ', hP', A', (hInduced F E σ l n hE π' hπ' P' hP' hirrπ' hirrP' A'
    (∏ i, c i)).mpr ?_⟩
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hFactor i).1), ?_⟩
  intro δ γ hnorm hreg
  obtain ⟨k, d, g, w, hpairs, hF, hT⟩ := hExpansion F E σ l n hE hn B δ γ hnorm hreg
  have hValues (j : Fin k) (i : Fin B.length) :=
    (hFactor i).2 (d j i) (g j i) (hpairs j i).1 (hpairs j i).2
  choose a ha hb using hValues
  refine ⟨∑ j, w j * ∏ i, a j i, hF V π hπ hirrπ hirrπ' a ha, ?_⟩
  have hs : (∑ j, w j * ∏ i, (c i * a j i)) = (∏ i, c i) * ∑ j, w j * ∏ i, a j i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.prod_mul_distrib, mul_left_comm]
  simpa only [hs] using hT W P hP A hirrP hirrP' (fun j i => c i * a j i) hb

end Langlands.BaseChange
