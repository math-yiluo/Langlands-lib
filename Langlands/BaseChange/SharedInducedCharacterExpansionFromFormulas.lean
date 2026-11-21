import Langlands.BaseChange.TwistedInducedCharacterFormulaStatement
import Langlands.BaseChange.SigmaLiftInductionReduction
import Langlands.BaseChange.ExternalTensorTwistedCharacter

/-! # Shared induced character expansions from the induced character formulas

The ordinary and twisted cases of Henniart–Lemaire (2011), II.4.5 (3), taken as premises, give
the Library's `SharedInducedCharacterExpansionStatement`. The two formulas are not proved here.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.BaseChange

open GeneralLinear JacquetLanglands HarmonicAnalysis

universe u v uV uW

/-- The tensor product of the block σ-intertwiners is the tensor map of their linear maps. -/
theorem leviTensorIntertwiner_toLinearMap {F : Type u} [CommRing F] {E : Type v} [CommRing E]
    [Algebra F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i)}
    (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)) :
    (leviTensorIntertwiner σ B A).toLinearMap = PiTensorProduct.map fun i => (A i).toLinearMap :=
  rfl

/-- The ordinary and twisted induced character formulas imply the shared finite expansion
of the induced characters at norm-associated regular points. -/
def SharedInducedCharacterExpansionFormulaReductionStatement : Prop :=
  InducedCharacterFormulaStatement.{u, uV} →
  TwistedInducedCharacterFormulaStatement.{u, v, uW} →
  SharedInducedCharacterExpansionStatement.{u, v, uV, uW}

/-- Choose a Levi class system and σ-conjugate representatives with exact block norms, then
factor the Levi character values through the external tensor product. -/
theorem sharedInducedCharacterExpansion_of_formulas :
    SharedInducedCharacterExpansionFormulaReductionStatement.{u, v, uV, uW} := by
  intro hO hT F _ _ _ _ _ E _ _ _ _ _ _ σ l n hE hn B δ γ hnorm hreg
  have hσ : σ ^ l = 1 := hE.pow_eq_one
  obtain ⟨k, m, hm⟩ := exists_isLeviClassSystem B hreg
  have hrep : ∀ j, ∃ (x : GeneralLinear n E) (d : B.Levi E),
      x⁻¹ * δ * entrywiseAut σ n x = B.leviEmbedding E d ∧
        ∀ i, cyclicNorm σ l (d i) = baseChange F E (B.size i) (m j i) ∧
          IsRegularSemisimple (m j i) := by
    intro j
    obtain ⟨x, hx⟩ := hm.1 j
    have ha : IsNormAssociated σ l δ (B.leviEmbedding F (m j)) := by
      have h := hnorm.twistedConj hσ 1 x
      rwa [inv_one, one_mul, map_one, mul_one, hx] at h
    have hr : IsRegularSemisimple (B.leviEmbedding F (m j)) :=
      hx ▸ isRegularSemisimple_conj hreg x
    exact regularLeviNormRepresentative F E σ l n hσ B (m j) δ ha hr
  choose x d hxd hdn using hrep
  refine ⟨k, d, m, fun j => relativeDiscriminantWeight B (m j), ?_, ?_, ?_⟩
  · intro j i
    exact ⟨⟨1, by rw [inv_one, one_mul, mul_one, (hdn j i).1]⟩, (hdn j i).2⟩
  · intro V _ _ π hπ hirr _ a ha
    have : ∀ i, T2Space (GeneralLinear (B.size i) F) := fun i =>
      LocalFieldTopology.generalLinear_t2Space F (B.size i)
    have : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) F) := fun i =>
      LocalFieldTopology.generalLinear_locallyCompactSpace F (B.size i)
    have : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) F) := fun i =>
      LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (B.size i)
    have : ∀ i, SecondCountableTopology (GeneralLinear (B.size i) F) := fun i =>
      LocalFieldTopology.generalLinear_secondCountableTopology F (B.size i)
    have hL : ∀ j, HasCharacterValue (B.blockTensor π) (FiniteTensor.isAdmissible_external π hπ)
        (m j) (∏ i, a j i) := by
      intro j
      have h := hasTwistedCharacterValue_external π hπ (fun _ => 1) (m j) (a j)
        (fun i => (hasTwistedCharacterValue_one_iff _ _ _ _).mpr (ha j i))
      have h1 : (PiTensorProduct.map fun i => (1 : Module.End ℂ (V i))) = 1 :=
        PiTensorProduct.map_id
      rw [h1] at h
      exact (hasTwistedCharacterValue_one_iff _ _ _ _).mp h
    exact hO F n hn B V π hπ hirr γ hreg k m hm (fun j => ∏ i, a j i) hL
  · intro W _ _ P hP A hirr _ b hb
    have : ∀ i, T2Space (GeneralLinear (B.size i) E) := fun i =>
      LocalFieldTopology.generalLinear_t2Space E (B.size i)
    have : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E) := fun i =>
      LocalFieldTopology.generalLinear_locallyCompactSpace E (B.size i)
    have : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E) := fun i =>
      LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (B.size i)
    have : ∀ i, SecondCountableTopology (GeneralLinear (B.size i) E) := fun i =>
      LocalFieldTopology.generalLinear_secondCountableTopology E (B.size i)
    have hL : ∀ j, HasTwistedCharacterValue (B.blockTensor P)
        (FiniteTensor.isAdmissible_external P hP) (leviTensorIntertwiner σ B A).toLinearMap
        (d j) (∏ i, b j i) := by
      intro j
      rw [leviTensorIntertwiner_toLinearMap]
      exact hasTwistedCharacterValue_external P hP (fun i => (A i).toLinearMap) (d j) (b j)
        (fun i => hb j i)
    exact hT F E σ l n hE hn B W P hP A hirr δ γ hnorm hreg k m hm d
      (fun j => ⟨⟨x j, hxd j⟩, fun i => (hdn j i).1⟩) (fun j => ∏ i, b j i) hL

end Langlands.BaseChange
