import Langlands.Representation.Classification.LeviTemperedUnitarityStatement
import Langlands.Representation.Classification.BlockTensorTemperedProof
import Langlands.Representation.Classification.TemperedHaarProof
import Langlands.Representation.Classification.TemperedUnitarityProof
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.Tensor.UnitaryProof

/-!
# Unitarity of analytically tempered actual block Levi representations

Factor the irreducible admissible action on its original carrier universe,
reflect temperedness to each block using the published Haar and tensor
comparisons, apply ambient tempered unitarity to the factors, and pull back the
finite tensor positive form to the supplied carrier.
-/

namespace Langlands

universe uF uV

/-- Every irreducible analytically tempered representation of an actual GL block
Levi admits an invariant positive definite Hermitian form on its given carrier. -/
theorem glLeviTemperedUnitarity :
    GLLeviTemperedUnitarityStatement.{uF, uV} := by
  classical
  intro p _ F T
  let := T.topology
  intro n hn B
  dsimp only
  intro m₀ b₀ μ hμ V _ _ σ hi ht
  let := T.leviTopologicalGroup B
  let S : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) :=
    SmoothRep.of σ ht.1.1
  obtain ⟨A, hAi, hAa, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviAdmissibleFactorization p F T n hn B S hi ht.1
  have hFactors : ∀ i, T.IsTempered (A i).representation := by
    apply (glBlockTensorTempered p F T n hn B (fun i => (A i : Type uV))
      (fun i => (A i).representation) hAi hAa).mpr
    intro m₁ b₁ ν hν
    exact isTemperedModCenter_of_equiv e ν
      (@glLeviTemperedHaarExtension p _ F T n B
        m₀ b₀ μ hμ V _ _ σ ht m₁ b₁ ν hν)
  have hUnitary : ∀ i, IsUnitarizable (A i).representation := by
    intro i
    exact glTemperedUnitarity.{uF, uV} p F T (B.size i) (B.positive i) (A i)
      (A i).representation (hAi i) (hFactors i)
  let b : ∀ i, InvariantPositiveForm (A i).representation :=
    fun i => Classical.choice (hUnitary i)
  obtain ⟨bT, _⟩ := FiniteTensor.invariantPositiveForm (Fin B.length)
    (fun i => GeneralLinear (B.size i) F.Carrier)
    (fun i => (A i : Type uV)) (fun i => (A i).representation) b
  exact ⟨bT.ofEquiv e⟩

end Langlands
