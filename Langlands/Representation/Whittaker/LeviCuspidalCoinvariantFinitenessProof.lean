import Langlands.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessStatement
import Langlands.Representation.Whittaker.SupercuspidalCoinvariantFinitenessProof
import Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof
import Langlands.Representation.Tensor.ProductCharacterDecomposition
import Langlands.Representation.Jacquet.LocalizationTransport
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# Finite twisted coinvariants of irreducible cuspidal Levi representations

Factor the representation into irreducible supercuspidal block representations, restrict
the character to each block, and transport finite dimensionality of the tensor of the
blockwise coinvariants to the original quotient.
-/

noncomputable section

namespace Langlands.Whittaker

universe uF uV

/-- The finite-dimensionality part of the cuspidal-Levi coefficient step in
Bernstein--Zelevinsky (1976), Theorem 7.12(5), for every locally constant character. -/
theorem leviCuspidalCoinvariantFiniteness :
    LeviCuspidalCoinvariantFinitenessStatement.{uF, uV} := by
  intro p _ F T n hn B
  let := T.topology
  intro σ hσ hcuspidal η hη
  obtain ⟨A, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviCuspidalFactorization.{uF, uV, uV}
      p F T n hn B σ hσ hcuspidal
  let U := fun i : Fin B.length => GeneralLinear.upperUnipotent (B.size i) F.Carrier
  let θ := FiniteTensor.coordinateCharacter U η
  have hθ (i : Fin B.length) : IsLocallyConstant fun u => (θ i u : ℂ) :=
    FiniteTensor.isLocallyConstant_coordinateCharacter U hη i
  have hfinite (i : Fin B.length) :
      FiniteDimensional ℂ (Jacquet.Localization.Coinvariants
        (A i).obj.representation (U i) (θ i)) :=
    supercuspidalCoinvariantFiniteness.{uF, uV}
      p F T (B.size i) (B.positive i) (A i).obj
      (A i).property.1 (A i).property.2 (θ i) (hθ i)
  let : ∀ i, FiniteDimensional ℂ
      (Jacquet.Localization.Coinvariants (A i).obj.representation (U i) (θ i)) := hfinite
  have hcharacter : FiniteTensor.productCharacter U θ = η :=
    FiniteTensor.productCharacter_coordinateCharacter U η
  let E := Jacquet.Localization.representationEquiv (Subgroup.pi Set.univ U)
    (FiniteTensor.productCharacter U θ) e
  let L := FiniteTensor.characterLocalizationEquiv (fun i => (A i).obj.representation) U θ
  have hproduct : FiniteDimensional ℂ (Jacquet.Localization.Coinvariants σ.representation
      (Subgroup.pi Set.univ U) (FiniteTensor.productCharacter U θ)) :=
    (L.symm.trans E.symm).finiteDimensional
  exact hcharacter ▸ hproduct

end Langlands.Whittaker
