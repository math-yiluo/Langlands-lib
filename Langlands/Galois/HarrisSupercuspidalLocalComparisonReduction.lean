import Langlands.Galois.CommonTwistLocalComparison
import Langlands.Galois.Harris1999Theorem59iiParameterStatement
import Langlands.Galois.HarrisSupercuspidalLocalComparisonStatement
import Langlands.Galois.PureDeterminantWeight

/-! # Reduction of the Harris pairwise comparison to the canonical comparison -/

noncomputable section

universe uK uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Automorphic
open NumberField (IsTotallyComplex IsCMField)
open scoped Valued

/-- The canonical local parameter and absolute irreducibility imply the pairwise
    comparison of actual restrictions at a split supercuspidal place. -/
def HarrisSupercuspidalLocalComparisonReductionStatement : Prop :=
  Harris1999Theorem59iiParameterStatement.{uK, uL, uV, uW} →
    HarrisSupercuspidalRestrictionIrreducibleStatement.{uK, uL, uV, uW} →
    HarrisSupercuspidalLocalComparisonStatement.{uK, uL, uV, uW}

private theorem isAbsolutelyIrreducible_of_scalarExtensionAlong
    {F G : Type*} [Field F] [Monoid G] (A : FiniteRepresentation F G)
    (h : Representation.IsIrreducible (scalarExtensionAlong
      (algebraMap F (AlgebraicClosure F)) A).representation) :
    A.IsAbsolutelyIrreducible := by
  let P (a : Algebra F (AlgebraicClosure F)) : Prop :=
    letI := a
    Representation.IsIrreducible (A.extendCoefficients (AlgebraicClosure F)).representation
  change P (AlgebraicClosure.instAlgebra F)
  exact Eq.mp (congrArg P (toAlgebra_algebraMap (R := F) (S := AlgebraicClosure F))) h

set_option maxHeartbeats 1200000 in
/-- The canonical comparison and absolute irreducibility imply the exact
    pairwise comparison, including its common-weight cancellation. -/
theorem harrisSupercuspidalLocalComparison_of_canonical :
    HarrisSupercuspidalLocalComparisonReductionStatement.{uK, uL, uV, uW} := by
  intro hParam hIrr K _ _ _ _ K₀ hdeg hcm r hr S T P Q v hSreg hTreg hScsd hTcsd hsplit hPsc hQsc
    L _ _ ι R U m hR hU hRrank hUrank hRs hUs lam hchar hlocal
  obtain ⟨Φ, hΦ⟩ := hParam K K₀ hdeg hcm r hr v hsplit
  obtain ⟨L₀, f₀, n₀, ι₀, C, m₀, hC, hCrank, hCs, hCΦ⟩ := hΦ S P hSreg hScsd hPsc
  obtain ⟨L₁, f₁, n₁, ι₁, D, m₁, hD, hDrank, hDs, hDΦ⟩ := hΦ T Q hTreg hTcsd hQsc
  let : Field L₀ := f₀
  let : NumberField L₀ := n₀
  let : Field L₁ := f₁
  let : NumberField L₁ := n₁
  let p := CompletionPadic.residuePrime lam
  have hpchar : p ≠ residueCharacteristic v := by
    change CompletionPadic.residuePrime lam ≠ residueCharacteristic v
    rwa [← residueCharacteristic_eq_residuePrime, ne_comm]
  have hCanonical (e : PadicAlgCl p ≃+* ℂ) (lam₀ : FinitePlace L₀) (lam₁ : FinitePlace L₁)
      (j₀ : FiniteCompletion L₀ lam₀ →+* PadicAlgCl p)
      (j₁ : FiniteCompletion L₁ lam₁ →+* PadicAlgCl p)
      (hj₀ : Continuous j₀) (hj₁ : Continuous j₁)
      (hι₀ : ∀ x : L₀, e (j₀ (NumberField.FinitePlace.embedding lam₀ x)) = ι₀ x)
      (hι₁ : ∀ x : L₁, e (j₁ (NumberField.FinitePlace.embedding lam₁ x)) = ι₁ x) :
      letI : Algebra (FiniteCompletion L₀ lam₀) (PadicAlgCl p) := j₀.toAlgebra
      letI : Algebra (FiniteCompletion L₁ lam₁) (PadicAlgCl p) := j₁.toAlgebra
      Nonempty (FiniteRepresentation.Equiv
        ((atFinitePlace v (C ⟨lam₀, by simp⟩)).val.extendCoefficients (PadicAlgCl p))
        ((atFinitePlace v (D ⟨lam₁, by simp⟩)).val.extendCoefficients (PadicAlgCl p))) := by
    obtain ⟨eC⟩ := hCΦ p hpchar e lam₀ j₀ hj₀ hι₀
    obtain ⟨eD⟩ := hDΦ p hpchar e lam₁ j₁ hj₁ hι₁
    rw [hlocal] at eC
    exact ⟨eC.trans eD.symm⟩
  have hweights : m₀ = m₁ := by
    refine pureWeights_eq_of_localDeterminants_eq p v hpchar.symm ι₀ ι₁
      (Nat.succ_pos r) hC hD hCrank hDrank ?_
    intro e lam₀ lam₁ j₀ j₁ hj₀ hj₁ hι₀ hι₁
    exact mapped_determinantCharacter_eq_of_local_extendCoefficients_equiv
      (C ⟨lam₀, by simp⟩) (D ⟨lam₁, by simp⟩) j₀ j₁ v
      (hCanonical e lam₀ lam₁ j₀ j₁ hj₀ hj₁ hι₀ hι₁)
  subst m₁
  let i := coefficientCompletionEmbedding lam
  have hi := continuous_coefficientCompletionEmbedding lam
  obtain ⟨e, hι⟩ := exists_padicAlgClComplexEquiv_extending p
    (i.comp (NumberField.FinitePlace.embedding lam)) ι
  obtain ⟨lam₀, j₀, hp₀, hj₀, hι₀⟩ := exists_compatibleCoefficientCompletionEmbedding p e ι₀
  obtain ⟨lam₁, j₁, _, hj₁, hι₁⟩ := exists_compatibleCoefficientCompletionEmbedding p e ι₁
  let ℓ : {l : FinitePlace L // l ∉ (∅ : Finset (FinitePlace L))} := ⟨lam, by simp⟩
  let ℓ₀ : {l : FinitePlace L₀ // l ∉ (∅ : Finset (FinitePlace L₀))} := ⟨lam₀, by simp⟩
  let ℓ₁ : {l : FinitePlace L₁ // l ∉ (∅ : Finset (FinitePlace L₁))} := ⟨lam₁, by simp⟩
  have hCD := hCanonical e lam₀ lam₁ j₀ j₁ hj₀ hj₁ hι₀ hι₁
  have hCabs : (atFinitePlace v (C ℓ₀)).val.IsAbsolutelyIrreducible :=
    isAbsolutelyIrreducible_of_scalarExtensionAlong _
      (hIrr K K₀ hdeg hcm r hr S.isoClass v hSreg hScsd hsplit ⟨S, P, rfl, hPsc⟩
        L₀ ι₀ C m₀ hC hCrank hCs lam₀ (by simpa only [hp₀] using hpchar.symm))
  have hCspec := weakAssociationToSpectrum_of_class hCs P
  have hDspec := weakAssociationToSpectrum_of_class hDs Q
  have hRspec := weakAssociationToSpectrum_of_class hRs P
  have hUspec := weakAssociationToSpectrum_of_class hUs Q
  have hpos : 0 < (R ℓ).val.rank := by rw [hRrank ℓ]; exact Nat.succ_pos r
  obtain ⟨d, hd⟩ := pureWeightDifferenceEven ℓ₀ ℓ hpos hC hR hCspec hRspec
  have hCeq := eventually_frobeniusEulerPolynomial_map_eq_cyclotomicTwist_of_weakAssociation
    hd hC hR hCspec hRspec ℓ₀ ℓ e.toRingHom j₀ i hι₀ hι
  have hDeq := eventually_frobeniusEulerPolynomial_map_eq_cyclotomicTwist_of_weakAssociation
    hd hD hU hDspec hUspec ℓ₁ ℓ e.toRingHom j₁ i hι₁ hι
  exact localEquiv_of_commonTwist_of_canonicalComparison v (R ℓ) (U ℓ) (C ℓ₀) (D ℓ₁)
    (geometricCyclotomicPower K p (CompletionPadic.padicMap lam) d)
    (continuous_geometricCyclotomicPower K p _ (CompletionPadic.continuous_padicMap lam) d)
    i j₀ j₁ hi hj₀ hj₁ hCeq hDeq ((hCrank ℓ₀).trans (hRrank ℓ).symm)
    ((hDrank ℓ₁).trans (hUrank ℓ).symm) hCabs hCD

end Langlands.GaloisRepresentation
