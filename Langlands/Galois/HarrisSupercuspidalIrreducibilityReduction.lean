import Langlands.Galois.CoefficientIdentification
import Langlands.Galois.Harris1999Theorem59iiParameterStatement
import Langlands.Galois.PureLocalIrreducibility

/-! # Transfer from an irreducible Harris witness -/

noncomputable section

universe uK uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Automorphic
open NumberField (IsTotallyComplex IsCMField)
open scoped Valued

/-- One pure weakly associated family with absolutely irreducible restrictions
    away from the residue characteristic of the supercuspidal place suffices
    for the universal absolute irreducibility assertion. -/
def HarrisSupercuspidalIrreducibilityReductionStatement : Prop :=
  (∀ (K : Type uK) [Field K] [NumberField K] [IsCMField K]
    [CompactSpace (AdeleQuotient K)] (K₀ : IntermediateField ℚ K),
    Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ →
    ∀ (r : ℕ), 1 ≤ r → ∀ (v : FinitePlace K), Harris.conjPlace K v ≠ v →
    ∀ (S : CuspidalOperatorRealization K r) (P : CuspidalSpectralPresentation.{uK, uW} S),
      S.isoClass.IsRegularAlgebraic → S.isoClass.IsConjugateSelfDual →
      (P.localComponent v).IsSupercuspidal →
      ∃ (L₀ : Type uL) (fieldL₀ : Field L₀),
        letI : Field L₀ := fieldL₀
        ∃ (numberFieldL₀ : NumberField L₀),
          letI : NumberField L₀ := numberFieldL₀
          ∃ (ι₀ : L₀ →+* ℂ) (C : Collection.{uK, uL, uV} K L₀ ∅) (m₀ : ℤ),
            IsPureCompatible ∅ C m₀ ∧ HasRank ∅ C (r + 1) ∧
            CuspidalOperatorRealization.IsoClass.IsWeaklyAssociated.{uK, uL, uV, uW}
              S.isoClass ι₀ ∅ C ∧
            ∀ lam₀ : FinitePlace L₀, residueCharacteristic v ≠ residueCharacteristic lam₀ →
              (atFinitePlace v (C ⟨lam₀, by simp⟩)).val.IsAbsolutelyIrreducible) →
    HarrisSupercuspidalRestrictionIrreducibleStatement.{uK, uL, uV, uW}

set_option maxHeartbeats 800000 in
theorem harrisSupercuspidalRestrictionIrreducible_of_pureWitness :
    HarrisSupercuspidalIrreducibilityReductionStatement.{uK, uL, uV, uW} := by
  intro hWitness K _ _ _ _ K₀ hdeg hcm r hr c v hreg hcsd hsplit hsc L _ _ ι R m hR hRank hRs
    lam hchar
  obtain ⟨S, P, hclass, hP⟩ := hsc
  subst c
  obtain ⟨L₀, fieldL₀, numberFieldL₀, ι₀, C, m₀, hC, hCrank, hCs, hCabs⟩ :=
    hWitness K K₀ hdeg hcm r hr v hsplit S P hreg hcsd hP
  let : Field L₀ := fieldL₀
  let : NumberField L₀ := numberFieldL₀
  let p := CompletionPadic.residuePrime lam
  let i := coefficientCompletionEmbedding lam
  obtain ⟨e, hι⟩ := exists_padicAlgClComplexEquiv_extending p
    (i.comp (NumberField.FinitePlace.embedding lam)) ι
  obtain ⟨lam₀, j, hp₀, hj, hι₀⟩ := exists_compatibleCoefficientCompletionEmbedding p e ι₀
  have hchar₀ : residueCharacteristic v ≠ residueCharacteristic lam₀ := by
    rw [hp₀]
    change residueCharacteristic v ≠ CompletionPadic.residuePrime lam
    rwa [← residueCharacteristic_eq_residuePrime]
  let ℓ₀ : {l : FinitePlace L₀ // l ∉ (∅ : Finset (FinitePlace L₀))} := ⟨lam₀, by simp⟩
  let ℓ : {l : FinitePlace L // l ∉ (∅ : Finset (FinitePlace L))} := ⟨lam, by simp⟩
  let : Algebra (FiniteCompletion L₀ lam₀) (PadicAlgCl p) := j.toAlgebra
  have hCext := (hCabs lam₀ hchar₀).extendCoefficients (PadicAlgCl p)
  have hpos : 0 < (R ℓ).val.rank := by rw [hRank ℓ]; exact Nat.succ_pos r
  have hRabs : (atFinitePlace v (R ℓ)).val.IsAbsolutelyIrreducible :=
    pureLocalIrreducibilityTransfer hC hR
      (weakAssociationToSpectrum_of_class hCs P) (weakAssociationToSpectrum_of_class hRs P)
      v ℓ₀ ℓ hpos ((hCrank ℓ₀).trans (hRank ℓ).symm) e.toRingHom j i
      hj (continuous_coefficientCompletionEmbedding lam) hι₀ hι hCext
  let F := FiniteCompletion L lam
  let A := (atFinitePlace v (R ℓ)).val
  let Irr (a : Algebra F (AlgebraicClosure F)) : Prop :=
    letI := a
    Representation.IsIrreducible (A.extendCoefficients (AlgebraicClosure F)).representation
  change Irr ((algebraMap F (AlgebraicClosure F)).toAlgebra)
  exact Eq.mpr (congrArg Irr (toAlgebra_algebraMap (R := F) (S := AlgebraicClosure F))) hRabs

end Langlands.GaloisRepresentation
