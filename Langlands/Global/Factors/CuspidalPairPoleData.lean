import Langlands.Global.Factors.CuspidalArchimedeanParameterExistenceProof
import Langlands.Global.Factors.CuspidalPairPoleFiniteEuler

/-! # Finite and archimedean data for cuspidal pair poles -/

universe u uQ

set_option autoImplicit false

namespace Langlands.Global

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open CuspidalPairPoles (FinitePairLChoice nonempty_finitePairLChoice)

/-- The data-existence conjunct of `CuspidalPairPoleStatement` for fields and ranks as
in that statement. Data existence holds before imposing split-centre triviality. -/
def CuspidalPairPoleDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P'),
    Nonempty (FinitePairLChoice P P' h h') ∧
      (∀ v : {v : InfinitePlace F // v.IsReal},
        (∃ ds, OperatorRealization.HasRealPlaceParameter T.realization v ds) ∧
          ∃ ds, OperatorRealization.HasRealPlaceParameter T'.realization v ds) ∧
      ∀ v : {v : InfinitePlace F // v.IsComplex},
        (∃ ds, OperatorRealization.HasComplexPlaceParameter T.realization v ds) ∧
          ∃ ds, OperatorRealization.HasComplexPlaceParameter T'.realization v ds

/-- The presentations have certified finite pair L-data and both realizations have
archimedean standard-module parameters at every infinite place. -/
theorem cuspidalPairPoleData : CuspidalPairPoleDataStatement.{u, uQ} := by
  intro F _ _ _ r t T T' P P' h h'
  have hT := cuspidalArchimedeanParameterExistence F r T
  have hT' := cuspidalArchimedeanParameterExistence F t T'
  exact ⟨nonempty_finitePairLChoice,
    fun v => ⟨hT.1 v, hT'.1 v⟩, fun v => ⟨hT.2 v, hT'.2 v⟩⟩

end Langlands.Global
