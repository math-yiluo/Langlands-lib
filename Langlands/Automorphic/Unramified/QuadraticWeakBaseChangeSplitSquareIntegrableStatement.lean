import Langlands.Automorphic.SquareIntegrableComponent
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Galois.QuadraticPatchingStatement

/-! # The split square-integrable case of strong quadratic base change -/

noncomputable section

universe uF uE uV uW

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- A unitary isobaric weak quadratic lift of a cuspidal class with a
square-integrable component at a completely split place is cuspidal.
Its components at the places above the given place are square-integrable and
identify with the original component along the completion maps. -/
def QuadraticWeakBaseChangeSplitSquareIntegrableStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    Module.finrank F E = 2 →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r)
      (P : CuspidalSpectralPresentation.{uF, uV} S) (D : IsobaricData E) (v : FinitePlace F),
      (P.localComponent v).IsSquareIntegrable → SplitsCompletelyAt (N := E) v →
      let B := IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)
      B.IsUnitary → D.IsUnitary → D.IsWeakBaseChangeOf.{uF, uE, uV, uW} B →
      ∃ (T : CuspidalOperatorRealization E r) (Q : CuspidalSpectralPresentation.{uE, uW} T),
        D = IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass) ∧
        ∀ w : FinitePlacesAbove E v,
          letI : w.val.asIdeal.LiesOver v.asIdeal := w.property
          (Q.localComponent w.val).IsSquareIntegrable ∧
          Nonempty ((P.localComponent v).representation.Equiv
            ((Q.localComponent w.val).representation.comp
              (Matrix.GeneralLinearGroup.map (completionMap v w.val))))

end Langlands.Automorphic.Unramified
