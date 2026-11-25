import Langlands.Automorphic.IsobaricLocalSupport
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Correspondence.HenniartCyclicBaseChange
import Langlands.Global.CompletionPadicTower
import Langlands.Global.Arithmetic.HarrisSetup

/-! # Restricted cyclic base-change compatibility

For each local prime-degree cyclic step, a single weak local base-change map
works in every rank and every compatible globalization in the restricted
Arthur--Clozel III.5.1 setting. The conclusion is the total actual local
supercuspidal support of a unitary isobaric weak base change.
-/

noncomputable section

universe uK uV uF uP uQ

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Henniart

/-- Restricted Arthur--Clozel III.5.1, expressed using one chosen weak local
cyclic base-change map per local step, uniformly over ranks and compatible
globalizations. This is an internal E2/E3 interface, stated without proof. -/
def RestrictedCyclicBaseChangeCompatibilityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : Numerical.CyclicPrimeStep.{uK} p),
    ∃ Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S,
      Numerical.IsWeakCyclicBaseChange S Ch ∧
      ∀ (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
        [NumberField.IsCMField F] [Algebra F E] [IsGalois F E]
        [IsCyclic (E ≃ₐ[F] E)] [CompactSpace (AdeleQuotient F)]
        [CompactSpace (AdeleQuotient E)],
        Module.finrank F E = S.degree →
        ∀ v : FinitePlace F,
          let vc := Harris.conjPlace F v
          v ≠ vc →
          ∀ (w : FinitePlacesAbove E v) (wc : FinitePlacesAbove E vc),
            (∀ w' : FinitePlacesAbove E v, w' = w) →
            (∀ wc' : FinitePlacesAbove E vc, wc' = wc) →
            ∀ (hpF : CompletionPadic.residuePrime v = p)
              (hpE : CompletionPadic.residuePrime w.1 = p)
              (αF : letI := (CompletionPadic.padicFieldAt v hpF).algebra
                S.base.Carrier ≃ₐ[Padic p]
                (CompletionPadic.padicFieldAt v hpF).Carrier)
              (αE : letI := (CompletionPadic.padicFieldAt w.1 hpE).algebra
                S.top.Carrier ≃ₐ[Padic p]
                (CompletionPadic.padicFieldAt w.1 hpE).Carrier),
              (∀ x : S.base.Carrier, αE (S.embedding x) =
                FiniteExtension.completionMap v w.1 (αF x)) →
              ∀ (r : ℕ) (T : CuspidalOperatorRealization F r),
                ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
                T.isoClass.IsRegularAlgebraic →
                T.isoClass.HasSupercuspidalComponent.{uF, uP} v →
                T.isoClass.HasSupercuspidalComponent.{uF, uP} vc →
                ∀ D : IsobaricData E, D.IsUnitary →
                  D.IsWeakBaseChangeOf.{uF, uF, uP, uQ}
                    (IsobaricData.ofCuspidal
                      (PositiveRankCuspidalClass.ofFixedRank T.isoClass)) →
                  ∀ π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV}
                    S.base r.succPNat,
                    T.isoClass.HasPadicSupercuspidalClass.{uF, uP, uK, uV}
                      v hpF S.base αF π →
                    D.HasLocalSupercuspidalSupport.{uF, uQ, uK, uV}
                      w.1 hpE S.top αE (Ch r π)

end Langlands.Automorphic.Unramified
