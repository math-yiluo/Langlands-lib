import Langlands.Automorphic.Unramified.IsobaricWeakTransfer

/-! # Spectral attachments of an isobaric enumeration and its arithmetic conjugate -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified

/-- The actual class multiset of an enumeration admits the finite-sum spectrum
of the supplied constituent presentations, with its rank cast to the rank of
the multiset. -/
def IsobaricEnumerationSpectralAttachmentStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (k : ℕ) (c : Fin k → PositiveRankCuspidalClass F)
    (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank),
    (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
    let A : IsobaricData F := (Finset.univ : Finset (Fin k)).val.map c
    ∃ t : SpectralSystem (FinitePlace F) A.rank,
      A.HasSpectralSystem.{uF, uV} t ∧ (SpectralSystem.finiteSum s).SameEulerPolynomials t

/-- Conjugate the actual attached cuspidal presentations. At each good place
of the conjugate, the Euler polynomial is the original one at the place
pulled back along `σ`. -/
def IsobaricSpectralConjugationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (σ : F ≃+* F) (A : IsobaricData F) (s : SpectralSystem (FinitePlace F) A.rank),
    A.HasSpectralSystem.{uF, uV} s →
    let B : IsobaricData F := A.map (PositiveRankCuspidalClass.arithmeticComap σ.symm)
    ∃ t : SpectralSystem (FinitePlace F) B.rank,
      B.HasSpectralSystem.{uF, uV} t ∧
      ∀ᶠ v in Filter.cofinite,
        ∀ (hs : finitePlaceEquiv σ v ∉ s.exceptional) (ht : v ∉ t.exceptional),
          t.eulerPolynomial v ht = s.eulerPolynomial (finitePlaceEquiv σ v) hs

end Langlands.Automorphic.Unramified
