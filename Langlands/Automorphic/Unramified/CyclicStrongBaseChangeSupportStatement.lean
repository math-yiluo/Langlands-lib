import Langlands.Automorphic.IsobaricLocalSupport
import Langlands.Automorphic.IsobaricComplexPlaceParameter
import Langlands.Automorphic.IsobaricRealPlaceParameter
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport
import Langlands.BaseChange.SigmaLiftOnSupercuspidals
import Langlands.Correspondence.HenniartCyclicBaseChange
import Langlands.LocalFactor.ArchimedeanRestriction
import Mathlib.FieldTheory.Galois.Basic

/-! # Strong cyclic base change on isobaric support and parameters

A named external input derived from the strong-lifting assertion of Arthur–Clozel
III.5.1. It expresses finite-place compatibility on actual supercuspidal
supports and infinite-place compatibility on the Library's parameter lists.
-/

noncomputable section

universe uK uV uF uE uP uQ

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Henniart.Numerical
open Langlands.LocalFactor.Archimedean

/-- A weak lift of unitary isobaric data along a cyclic number-field extension
of prime degree has the specified local support and parameter compatibilities
at nonsplit finite, split finite, complex and real places. At a nonsplit
finite place the input local map is certified by σ-lift character identities. -/
def CyclicStrongBaseChangeSupportStatement : Prop :=
  -- N′: apply a certified local map at the unique place above a nonsplit place.
  (∀ (p : ℕ) [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)
    (Ch : CyclicBaseChangeMap.{uK, uV} S),
    (∀ σ : S.Gal, σ ≠ 1 → BaseChange.IsSigmaLiftOnSupercuspidals.{uK, uV}
      S.embedding Ch σ) →
    ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
      [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
      [IsCyclic (E ≃ₐ[F] E)]
      [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
      Module.finrank F E = S.degree →
      ∀ (DF : IsobaricData F) (DE : IsobaricData E),
        DF.IsUnitary → DE.IsUnitary →
        IsobaricData.IsWeakBaseChangeOf.{uF, uE, uP, uQ} DE DF →
        ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v),
          (∀ w' : FinitePlacesAbove E v, w' = w) →
          ∀ (hpF : CompletionPadic.residuePrime v = p)
            (hpE : CompletionPadic.residuePrime w.1 = p)
            (αF : letI := (CompletionPadic.padicFieldAt v hpF).algebra
              S.base.Carrier ≃ₐ[Padic p] (CompletionPadic.padicFieldAt v hpF).Carrier)
            (αE : letI := (CompletionPadic.padicFieldAt w.1 hpE).algebra
              S.top.Carrier ≃ₐ[Padic p] (CompletionPadic.padicFieldAt w.1 hpE).Carrier),
            (∀ x : S.base.Carrier,
              αE (S.embedding x) = FiniteExtension.completionMap v w.1 (αF x)) →
            ∀ sF : Multiset (Σ k : ℕ,
              Correspondence.SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat),
              IsobaricData.HasLocalSupercuspidalSupport.{uF, uP, uK, uV}
                DF v hpF S.base αF sF →
              IsobaricData.HasLocalSupercuspidalSupport.{uE, uQ, uK, uV}
                DE w.1 hpE S.top αE (sF.bind (fun x => Ch x.1 x.2))) ∧
  -- S: transport support through a split completion square.
  (∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (DF : IsobaricData F) (DE : IsobaricData E),
      DF.IsUnitary → DE.IsUnitary →
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uP, uQ} DE DF →
      ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v)
        (p : ℕ) [Fact p.Prime]
        (hpF : CompletionPadic.residuePrime v = p)
        (hpE : CompletionPadic.residuePrime w.1 = p)
        (K : PadicField.{uK} p)
        (αF : letI := (CompletionPadic.padicFieldAt v hpF).algebra
          K.Carrier ≃ₐ[Padic p] (CompletionPadic.padicFieldAt v hpF).Carrier)
        (αE : letI := (CompletionPadic.padicFieldAt w.1 hpE).algebra
          K.Carrier ≃ₐ[Padic p] (CompletionPadic.padicFieldAt w.1 hpE).Carrier),
        (∀ x : K.Carrier, αE x = FiniteExtension.completionMap v w.1 (αF x)) →
        ∀ s : Multiset (Σ k : ℕ,
          Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat),
          IsobaricData.HasLocalSupercuspidalSupport.{uF, uP, uK, uV} DF v hpF K αF s →
          IsobaricData.HasLocalSupercuspidalSupport.{uE, uQ, uK, uV} DE w.1 hpE K αE s) ∧
  -- C: transport the aggregate parameter above a complex place.
  (∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (DF : IsobaricData F) (DE : IsobaricData E),
      DF.IsUnitary → DE.IsUnitary →
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uP, uQ} DE DF →
      ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
        (w : InfinitePlacesAbove E v.1) (ds : List ComplexCharacterData),
        DF.HasComplexPlaceParameter v ds ↔
          DE.HasComplexPlaceParameter (complexPlaceAbove v w)
            (complexPlaceParameterTransport v w ds)) ∧
  -- R: compare at real places and restrict to the Weil group at complex places above them.
  (∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (DF : IsobaricData F) (DE : IsobaricData E),
      DF.IsUnitary → DE.IsUnitary →
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uP, uQ} DE DF →
      ∀ (v : {v : NumberField.InfinitePlace F // v.IsReal})
        (w : InfinitePlacesAbove E v.1) (ds : List RealBlock),
        (∀ hw : w.1.IsReal,
          (∀ d : ComplexCharacterData, RealBlock.induced d ∈ ds → d.weight ≠ 0) →
          (DF.HasRealPlaceParameter v ds ↔ DE.HasRealPlaceParameter ⟨w.1, hw⟩ ds)) ∧
        (∀ hw : w.1.IsComplex,
          DF.HasRealPlaceParameter v ds →
            DE.HasComplexPlaceParameter ⟨w.1, hw⟩ (realParameterRestrictToComplex ds)))

end Langlands.Automorphic.Unramified
