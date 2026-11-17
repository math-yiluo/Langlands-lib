import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Automorphic.SupercuspidalComponent

/-! # Supercuspidality descends from a cuspidal weak base change at a unique place

Interface B5 of the operator's plan of 16 November 2026 (Section 2.2), with its totally
complex form. It is a derived global consequence of Arthur--Clozel (1989), Chapter III,
Theorem 5.1, and of the local base-change theory of Chapter I, Section 6. Its proof must
also identify a supplied weak base change with the global cyclic base change. Proposition
definitions only.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.CuspidalOperatorRealization

/-- For a Galois extension `E/F` of prime degree and a finite place `v` of `F` with exactly
one place `w` of `E` above it: if a cuspidal class over `F` with unitary central character
has a cuspidal weak base change to `E` with a supercuspidal component at `w`, then it has a
supercuspidal component at `v`. This is a derived global input, not the local base-change
theorem. -/
def CyclicWeakBaseChangeSupercuspidalStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w' : FinitePlacesAbove E v, w' = w) →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r)
      (T : CuspidalOperatorRealization E r)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      (P.localComponent w.1).IsSupercuspidal →
      IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass →
      IsoClass.HasSupercuspidalComponent.{uF, uV} S.isoClass v

/-- The totally complex form of `CyclicWeakBaseChangeSupercuspidalStatement`: the same
statement with `[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, at the
same universe levels, the rest verbatim. -/
def CyclicWeakBaseChangeSupercuspidalTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w' : FinitePlacesAbove E v, w' = w) →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r)
      (T : CuspidalOperatorRealization E r)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      (P.localComponent w.1).IsSupercuspidal →
      IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass →
      IsoClass.HasSupercuspidalComponent.{uF, uV} S.isoClass v

end Langlands.Automorphic.Unramified
