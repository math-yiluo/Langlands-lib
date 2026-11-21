import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeSupercuspidalStatement
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-! # Supercuspidality descends from a cuspidal weak base change supercuspidal at two places

Interface B5r of operator ruling `c05e16c6` (on request `d972fdbc`): the hypotheses of
B5 (`CyclicWeakBaseChangeSupercuspidalStatement`) and a second finite place `v' ≠ v`,
with a unique place `w'` above it at which the same presentation of the cuspidal weak
base change is supercuspidal; the conclusion of B5 at `v`. The general form assumes
that `E/F` is unramified at the infinite places; the totally complex form does not.
Proposition definitions only.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.CuspidalOperatorRealization

/-- B5 with a second finite place `v' ≠ v` of `F`, with exactly one place `w'` of `E`
above it, at which the same presentation of the weak base change is supercuspidal. -/
def RestrictedCyclicWeakBaseChangeSupercuspidalStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsUnramifiedAtInfinitePlaces F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w'' : FinitePlacesAbove E v, w'' = w) →
    ∀ (v' : FinitePlace F) (w' : FinitePlacesAbove E v'),
      v' ≠ v → (∀ w'' : FinitePlacesAbove E v', w'' = w') →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r)
      (T : CuspidalOperatorRealization E r)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      (P.localComponent w.1).IsSupercuspidal →
      (P.localComponent w'.1).IsSupercuspidal →
      IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass →
      IsoClass.HasSupercuspidalComponent.{uF, uV} S.isoClass v

/-- The totally complex form: `[NumberField.IsTotallyComplex F]` after `[NumberField F]`,
and no hypothesis at the infinite places. -/
def RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w'' : FinitePlacesAbove E v, w'' = w) →
    ∀ (v' : FinitePlace F) (w' : FinitePlacesAbove E v'),
      v' ≠ v → (∀ w'' : FinitePlacesAbove E v', w'' = w') →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r)
      (T : CuspidalOperatorRealization E r)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      (P.localComponent w.1).IsSupercuspidal →
      (P.localComponent w'.1).IsSupercuspidal →
      IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass →
      IsoClass.HasSupercuspidalComponent.{uF, uV} S.isoClass v

end Langlands.Automorphic.Unramified
