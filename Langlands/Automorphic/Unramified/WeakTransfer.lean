import Langlands.Representation.Unramified.WeakTransfer
import Langlands.Automorphic.CuspidalSpectralPresentation

/-! # Arithmetic weak transfer attached to actual full cuspidal classes -/

noncomputable section

universe uF uE uV uW

namespace Langlands.Automorphic.CuspidalOperatorRealization.IsoClass

open Langlands.Global Langlands.Unramified

variable {F : Type uF} {E : Type uE} [Field F] [Field E]
  [NumberField F] [NumberField E] [Algebra F E]
  [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
  {r q : ℕ}

/-- Equal-positive-rank weak base change, witnessed by genuine spectral
presentations of the actual full cuspidal classes. -/
def IsWeakBaseChangeOf (d : IsoClass E r) (c : IsoClass F r) : Prop :=
  ∃ (s : SpectralSystem (FinitePlace F) (r + 1))
    (t : SpectralSystem (FinitePlace E) (r + 1)),
    HasSpectralSystem.{uF, uV} c s ∧ HasSpectralSystem.{uE, uW} d t ∧
      t.IsArithmeticWeakBaseChangeOf s

/-- Weak induction between independently supplied positive ranks, with genuine
attachments and the numerical relation's explicit field-degree rank equation. -/
def IsWeakInductionOf (c : IsoClass F r) (d : IsoClass E q) : Prop :=
  ∃ (s : SpectralSystem (FinitePlace F) (r + 1))
    (t : SpectralSystem (FinitePlace E) (q + 1)),
    HasSpectralSystem.{uF, uV} c s ∧ HasSpectralSystem.{uE, uW} d t ∧
      s.IsArithmeticWeakInductionOf t

/-- The existential relation retains the required degree multiplication. -/
theorem IsWeakInductionOf.rank_eq {c : IsoClass F r} {d : IsoClass E q}
    (h : IsWeakInductionOf.{uF, uE, uV, uW} c d) :
    r + 1 = (q + 1) * Module.finrank F E := by
  rcases h with ⟨s, t, _, _, h⟩
  exact h.1

/-- The same class relation can be witnessed at any two actual representatives.
The attachment equivalence uses genuine presentation transport. -/
theorem isWeakBaseChangeOf_isoClass_iff
    (T : CuspidalOperatorRealization E r) (S : CuspidalOperatorRealization F r) :
    IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass ↔
      ∃ (P : CuspidalSpectralPresentation.{uF, uV} S)
        (Q : CuspidalSpectralPresentation.{uE, uW} T),
        Q.spectralSystem.IsArithmeticWeakBaseChangeOf P.spectralSystem := by
  constructor
  · rintro ⟨s, t, hs, ht, h⟩
    obtain ⟨P, rfl⟩ := (hasSpectralSystem_iff S s).mp hs
    obtain ⟨Q, rfl⟩ := (hasSpectralSystem_iff T t).mp ht
    exact ⟨P, Q, h⟩
  · rintro ⟨P, Q, h⟩
    exact ⟨P.spectralSystem, Q.spectralSystem,
      (hasSpectralSystem_iff S _).mpr ⟨P, rfl⟩,
      (hasSpectralSystem_iff T _).mpr ⟨Q, rfl⟩, h⟩

/-- The induction relation likewise has genuine witnesses at any actual
representatives, without a uniqueness assertion for their presentations. -/
theorem isWeakInductionOf_isoClass_iff
    (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E q) :
    IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass T.isoClass ↔
      ∃ (P : CuspidalSpectralPresentation.{uF, uV} S)
        (Q : CuspidalSpectralPresentation.{uE, uW} T),
        P.spectralSystem.IsArithmeticWeakInductionOf Q.spectralSystem := by
  constructor
  · rintro ⟨s, t, hs, ht, h⟩
    obtain ⟨P, rfl⟩ := (hasSpectralSystem_iff S s).mp hs
    obtain ⟨Q, rfl⟩ := (hasSpectralSystem_iff T t).mp ht
    exact ⟨P, Q, h⟩
  · rintro ⟨P, Q, h⟩
    exact ⟨P.spectralSystem, Q.spectralSystem,
      (hasSpectralSystem_iff S _).mpr ⟨P, rfl⟩,
      (hasSpectralSystem_iff T _).mpr ⟨Q, rfl⟩, h⟩

/-- Full equivalences transport both witnessing presentations, retaining their
spectral systems and hence their weak-base-change comparison. -/
theorem isWeakBaseChangeOf_transport
    {S S' : CuspidalOperatorRealization F r}
    {T T' : CuspidalOperatorRealization E r}
    (e : S.Equivalence S') (f : T.Equivalence T') :
    IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass ↔
      IsWeakBaseChangeOf.{uF, uE, uV, uW} T'.isoClass S'.isoClass := by
  rw [isWeakBaseChangeOf_isoClass_iff, isWeakBaseChangeOf_isoClass_iff]
  constructor
  · rintro ⟨P, Q, h⟩
    exact ⟨P.transport e, Q.transport f, h⟩
  · rintro ⟨P, Q, h⟩
    exact ⟨P.transport e.symm, Q.transport f.symm, h⟩

/-- Full equivalences preserve the induction relation via the same genuine
presentation transport, with both independently supplied ranks retained. -/
theorem isWeakInductionOf_transport
    {S S' : CuspidalOperatorRealization F r}
    {T T' : CuspidalOperatorRealization E q}
    (e : S.Equivalence S') (f : T.Equivalence T') :
    IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass T.isoClass ↔
      IsWeakInductionOf.{uF, uE, uV, uW} S'.isoClass T'.isoClass := by
  rw [isWeakInductionOf_isoClass_iff, isWeakInductionOf_isoClass_iff]
  constructor
  · rintro ⟨P, Q, h⟩
    exact ⟨P.transport e, Q.transport f, h⟩
  · rintro ⟨P, Q, h⟩
    exact ⟨P.transport e.symm, Q.transport f.symm, h⟩

end Langlands.Automorphic.CuspidalOperatorRealization.IsoClass
