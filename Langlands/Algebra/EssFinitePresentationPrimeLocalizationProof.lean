import Langlands.Algebra.EssFinitePresentationPrimeLocalizationStatement
import Langlands.Algebra.PrimeLocalizationCriterion

/-! # Prime-localization presentation of an essentially finitely presented local algebra: proof -/

universe u v w

namespace Langlands.Algebra

/-- Let `A` be an `R`-algebra, `M` an arbitrary submonoid of `A`, and
`e : Localization M ≃ₐ[R] S` with `S` local. Then `S` is, as an `R`-algebra, the localization
of `A` at a prime ideal: the inverse image of the maximal ideal of `Localization M`. -/
theorem exists_algEquiv_localization_atPrime_of_local
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S] [CommRing A] [Algebra R A]
    (M : Submonoid A) (e : Localization M ≃ₐ[R] S) :
    ∃ (q : Ideal A) (hq : q.IsPrime), Nonempty (@Localization.AtPrime _ _ q hq ≃ₐ[R] S) := by
  have : Nontrivial (Localization M) := e.toEquiv.nontrivial
  have : IsLocalRing (Localization M) :=
    IsLocalRing.of_surjective' e.symm.toRingEquiv.toRingHom e.symm.surjective
  let q : Ideal A := (IsLocalRing.maximalIdeal (Localization M)).comap
    (algebraMap A (Localization M))
  have : IsLocalization.AtPrime (Localization M) q :=
    isLocalization_atPrime_of_local_target M
  exact ⟨q, inferInstance,
    ⟨((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (Localization M)).restrictScalars R).trans e⟩⟩

/-- The exact published prime-localization proposition (first step of Stacks 00QV). -/
theorem essFinitePresentationPrimeLocalization :
    EssFinitePresentationPrimeLocalizationStatement.{u, v} := by
  intro R S _ _ _ _ hS
  obtain ⟨n, I, hI, M, ⟨e⟩⟩ := hS
  obtain ⟨q, hq, ⟨f⟩⟩ := exists_algEquiv_localization_atPrime_of_local M e
  exact ⟨n, I, hI, q, hq, ⟨f⟩⟩

example : EssFinitePresentationPrimeLocalizationStatement.{u, v} :=
  @essFinitePresentationPrimeLocalization.{u, v}

end Langlands.Algebra
