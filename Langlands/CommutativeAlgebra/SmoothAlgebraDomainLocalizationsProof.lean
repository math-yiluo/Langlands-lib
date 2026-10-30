import Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizationsStatement
import Langlands.CommutativeAlgebra.IntegrallyClosedInReducedArtinianDomainLocalizationsProof
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-! # Domain prime localizations of smooth algebras over arbitrary fields -/

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizationsProof

universe u v w

lemma integrallyClosedIn_tensor_of_smooth
    (R : Type u) (S : Type v) (B : Type w)
    [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    [Algebra.Smooth R S] [IsIntegrallyClosedIn R B] :
    IsIntegrallyClosedIn S (S ⊗[R] B) := by
  obtain ⟨hinj, hcl⟩ := (isIntegrallyClosedIn_iff (R := R) (A := B)).mp inferInstance
  refine isIntegrallyClosedIn_iff.mpr
    ⟨Algebra.TensorProduct.includeLeft_injective (S := S) (A := S) hinj, ?_⟩
  intro x hx
  obtain ⟨t, ht⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := B)).surjective
      ⟨x, hx⟩
  have hm : ∀ t : S ⊗[R] integralClosure R B,
      ∃ s : S, algebraMap S (S ⊗[R] B) s =
        (TensorProduct.toIntegralClosure R S B t : S ⊗[R] B) := by
    intro t
    induction t with
    | tmul s b =>
      obtain ⟨r, hr⟩ := hcl b.property
      refine ⟨s * algebraMap R S r, ?_⟩
      change (s * algebraMap R S r) ⊗ₜ[R] (1 : B) = s ⊗ₜ[R] (b : B)
      rw [← hr]
      simpa only [Algebra.smul_def, mul_one, one_mul, mul_comm] using
        (TensorProduct.smul_tmul (R := R) r s (1 : B))
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨s₁, hs₁⟩ := h₁
      obtain ⟨s₂, hs₂⟩ := h₂
      exact ⟨s₁ + s₂, by simp only [map_add, Subalgebra.coe_add, hs₁, hs₂]⟩
  obtain ⟨s, hs⟩ := hm t
  exact ⟨s, hs.trans (congrArg Subtype.val ht)⟩

lemma domain_localizations_of_etale_of_integrallyClosed
    (H : ∀ (C : Type v) (D : Type (max u v))
      [CommRing C] [CommRing D] [Algebra C D],
      IsIntegrallyClosedIn C D → IsReduced D → IsArtinianRing D →
        ∀ (p : Ideal C) [p.IsPrime], IsDomain (Localization.AtPrime p))
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (p : Ideal S) [p.IsPrime] : IsDomain (Localization.AtPrime p) := by
  let F := FractionRing R
  have : IsReduced (F ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field F _
  have := Algebra.FormallyUnramified.finite_of_free F (F ⊗[R] S)
  have : IsArtinianRing (F ⊗[R] S) := .of_finite F _
  let e := Algebra.TensorProduct.comm R S F
  have : IsReduced (S ⊗[R] F) := isReduced_of_injective e e.injective
  have : IsArtinianRing (S ⊗[R] F) := e.symm.toRingEquiv.isArtinianRing
  exact H S (S ⊗[R] F) (integrallyClosedIn_tensor_of_smooth R S F)
    inferInstance inferInstance p

lemma smoothAlgebraDomainLocalizations_of_artinian_lemma
    (H : ∀ (C : Type v) (D : Type (max u v))
      [CommRing C] [CommRing D] [Algebra C D],
      IsIntegrallyClosedIn C D → IsReduced D → IsArtinianRing D →
        ∀ (p : Ideal C) [p.IsPrime], IsDomain (Localization.AtPrime p)) :
    SmoothAlgebraDomainLocalizations.{u, v} := by
  intro K _ A _ _ hSmooth p hp
  let := hSmooth
  obtain ⟨f, hf, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let := hAlg
  let := hTower
  let := hEtale
  have hd : Disjoint (Submonoid.powers f : Set A) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let q : Ideal (Localization.Away f) := p.map (algebraMap A (Localization.Away f))
  have : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f) p hp hd
  have hc : q.comap (algebraMap A (Localization.Away f)) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) (Localization.Away f) hp hd
  have : IsDomain (Localization.AtPrime q) :=
    domain_localizations_of_etale_of_integrallyClosed H (MvPolynomial (Fin n) K)
      (Localization.Away f) q
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f) q
  have hdomain : IsDomain (Localization.AtPrime
      (q.comap (algebraMap A (Localization.Away f)))) :=
    (e.toRingEquiv.toMulEquiv.isDomain_iff).mpr inferInstance
  have transport (r : Ideal A) [r.IsPrime] (hr : r = p)
      (h : IsDomain (Localization.AtPrime r)) : IsDomain (Localization.AtPrime p) := by
    subst r
    exact h
  exact transport _ hc hdomain

end Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizationsProof

namespace Langlands.CommutativeAlgebra

/-- Every prime localization of a smooth algebra over any field is a domain. -/
theorem smoothAlgebraDomainLocalizations.{u, v} :
    SmoothAlgebraDomainLocalizations.{u, v} :=
  SmoothAlgebraDomainLocalizationsProof.smoothAlgebraDomainLocalizations_of_artinian_lemma
    integrallyClosedInReducedArtinianDomainLocalizations.{v, max u v}

end Langlands.CommutativeAlgebra
