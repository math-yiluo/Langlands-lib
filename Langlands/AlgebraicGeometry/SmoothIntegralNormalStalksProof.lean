import Langlands.AlgebraicGeometry.SmoothIntegralNormalStalksStatement
import Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizationsProof

/-! # Normal stalks of integral smooth schemes over arbitrary fields -/

noncomputable section

open scoped TensorProduct

universe u v w

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.CommutativeAlgebra.SmoothIntegralNormalStalks

open IntegrallyClosedInReducedArtinian

/-- If a domain is integrally closed in a reduced Artinian algebra, that
ambient algebra is a domain too: its separating idempotents descend. -/
lemma isDomain_of_integrallyClosedIn
    (R : Type u) (B : Type v) [CommRing R] [IsDomain R]
    [CommRing B] [Algebra R B] [IsReduced B] [IsArtinianRing B]
    [IsIntegrallyClosedIn R B] : IsDomain B := by
  have hinj : Function.Injective (algebraMap R B) :=
    IsIntegralClosure.algebraMap_injective R R B
  have : Nontrivial B := Function.Injective.nontrivial hinj
  have hidem : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (R := R) (A := B)
      (isIntegral_of_isIdempotentElem he)
    have hridem : r * r = r := by
      apply hinj
      rw [map_mul, hr]
      exact he
    have hzero : r * (r - 1) = 0 := by rw [mul_sub, hridem, mul_one, sub_self]
    rcases mul_eq_zero.mp hzero with h | h
    · left
      rw [← hr, h, map_zero]
    · right
      rw [sub_eq_zero.mp h] at hr
      simpa using hr.symm
  have : NoZeroDivisors B := by
    constructor
    intro a b hab
    obtain ⟨e, he, heb, hea⟩ := exists_separating_idempotent hab
    rcases hidem e he with h | h
    · left
      simpa [h] using hea
    · right
      simpa [h] using heb
  exact NoZeroDivisors.to_isDomain B

/-- An etale domain over an integrally closed domain is integrally closed. -/
lemma integrallyClosed_of_etale
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S] :
    IsIntegrallyClosed S := by
  let F := FractionRing R
  have : IsReduced (F ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field F _
  have := Algebra.FormallyUnramified.finite_of_free F (F ⊗[R] S)
  have : IsArtinianRing (F ⊗[R] S) := .of_finite F _
  let e := Algebra.TensorProduct.comm R S F
  have : IsReduced (S ⊗[R] F) := isReduced_of_injective e e.injective
  have : IsArtinianRing (S ⊗[R] F) := e.symm.toRingEquiv.isArtinianRing
  have : IsIntegrallyClosedIn S (S ⊗[R] F) :=
    SmoothAlgebraDomainLocalizationsProof.integrallyClosedIn_tensor_of_smooth R S F
  have : IsDomain (S ⊗[R] F) := isDomain_of_integrallyClosedIn S _
  let : Field (S ⊗[R] F) := (IsArtinianRing.isField_of_isDomain _).toField
  have : FaithfulSMul S (S ⊗[R] F) := IsIntegralClosure.faithfulSMul S S _
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn S (S ⊗[R] F)

/-- Every prime localization of a smooth domain over any field is normal. -/
lemma integrallyClosed_localization_of_smooth_domain
    (K : Type u) [Field K] (A : Type v) [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  obtain ⟨f, hf, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let := hAlg
  let := hTower
  let := hEtale
  have hd : Disjoint (Submonoid.powers f : Set A) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let q : Ideal (Localization.Away f) := p.map (algebraMap A (Localization.Away f))
  have : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f) p
      inferInstance hd
  have hc : q.comap (algebraMap A (Localization.Away f)) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) (Localization.Away f)
      inferInstance hd
  have hf0 : f ≠ 0 := by
    intro h
    apply hf
    rw [h]
    exact p.zero_mem
  have : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f)
      (Localization.Away f)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf0))
  have : IsIntegrallyClosed (Localization.Away f) :=
    integrallyClosed_of_etale (MvPolynomial (Fin n) K) (Localization.Away f)
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q) q.primeCompl
      q.primeCompl_le_nonZeroDivisors
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f) q
  have hnormal : IsIntegrallyClosed (Localization.AtPrime
      (q.comap (algebraMap A (Localization.Away f)))) :=
    IsIntegrallyClosed.of_equiv e.symm.toRingEquiv
  have transport (r : Ideal A) [r.IsPrime] (hr : r = p)
      (h : IsIntegrallyClosed (Localization.AtPrime r)) :
      IsIntegrallyClosed (Localization.AtPrime p) := by
    subst r
    exact h
  exact transport _ hc hnormal

end Langlands.CommutativeAlgebra.SmoothIntegralNormalStalks

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The actual stalks of an integral scheme smooth over any field are normal. -/
theorem smoothIntegralNormalStalks : SmoothIntegralNormalStalksStatement.{u} := by
  intro K _ X _ p hp x
  let := hp
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let U := X.affineCover.X i
  let q := X.affineCover.f i ≫ p
  have : Smooth q := inferInstance
  have : Nonempty U := ⟨y⟩
  have : IsIntegral U := isIntegral_of_isOpenImmersion (X.affineCover.f i)
  have : IsDomain Γ(U, ⊤) := inferInstance
  let g : CommRingCat.of K ⟶ Γ(U, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop
  have hg : g.hom.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appTop @Smooth q inferInstance)
  algebraize [g.hom]
  have : Algebra.Smooth K Γ(U, ⊤) := RingHom.smooth_algebraMap.mp hg
  let P := ((isAffineOpen_top U).primeIdealOf ⟨y, trivial⟩).asIdeal
  have : IsIntegrallyClosed (Localization.AtPrime P) :=
    Langlands.CommutativeAlgebra.SmoothIntegralNormalStalks.integrallyClosed_localization_of_smooth_domain
      K Γ(U, ⊤) P
  let := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, trivial⟩ : (⊤ : U.Opens))
  have := (isAffineOpen_top U).isLocalization_stalk ⟨y, trivial⟩
  have : IsIntegrallyClosed (U.presheaf.stalk y) :=
    IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv P.primeCompl
      (U.presheaf.stalk y) (Localization.AtPrime P)).symm.toRingEquiv
  exact IsIntegrallyClosed.of_equiv
    (asIso ((X.affineCover.f i).stalkMap y)).commRingCatIsoToRingEquiv.symm

end Langlands.AlgebraicGeometry
