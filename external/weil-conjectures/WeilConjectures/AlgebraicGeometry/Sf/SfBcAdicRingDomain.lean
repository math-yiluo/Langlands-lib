/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement

/-! # The base-change package's adic coefficient domain

The ring assertion is independent of the site universe. The scheme assertion uses
exactly the completed coefficient ring and three-clause integral domain.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The package valuation ring and every positive quotient satisfy the adic hypotheses,
with the specified two-term finite free resolution and its quotient augmentation. -/
theorem sf_bc_adic_ring_domain (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsNonarchimedean (Padic.coefficientExtensionAbsoluteValue l E) ∧
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
    IsDomain (Padic.coefficientExtensionIntegers l E) ∧
    IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) ∧
    (Ideal.span {Padic.coefficientExtensionUniformizer l E}).IsMaximal ∧
    Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E ∧
    Finite (Padic.coefficientExtensionResidueField l E) ∧
    CharP (Padic.coefficientExtensionResidueField l E) l ∧
    (∃ d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E),
      d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E}) ∧
    ∀ n : ℕ, 1 ≤ n →
      Finite (Padic.coefficientExtensionRing l E n) ∧
      (∀ x : Padic.coefficientExtensionRing l E n, l ^ n • x = 0) ∧
      Function.Surjective (Padic.coefficientExtensionTransition l E n) ∧
      adicQuotientPerfect (Padic.coefficientExtensionIntegers l E)
        (Ideal.span {Padic.coefficientExtensionUniformizer l E}) n ∧
      ∃ (P : CochainComplex (ModuleCat (Padic.coefficientExtensionIntegers l E)) ℤ),
        P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0 ∧
        (∀ i : ℤ, Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
          Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i)) ∧
        ∃ (em : P.X (-1) ≅ ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIntegers l E))
          (e0 : P.X 0 ≅ ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIntegers l E)),
          P.d (-1) 0 = em.hom ≫ ModuleCat.ofHom
            (LinearMap.mulLeft (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionUniformizer l E ^ n)) ≫ e0.inv ∧
          ∃ (φ : DerivedCategory.Q.obj P ≅
              (DerivedCategory.singleFunctor
                (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
                (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
                  (Padic.coefficientExtensionRing l E n)))
            (ε : P ⟶ (CochainComplex.singleFunctor
              (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
              (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
                (Padic.coefficientExtensionRing l E n))),
            DerivedCategory.Q.map ε = φ.hom ∧
            ε.f 0 = e0.hom ≫ ModuleCat.ofHom
              (AlgHom.toLinearMap (Ideal.Quotient.mkₐ
                (Padic.coefficientExtensionIntegers l E)
                (Padic.coefficientExtensionIdeal l E n))) ∧
            ∀ i : ℤ, i ≠ 0 → ε.f i = 0 := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hdvr : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.1
  have hpid : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.2.1
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hlmem : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    apply (h.2.1 _).2
    change spectralNorm ℚ_[l] E (l : E) < 1
    simpa only [map_natCast] using
      (spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])).trans_lt
        (Padic.norm_p_lt_one (p := l))
  have hlzero : (l : Padic.coefficientExtensionResidueField l E) = 0 := by
    exact (map_natCast (Ideal.Quotient.mk _) l).symm.trans
      ((Ideal.Quotient.eq_zero_iff_mem).2 hlmem)
  have hchar : CharP (Padic.coefficientExtensionResidueField l E) l :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hlzero
  have hfinite (n : ℕ) (hn : 1 ≤ n) := Padic.finite_coefficientExtensionRing l E n hn
  have hperfect (n : ℕ) (hn : 1 ≤ n) :
      adicQuotientPerfect (Padic.coefficientExtensionIntegers l E)
        (Ideal.span {Padic.coefficientExtensionUniformizer l E}) n := by
    obtain ⟨P, hge, hle, hfree, _, hrest⟩ := (standard_quotients_perfect l n hn).2 E
    obtain ⟨_, _, _, φ, ε, hε, _, _, _⟩ := hrest
    have hqi : QuasiIso ε := by
      have hiso : IsIso (DerivedCategory.Q.map ε) := by
        rw [hε]
        infer_instance
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := ε)).1 hiso
    let := HasDerivedCategory.standard
      (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E))
    unfold adicQuotientPerfect
    refine ⟨P, -1, 0, hge, hle, ?_, ⟨(asIso (DerivedCategory.Q.map ε)).symm⟩⟩
    intro i
    have := (hfree i).1
    exact ⟨inferInstance, (hfree i).2⟩
  refine ⟨?_, inferInstance, inferInstance, hdvr, hgen ▸ hmax, hgen,
    h.2.2.2.2.2.2.2.2.2.2.2.1, hchar, ?_, ?_⟩
  · exact isNonarchimedean_spectralNorm
  · refine ⟨{ ideal := Ideal.span {Padic.coefficientExtensionUniformizer l E}
              noetherian := inferInstance
              finitelyGenerated := Submodule.fg_span_singleton _
              quotientTorsion := ?_
              quotientFinite := fun n ↦ hfinite (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
              quotientPerfect := hperfect }, rfl⟩
    have : Finite (Padic.coefficientExtensionIntegers l E ⧸
        Ideal.span {Padic.coefficientExtensionUniformizer l E}) := by
      simpa only [Padic.coefficientExtensionRing, Padic.coefficientExtensionIdeal, pow_one]
        using hfinite 1 (by rfl)
    intro x
    exact (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
  · intro n hn
    refine ⟨hfinite n hn, ?_, Ideal.Quotient.factor_surjective _, hperfect n hn, ?_⟩
    · intro x
      rw [nsmul_eq_mul]
      have hz : ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
        apply (map_natCast (Ideal.Quotient.mk _) (l ^ n)).symm.trans
        apply (Ideal.Quotient.eq_zero_iff_mem).2
        rw [Nat.cast_pow]
        exact Ideal.pow_mem_pow (hgen.symm ▸ hlmem) n
      rw [hz, zero_mul]
    · obtain ⟨P, hge, hle, hfree, _, em, e0, hd, φ, ε, hε, hε0, hεi, _⟩ :=
        (standard_quotients_perfect l n hn).2 E
      exact ⟨P, hge, hle, hfree, em, e0, hd, φ, ε, hε, hε0, hεi⟩

end AlgebraicGeometry.Scheme
