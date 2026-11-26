import Langlands.Automorphic.WeakAutomorphicInduction
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Automorphic.CuspidalDualPresentationExistenceProof
import Langlands.Automorphic.Unramified.WeakInductionUniqueness
import Langlands.Automorphic.Unramified.InductionBaseChangeHeckeFamily
import Langlands.Representation.Unramified.PairedHeckeScalars

/-!
# Weak induction, inverse characters and contragredients

Three facts on the unramified condition of Harris's weak automorphic induction
(Definition 1.3(b), rank-one case):

* if a spectral system is weakly induced from a Hecke character `χ`, then a system whose
  spectrum is almost everywhere the inverse of the first one is weakly induced from `χ⁻¹`:
  inverting the eigenvalues inverts the coefficients `χ_w(ϖ_w)` of the induced Euler factor
  `∏_w (1 - χ_w(ϖ_w) X ^ f(w|v))`;
* so a realization of the contragredient of a cuspidal weak induction of `χ` is a weak
  induction of `χ⁻¹`, through any spectral presentation of the contragredient;
* two spectral systems weakly induced from the same character have the same Euler
  polynomials outside a finite set, so Euler constituent recovery over the base field,
  applied to two singleton families, identifies two cuspidal weak inductions of the same
  character.
-/

noncomputable section

universe uF uE uE' uV

set_option autoImplicit false

open Polynomial

namespace Langlands.Automorphic.Unramified.WeakInduction

open Langlands.Global Langlands.Unramified
open scoped NumberField

/-- The reverse of `1 - a X ^ f` is `X ^ f - a` when `a ≠ 0`. -/
theorem reverse_one_sub_C_mul_X_pow {a : ℂ} (ha : a ≠ 0) (f : ℕ) :
    (1 - C a * X ^ f : ℂ[X]).reverse = X ^ f - C a := by
  have e : (1 : ℂ[X]) - C a * X ^ f = C (-a) * X ^ f + C 1 := by
    rw [map_neg, C_1]
    ring
  rw [e, reverse_add_C, reverse_mul_X_pow, reverse_C,
    natDegree_C_mul_X_pow f (-a) (neg_ne_zero.2 ha), C_1, one_mul, map_neg]
  ring

/-- Reversal of complex polynomials is multiplicative over finite products. -/
theorem reverse_finset_prod {ι : Type*} (T : Finset ι) (g : ι → ℂ[X]) :
    (∏ i ∈ T, g i).reverse = ∏ i ∈ T, (g i).reverse := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, ← C_1, reverse_C]
  | @insert i T hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, reverse_mul_of_domain, ih]

/-- If the Euler polynomial of a spectrum `s` is `∏_i (1 - a_i X ^ f_i)` with every
`f_i ≥ 1`, then the Euler polynomial of the inverse spectrum is `∏_i (1 - a_i⁻¹ X ^ f_i)`.
Both sides, multiplied by suitable constants, are the reverse of the Euler polynomial of
`s`, and both have constant coefficient `1`. -/
theorem eulerPolynomial_map_inv_of_eq_prod {n : ℕ} (s : Eigenvalues n) {ι : Type*} [Fintype ι]
    (a : ι → ℂˣ) (f : ι → ℕ) (hf : ∀ i, 0 < f i)
    (hs : Eigenvalues.eulerPolynomial s = ∏ i, (1 - C (a i : ℂ) * X ^ f i)) :
    Eigenvalues.eulerPolynomial (s.map fun z => z⁻¹) =
      ∏ i, (1 - C (((a i)⁻¹ : ℂˣ) : ℂ) * X ^ f i) := by
  set k : ℂ := ((s : Multiset ℂˣ).map fun z : ℂˣ => -(z : ℂ)).prod with hk
  set k' : ℂ := ∏ i, (-(a i : ℂ)) with hk'
  set Q : ℂ[X] := ∏ i, (1 - C (((a i)⁻¹ : ℂˣ) : ℂ) * X ^ f i) with hQ
  have hrev : C k * Eigenvalues.eulerPolynomial (s.map fun z => z⁻¹) = C k' * Q := by
    rw [PairedHecke.C_mul_eulerPolynomial_map_inv, hs, reverse_finset_prod, hk', hQ, map_prod,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [reverse_one_sub_C_mul_X_pow (a i).ne_zero (f i), Units.val_inv_eq_inv_val]
    have hz : -(a i : ℂ) * (a i : ℂ)⁻¹ = -1 := by rw [neg_mul, mul_inv_cancel₀ (a i).ne_zero]
    calc X ^ f i - C (a i : ℂ)
        = C (-(a i : ℂ)) - C (-(a i : ℂ) * (a i : ℂ)⁻¹) * X ^ f i := by
          rw [hz, map_neg, map_neg, map_one]
          ring
      _ = C (-(a i : ℂ)) * (1 - C (a i : ℂ)⁻¹ * X ^ f i) := by
          rw [map_mul]
          ring
  have hQ0 : Q.eval 0 = 1 := by
    rw [hQ, eval_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [eval_sub, eval_one, eval_mul, eval_C, eval_pow, eval_X, zero_pow (hf i).ne', mul_zero,
      sub_zero]
  have hkk : k = k' := by
    have h0 := congrArg (eval 0) hrev
    rwa [eval_mul, eval_mul, eval_C, eval_C, Eigenvalues.eulerPolynomial_eval_zero, mul_one, hQ0,
      mul_one] at h0
  have hk0 : C k ≠ 0 := by
    rw [Ne, C_eq_zero, hkk, hk']
    exact Finset.prod_ne_zero_iff.mpr fun i _ => neg_ne_zero.mpr (a i).ne_zero
  rw [← hkk] at hrev
  exact mul_left_cancel₀ hk0 hrev

end Langlands.Automorphic.Unramified.WeakInduction

namespace Langlands.Unramified.SpectralSystem

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.Unramified.WeakInduction
open scoped NumberField

variable {E : Type uE} {E' : Type uE'} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E']

/-- A system whose spectrum is almost everywhere the inverse of that of a weak induction
of `χ` is a weak induction of `χ⁻¹`. -/
theorem IsWeakInductionOf.inv_of_eigenvalues {n : ℕ} {s t : SpectralSystem (FinitePlace E) n}
    {χ : HeckeCharacter E'} (hs : s.IsWeakInductionOf χ)
    (hst : ∀ᶠ v in Filter.cofinite, ∀ (hv : v ∉ s.exceptional) (hv' : v ∉ t.exceptional),
      t.eigenvalues v hv' = (s.eigenvalues v hv).map fun z => z⁻¹) :
    t.IsWeakInductionOf χ⁻¹ := by
  refine ⟨hs.1, ?_⟩
  filter_upwards [hs.2, hst, s.exceptional.eventually_cofinite_notMem] with v hv hinv hvs
  intro hvt
  obtain ⟨hun, hE⟩ := hv hvs
  refine ⟨fun w => ⟨(hun w).1, fun x hx => ?_⟩, fun ϖ hϖ => ?_⟩
  · change (χ.finiteComponent w.1 x)⁻¹ = 1
    rw [(hun w).2 x hx, inv_one]
  · have hpos (w : FinitePlacesAbove E' v) : 0 < w.1.asIdeal.inertiaDeg (𝓞 E) :=
      Ideal.inertiaDeg_pos _ _
    have hEv : Eigenvalues.eulerPolynomial (s.eigenvalues v hvs) =
        ∏ w : FinitePlacesAbove E' v, (1 - C ((χ.finiteComponent w.1 (ϖ w) : ℂˣ) : ℂ) *
          X ^ (w.1.asIdeal.inertiaDeg (𝓞 E))) :=
      hE ϖ hϖ
    have h := eulerPolynomial_map_inv_of_eq_prod (s.eigenvalues v hvs)
      (fun w : FinitePlacesAbove E' v => χ.finiteComponent w.1 (ϖ w))
      (fun w : FinitePlacesAbove E' v => w.1.asIdeal.inertiaDeg (𝓞 E)) hpos hEv
    change Eigenvalues.eulerPolynomial (t.eigenvalues v hvt) =
      ∏ w : FinitePlacesAbove E' v, (1 - C ((χ⁻¹.finiteComponent w.1 (ϖ w) : ℂˣ) : ℂ) *
        X ^ (w.1.asIdeal.inertiaDeg (𝓞 E)))
    rw [hinv hvs hvt, h]
    rfl

/-- Two weak inductions of the same character have the same Euler polynomials outside a
finite set. -/
theorem IsWeakInductionOf.sameEulerPolynomials {n m : ℕ} {s : SpectralSystem (FinitePlace E) n}
    {t : SpectralSystem (FinitePlace E) m} {χ : HeckeCharacter E'}
    (hs : s.IsWeakInductionOf χ) (ht : t.IsWeakInductionOf χ) : s.SameEulerPolynomials t := by
  filter_upwards [hs.2, ht.2] with v hsv htv
  intro hvs hvt
  choose ϖ hϖ using fun w : FinitePlacesAbove E' v => exists_uniformizer w.1
  exact ((hsv hvs).2 ϖ hϖ).trans ((htv hvt).2 ϖ hϖ).symm

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic.CuspidalOperatorRealization.IsoClass

open Langlands.Global Langlands.Unramified Langlands.Automorphic.Unramified

section Contragredient

variable {E : Type uE} {E' : Type uE'} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E'] [CompactSpace (AdeleQuotient E)] {r : ℕ}

/-- If `Sd` realizes the contragredient of a cuspidal weak induction `S` of `χ`, then `Sd`
is a weak induction of `χ⁻¹`: a spectral presentation of `Sd` has, outside the exceptional
sets, the inverse spectrum of a presentation of `S`. -/
theorem isWeakAutomorphicInductionOf_inv_of_isContragredientOf
    (S Sd : CuspidalOperatorRealization E r)
    (hSd : Sd.realization.IsContragredientOf S.realization) {χ : HeckeCharacter E'}
    (h : IsWeakAutomorphicInductionOf.{uE, uE', uV} S.isoClass χ) :
    IsWeakAutomorphicInductionOf.{uE, uE', uV} Sd.isoClass χ⁻¹ := by
  obtain ⟨P, hP⟩ := (isWeakAutomorphicInductionOf_iff S χ).mp h
  obtain ⟨Pd⟩ := cuspidalDualPresentationExistence.{uE, uV, uV} E r S Sd hSd P
  exact (isWeakAutomorphicInductionOf_iff Sd χ⁻¹).mpr ⟨Pd, hP.inv_of_eigenvalues
    (Filter.Eventually.of_forall fun v hv hv' =>
      S.eigenvalues_eq_map_inv_of_isContragredientOf Sd P Pd hSd v hv hv')⟩

end Contragredient

section Uniqueness

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- Euler constituent recovery over `F`, applied to two singleton families: two cuspidal
classes over `F` with attached systems having the same Euler polynomials outside a finite
set are equal. The hypothesis is `CuspidalEulerConstituentRecoveryStatement` at the field
`F`. -/
theorem eq_of_sameEulerPolynomials
    (hRig : ∀ (p q : ℕ) (c : Fin p → PositiveRankCuspidalClass F)
      (d : Fin q → PositiveRankCuspidalClass F)
      (s : ∀ i, SpectralSystem (FinitePlace F) (c i).rank)
      (t : ∀ j, SpectralSystem (FinitePlace F) (d j).rank),
      (∀ i, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (c i) (s i)) →
      (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV} (d j) (t j)) →
      (SpectralSystem.finiteSum s).SameEulerPolynomials (SpectralSystem.finiteSum t) →
      ∃ e : Fin p ≃ Fin q, ∀ i, c i = d (e i))
    {c d : IsoClass F r} {s t : SpectralSystem (FinitePlace F) (r + 1)}
    (hc : HasSpectralSystem.{uF, uV} c s) (hd : HasSpectralSystem.{uF, uV} d t)
    (hst : s.SameEulerPolynomials t) : c = d := by
  let c₁ : Fin 1 → PositiveRankCuspidalClass F := fun _ => PositiveRankCuspidalClass.ofFixedRank c
  let d₁ : Fin 1 → PositiveRankCuspidalClass F := fun _ => PositiveRankCuspidalClass.ofFixedRank d
  let sc : ∀ i, SpectralSystem (FinitePlace F) (c₁ i).rank := fun _ => s
  let sd : ∀ i, SpectralSystem (FinitePlace F) (d₁ i).rank := fun _ => t
  have hsum := (IsobaricData.sameEulerPolynomials_finiteSum_one sc).symm.trans
    (hst.trans (IsobaricData.sameEulerPolynomials_finiteSum_one sd))
  obtain ⟨e, he⟩ := hRig 1 1 c₁ d₁ sc sd (fun _ => hc) (fun _ => hd) hsum
  exact PositiveRankCuspidalClass.ofFixedRank_injective r (he 0)

end Uniqueness

end Langlands.Automorphic.CuspidalOperatorRealization.IsoClass
