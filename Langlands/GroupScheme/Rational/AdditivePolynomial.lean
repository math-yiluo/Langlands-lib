import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-! # Additive polynomials cut out by subgroup conditions, and their composition maps -/

noncomputable section

universe u

open Polynomial

namespace Langlands.GroupScheme.RelativeRoot.AdditivePolynomial

variable {k : Type u} [Field k]

/-- A two-variable polynomial whose coefficients, as polynomials in the inner variable, and
whose degree in the outer variable are both below the degree of a monic `f`, lies in the
ideal `(f(X), f(Y))` only if it is zero. -/
theorem eq_zero_of_mem_span {f : k[X]} (hf : f.Monic) {h : k[X][X]}
    (hmem : h ∈ Ideal.span {C f, f.map C}) (hdeg : h.degree < (f.map (C : k →+* k[X])).degree)
    (hcoeff : ∀ n, (h.coeff n).natDegree < f.natDegree) : h = 0 := by
  have hF : (f.map (C : k →+* k[X])).Monic := hf.map C
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hmem
  have hmod : (a * C f + b * f.map C) %ₘ f.map C = C f * (a %ₘ f.map C) := by
    rw [add_modByMonic, (modByMonic_eq_zero_iff_dvd hF).mpr (dvd_mul_left _ _), add_zero,
      mul_comm, ← smul_eq_C_mul, smul_modByMonic, smul_eq_C_mul]
  have hself := (modByMonic_eq_self_iff hF).mpr hdeg
  rw [hself] at hmod
  rw [hmod] at hcoeff ⊢
  have ha : a %ₘ f.map C = 0 := by
    refine Polynomial.ext fun n => ?_
    rw [coeff_zero]
    by_contra hne
    have h1 := hcoeff n
    rw [coeff_C_mul, hf.natDegree_mul' hne] at h1
    omega
  rw [ha, mul_zero]

/-- The coefficients of `f(X + Y)`, expanded in the outer variable `Y`, are the Hasse
derivatives of `f`. -/
theorem taylor_map_coeff (f : k[X]) (n : ℕ) :
    (taylor (X : k[X]) (f.map C)).coeff n = hasseDeriv n f := by
  rw [taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X]

/-- If `f(X + Y)` lies in `(f(X), f(Y))` for a monic nonconstant `f`, then
`f(X + Y) = f(X) + f(Y)`. -/
theorem taylor_eq_of_mem_span {f : k[X]} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hmem : taylor (X : k[X]) (f.map C) ∈ Ideal.span {C f, f.map C}) :
    taylor (X : k[X]) (f.map C) = f.map C + C f := by
  set h := taylor (X : k[X]) (f.map C) - f.map C - C f with hh
  have hcoeffh : ∀ n, h.coeff n = hasseDeriv n f - C (f.coeff n) - if n = 0 then f else 0 := by
    intro n
    rw [hh, coeff_sub, coeff_sub, taylor_map_coeff, coeff_map, coeff_C]
  have hmemh : h ∈ Ideal.span {C f, f.map C} :=
    Ideal.sub_mem _ (Ideal.sub_mem _ hmem (Ideal.subset_span (by simp)))
      (Ideal.subset_span (by simp))
  have hzero : h = 0 := by
    refine eq_zero_of_mem_span hf hmemh ?_ ?_
    · rw [hf.degree_map C, degree_eq_natDegree hf.ne_zero, degree_lt_iff_coeff_zero]
      intro m hm
      rw [hcoeffh, ite_eq_right (by omega)]
      rcases (Nat.lt_or_eq_of_le hm) with hlt | heq
      · rw [hasseDeriv_eq_zero_of_lt_natDegree _ _ hlt, coeff_eq_zero_of_natDegree_lt hlt]
        simp
      · subst heq
        rw [hasseDeriv_natDegree_eq_C]
        simp
    · intro n
      rw [hcoeffh]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hasseDeriv_zero, LinearMap.id_apply, ite_eq_left rfl, sub_sub_cancel_left,
          natDegree_neg, natDegree_C]
        exact hd
      · rw [ite_eq_right (by omega), sub_zero]
        refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
        rw [natDegree_C, max_lt_iff]
        refine ⟨lt_of_le_of_lt (natDegree_hasseDeriv_le f n) (by omega), hd⟩
  rw [hh, sub_sub, sub_eq_zero] at hzero
  exact hzero

/-- The identity `f(X + Y) = f(X) + f(Y)` evaluates to additivity in every commutative ring. -/
theorem eval₂_add_of_taylor_eq {f : k[X]}
    (htaylor : taylor (X : k[X]) (f.map C) = f.map C + C f)
    {S : Type*} [CommRing S] (ρ : k →+* S) (a b : S) :
    f.eval₂ ρ (a + b) = f.eval₂ ρ a + f.eval₂ ρ b := by
  have h := congrArg (eval₂ (eval₂RingHom ρ a) b) htaylor
  have hc : (eval₂RingHom ρ a).comp C = ρ := by
    ext c
    simp
  rw [taylor_apply, eval₂_comp] at h
  simp only [eval₂_add, eval₂_X, eval₂_C, eval₂_map, hc, coe_eval₂RingHom] at h
  rw [add_comm a b, h, add_comm]

/-- The composition map `p ↦ p ∘ f`. -/
def compHom (f : k[X]) : k[X] →+* k[X] :=
  (aeval f : k[X] →ₐ[k] k[X]).toRingHom

theorem compHom_apply (f p : k[X]) : compHom f p = aeval f p :=
  rfl

theorem compHom_C (f : k[X]) (c : k) : compHom f (C c) = C c := by
  simp [compHom]

theorem compHom_X (f : k[X]) : compHom f X = f := by
  simp [compHom]

theorem compHom_comp_C (f : k[X]) : (compHom f).comp C = C :=
  RingHom.ext fun c => compHom_C f c

theorem compHom_injective {f : k[X]} (hd : 0 < f.natDegree) :
    Function.Injective (compHom f) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [compHom_apply, ← comp_eq_aeval, comp_eq_zero_iff] at hp
  rcases hp with hp | ⟨-, hc⟩
  · exact hp
  · exfalso
    have := congrArg natDegree hc
    rw [natDegree_C] at this
    omega

/-- The variable is integral over the composition map of a monic nonconstant polynomial. -/
theorem compHom_isIntegralElem_X {f : k[X]} (hf : f.Monic) (hd : 0 < f.natDegree) :
    (compHom f).IsIntegralElem X := by
  refine ⟨f.map C - C X, (hf.map C).sub_of_left ?_, ?_⟩
  · rw [hf.degree_map C, degree_eq_natDegree hf.ne_zero]
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hd)
  · rw [eval₂_sub, eval₂_map, compHom_comp_C, eval₂_C, compHom_X, eval₂_C_X, sub_self]

theorem compHom_isIntegral {f : k[X]} (hf : f.Monic) (hd : 0 < f.natDegree) :
    (compHom f).IsIntegral := by
  have hpow : ∀ n : ℕ, (compHom f).IsIntegralElem (X ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, ← map_one (compHom f)]
      exact (compHom f).isIntegralElem_map
    | succ n ih =>
      rw [pow_succ]
      exact RingHom.IsIntegralElem.mul _ ih (compHom_isIntegralElem_X hf hd)
  intro p
  induction p using Polynomial.induction_on with
  | C c =>
    rw [← compHom_C f c]
    exact (compHom f).isIntegralElem_map
  | add p q hp hq => exact RingHom.IsIntegralElem.add _ hp hq
  | monomial n c _ =>
    rw [← compHom_C f c]
    exact RingHom.IsIntegralElem.mul _ (compHom f).isIntegralElem_map (hpow _)

/-- An injective ring map from a Dedekind domain to a domain is flat. -/
theorem flat_of_injective {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A]
    [IsDomain B] {φ : A →+* B} (hφ : Function.Injective φ) : φ.Flat := by
  algebraize [φ]
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem compHom_flat {f : k[X]} (hd : 0 < f.natDegree) : (compHom f).Flat :=
  flat_of_injective (compHom_injective hd)

theorem compHom_faithfullyFlat {f : k[X]} (hf : f.Monic) (hd : 0 < f.natDegree) :
    (compHom f).FaithfullyFlat :=
  RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
    ⟨compHom_flat hd, (compHom_isIntegral hf hd).comap_surjective (compHom_injective hd)⟩

theorem compHom_finitePresentation (f : k[X]) : (compHom f).FinitePresentation := by
  refine RingHom.FinitePresentation.of_finiteType.mp ?_
  refine RingHom.FiniteType.of_comp_finiteType (f := (C : k →+* k[X])) ?_
  rw [compHom_comp_C]
  change (algebraMap k k[X]).FiniteType
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end Langlands.GroupScheme.RelativeRoot.AdditivePolynomial
