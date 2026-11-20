import Langlands.Global.RankinSelberg.ComplexLocalIwasawa
import Langlands.Representation.Archimedean.ComplexBlockLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension

/-! # Complex standard sections with a fixed compact profile -/

noncomputable section

open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCompactProfileFamily

open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent
  principalSeriesCharacter complexPositionCharacter unitaryCompact mem_kFiniteVectors_iff continuous_unitary_toUnits)
open Langlands.Archimedean.ComplexBlockLanglandsQuotient (complexPositionWeight_ofFn complexPositionExponent_ofFn)
open Langlands.Archimedean.ComplexGramFormula (phaseUnit phaseUnit_val norm_phaseUnit
  complexPositionExponent complexPositionCharacter_eq_phaseUnit_mul)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (extension extension_iwasawa phaseMatrix phaseMatrix_val)
open Langlands.Archimedean.ComplexStrictLanglandsQuotient (complexPositionCharacter_phase)
open Langlands.Archimedean.GramFormula (shiftedExponent)
open ComplexLocalIwasawa (alpha kpart npart continuous_alpha continuous_kpart npart_mul_logTorus_mul_kpart
  conjTorus conjTorus_val logTorus_neg)
open ComplexLocalWhittakerGauge (logTorus)

variable {n : ℕ}
local notation "P" => Fin n → ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "U" => Matrix.unitaryGroup (Fin n) ℂ

/-- The list of characters with fixed unitary weights and varying complex radial exponents. -/
def characterList (l : Fin n → ℤ) (p : P) : List Langlands.LocalFactor.Archimedean.ComplexCharacterData :=
  List.ofFn fun i => characterOfParams (l i) (p i)

theorem phase_borel_character (l : Fin n → ℤ) (p : P) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter (characterList l p)) (fun i => phaseUnit (a i)) =
      ∏ i : Fin n, ((phaseUnit (a i) : ℂˣ) : ℂ) ^ l i := by
  unfold principalSeriesCharacter
  apply Finset.prod_congr rfl
  intro i _
  rw [complexPositionCharacter_phase, characterList, complexPositionWeight_ofFn,
    characterOfParams_weight, norm_phaseUnit]
  simp

/-- A continuous compact-finite profile with the torus covariance of the given angular weights. -/
def IsCompactProfile (l : Fin n → ℤ) (φ : U → ℂ) : Prop :=
  Continuous φ ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : U => fun x => φ (x * k))) ∧
    ∀ (a : Fin n → ℂˣ) (k : U),
      φ (phaseMatrix a * k) = (∏ i : Fin n, ((phaseUnit (a i) : ℂˣ) : ℂ) ^ l i) * φ k

private def rho (i : Fin n) : ℂ := ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)

/-- Extend the fixed unitary profile with the normalized inducing exponent on each diagonal entry. -/
def standardSection (p : P) (φ : U → ℂ) : G → ℂ := extension (p + rho) φ

private theorem shifted_eq (l : Fin n → ℤ) (p : P) :
    shiftedExponent n (complexPositionExponent (characterList l p)) = p + rho := by
  ext i
  simp only [shiftedExponent, characterList, complexPositionExponent_ofFn, characterOfParams_exponent,
    Pi.add_apply, rho]

private def compactPart (g : G) : U := ⟨(kpart g).val.val, (kpart g).2⟩

private theorem continuous_compactPart : Continuous (compactPart (n := n)) :=
  (Units.continuous_val.comp (continuous_subtype_val.comp continuous_kpart)).subtype_mk _

private theorem standardSection_eq (p : P) (φ : U → ℂ) (g : G) :
    standardSection p φ g = Complex.exp (∑ i : Fin n, ((2 * alpha g i : ℝ) : ℂ) * (p i + rho i)) *
      φ (compactPart g) := by
  let y := alpha g
  let a : Fin n → ℂˣ := fun i => Units.mk0 (Real.exp (y i) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  let u := conjTorus (-y) (npart g)
  have hdecomp : Langlands.GeneralLinear.Iwasawa.diagonalUnits a * u.val * (kpart g).val = g := by
    change logTorus y * (conjTorus (-y) (npart g)).val * (kpart g).val = _
    rw [conjTorus_val, logTorus_neg, inv_inv]
    calc
      _ = (npart g).val * logTorus y * (kpart g).val := by group
      _ = g := npart_mul_logTorus_mul_kpart g
  have ha (i : Fin n) : ‖(a i : ℂ)‖ = Real.exp (y i) := Complex.norm_of_nonneg (Real.exp_pos _).le
  have hphase : phaseMatrix a = 1 := by
    have h (i : Fin n) : phaseUnit (a i) = 1 := by
      apply Units.ext
      rw [phaseUnit_val, ha]
      exact div_self (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    apply Subtype.ext
    simp [phaseMatrix_val, h, Matrix.diagonal_one]
  have hex := extension_iwasawa (p + rho) φ a u (kpart g).2
  rw [hdecomp, hphase, one_mul] at hex
  rw [standardSection, hex, Complex.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ha, ← Real.exp_nat_mul, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)), ← Complex.ofReal_log (Real.exp_pos _).le,
    Real.log_exp]
  norm_num [y]

theorem continuous_standardSection_family {φ : U → ℂ} (hφ : Continuous φ) :
    Continuous (fun a : P × G => standardSection a.1 φ a.2) := by
  have he : (fun a : P × G => standardSection a.1 φ a.2) = fun a =>
      Complex.exp (∑ i : Fin n, ((2 * alpha a.2 i : ℝ) : ℂ) * (a.1 i + rho i)) * φ (compactPart a.2) :=
    funext fun a => standardSection_eq a.1 φ a.2
  rw [he]
  refine (Continuous.cexp ?_).mul (hφ.comp (continuous_compactPart.comp continuous_snd))
  apply continuous_finsetSum
  intro i _
  have hlog : Continuous (fun a : P × G => 2 * alpha a.2 i) :=
    (((continuous_apply i).comp continuous_alpha).comp continuous_snd).const_mul 2
  have hexp : Continuous (fun a : P × G => a.1 i) := (continuous_apply i).comp continuous_fst
  exact (Complex.continuous_ofReal.comp hlog).mul (hexp.add_const (rho i))

theorem differentiable_standardSection (φ : U → ℂ) (g : G) :
    Differentiable ℂ (fun p : P => standardSection p φ g) := by
  simp_rw [standardSection_eq]
  refine (Differentiable.cexp ?_).mul_const (φ (compactPart g))
  exact Differentiable.fun_sum fun i _ =>
    (((ContinuousLinearMap.proj i : P →L[ℂ] ℂ).differentiable).add_const (rho i)).const_mul _

theorem standardSection_mem {l : Fin n → ℤ} {φ : U → ℂ} (hφ : IsCompactProfile l φ) (p : P) :
    standardSection p φ ∈ Automorphic.complexStandardKFinite n (characterList l p) := by
  rw [standardSection, ← shifted_eq l p]
  refine Langlands.Archimedean.ComplexPrincipalSeriesExtension.extension_mem_kFiniteFunctions
    _ (complexPositionCharacter_eq_phaseUnit_mul (characterList l p)) hφ.1 hφ.2.1 ?_
  intro a k
  rw [phase_borel_character]
  exact hφ.2.2 a k

theorem standardSection_unitary (p : P) (φ : U → ℂ) (k : U) : standardSection p φ (Unitary.toUnits k) = φ k :=
  Langlands.Archimedean.ComplexPrincipalSeriesExtension.extension_unitary _ φ k

/-- The linear restriction of group functions to the unitary subgroup. -/
def compactRestriction : (G → ℂ) →ₗ[ℂ] (U → ℂ) :=
  LinearMap.pi fun k => LinearMap.proj (R := ℂ) (Unitary.toUnits k)

theorem compactRestriction_isCompactProfile {l : Fin n → ℤ} {p : P} {f : G → ℂ}
    (hf : f ∈ Automorphic.complexStandardKFinite n (characterList l p)) :
    IsCompactProfile l (compactRestriction f) := by
  have hcont : Continuous (compactRestriction f) := hf.1.1.continuous.comp continuous_unitary_toUnits
  refine ⟨hcont, ?_, ?_⟩
  · let V := Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
      Langlands.Whittaker.rightTranslation ℂ G k.val f)
    have : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hf.2
    apply Submodule.finiteDimensional_of_le (S₂ := V.map compactRestriction)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    let k' : unitaryCompact ℂ n := ⟨Unitary.toUnits k, k.2⟩
    refine ⟨Langlands.Whittaker.rightTranslation ℂ G k'.val f, Submodule.subset_span ⟨k', rfl⟩, ?_⟩
    funext x
    change f (Unitary.toUnits x * Unitary.toUnits k) = f (Unitary.toUnits (x * k))
    rw [map_mul]
  · intro a k
    have hphase : Unitary.toUnits (phaseMatrix a) =
        Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun i => phaseUnit (a i)) := by
      apply Units.ext
      change (phaseMatrix a).val = _
      rw [phaseMatrix_val]
      rfl
    change f (Unitary.toUnits (phaseMatrix a * k)) = _ * f (Unitary.toUnits k)
    rw [map_mul, hphase]
    have h := hf.1.2 (fun i => phaseUnit (a i)) 1 (Unitary.toUnits k)
    simpa only [Subgroup.coe_one, mul_one, phase_borel_character] using h

theorem standardSection_compactRestriction {l : Fin n → ℤ} {p : P} {f : G → ℂ}
    (hf : f ∈ Automorphic.complexStandardKFinite n (characterList l p)) :
    standardSection p (compactRestriction f) = f := by
  refine Langlands.Archimedean.ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary
    (standardSection_mem (compactRestriction_isCompactProfile hf) p).1 hf.1 (fun g hg => ?_)
  let k : U := ⟨g.val, hg⟩
  have hk : Unitary.toUnits k = g := Units.ext rfl
  rw [← hk, standardSection_unitary]
  rfl

/-- A fixed admissible compact profile gives a holomorphic family in the actual compact-finite
complex standard modules for all inducing exponents, and compact restriction recovers the
profile of every compact-finite standard vector. -/
def ComplexCompactProfileFamilyStatement : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℤ),
    (∀ (φ : Matrix.unitaryGroup (Fin n) ℂ → ℂ), IsCompactProfile l φ →
      (∀ p, standardSection p φ ∈ Automorphic.complexStandardKFinite n (characterList l p)) ∧
      (∀ p k, standardSection p φ (Unitary.toUnits k) = φ k) ∧
      Continuous (fun a : (Fin n → ℂ) × Langlands.GeneralLinear n ℂ => standardSection a.1 φ a.2) ∧
      ∀ g : Langlands.GeneralLinear n ℂ, Differentiable ℂ (fun p : Fin n → ℂ => standardSection p φ g)) ∧
    ∀ (p : Fin n → ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ),
      f ∈ Automorphic.complexStandardKFinite n (characterList l p) →
      IsCompactProfile l (compactRestriction f) ∧ standardSection p (compactRestriction f) = f

theorem complexCompactProfileFamily : ComplexCompactProfileFamilyStatement := by
  intro n l
  refine ⟨fun φ hφ => ⟨standardSection_mem hφ, fun p k => standardSection_unitary p φ k,
    continuous_standardSection_family hφ.1, differentiable_standardSection φ⟩, fun p f hf => ?_⟩
  exact ⟨compactRestriction_isCompactProfile hf, standardSection_compactRestriction hf⟩

end Langlands.Global.RankinSelbergGlobal.ComplexCompactProfileFamily
