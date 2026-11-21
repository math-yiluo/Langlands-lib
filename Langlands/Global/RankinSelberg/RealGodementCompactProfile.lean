import Langlands.Global.RankinSelberg.RealIwasawa
import Langlands.Global.RankinSelberg.RealUniformWhittakerDual
import Langlands.Representation.Archimedean.RealDiscreteSeparatedSource

/-! # Fixed compact profiles of real standard modules at all character exponents -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodementProfiles

open GramFormula PrincipalSeriesExtension RealIwasawa RealJacquetFrobenius
open RealUniformWhittakerDual

variable {n : ℕ}

local notation "P" => (Fin n → ℂ)
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "K" => unitaryCompact ℝ n
local notation "U" => Matrix.unitaryGroup (Fin n) ℝ
local notation "ρ" => Whittaker.rightTranslation ℂ G

/-- A real character list with fixed signs and varying complex exponents. -/
def characterList (p : Fin n → Fin 2) (z : P) : List RealBlock :=
  (List.ofFn fun i => charData (p i) (z i)).map RealBlock.character

theorem realRank_characterList (p : Fin n → Fin 2) (z : P) : realRank (characterList p z) = n := by
  simp only [characterList, realRank_map_character, List.length_ofFn]

theorem characterList_cons (p : Fin (n + 1) → Fin 2) (z : Fin (n + 1) → ℂ) :
    characterList p z = .character (charData (p 0) (z 0)) ::
      characterList (fun i => p i.succ) (fun i => z i.succ) := by
  rw [characterList, List.ofFn_succ]
  rfl

theorem realPositionCharacter_characterList (p : Fin n → Fin 2) (z : P)
    (i : Fin n) (x : ℝˣ) : realPositionCharacter (characterList p z) i x = charFun (p i) (z i) x := by
  rw [characterList, realPositionCharacter_map_character _ i (by simp)]
  simp only [List.getElem_ofFn, charData_character_apply]

theorem realPositionExponent_characterList (p : Fin n → Fin 2) (z : P) (i : Fin n) :
    realPositionExponent (characterList p z) i = z i := by
  rw [characterList, RealDiscreteSeparated.realPositionExponent_map_character _ i (by simp)]
  rw [List.getElem_ofFn]
  rfl

private theorem signBorel_characterList (p : Fin n → Fin 2) (z : P) (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter (characterList p z)) (fun i => signUnit (a i)) =
      ∏ i : Fin n, ((signReal (a i : ℝ) : ℝ) : ℂ) ^ (p i).val := by
  unfold principalSeriesCharacter
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [realPositionCharacter_characterList]
  unfold RealJacquetFrobenius.charFun
  simp only [Module.finrank_self, pow_one, Real.norm_eq_abs, signUnit_val, abs_signReal, div_one,
    Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- A continuous K-finite function on the orthogonal group with the specified diagonal signs. -/
def IsCompactProfile (p : Fin n → Fin 2) (φ : U → ℂ) : Prop :=
  Continuous φ ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : U => fun x => φ (x * k))) ∧
    ∀ (a : Fin n → ℝˣ) (k : U),
      φ (signDiagonal (fun i => (a i : ℝ)) * k) =
        (∏ i : Fin n, ((signReal (a i : ℝ) : ℝ) : ℂ) ^ (p i).val) * φ k

private def normalization (i : Fin n) : ℂ := ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)

/-- Extend the fixed orthogonal profile with the supplied real-position exponents. -/
def standardSection (z : P) (φ : U → ℂ) : G → ℂ := extension (z + normalization) φ

private theorem shiftedExponent_characterList (p : Fin n → Fin 2) (z : P) :
    shiftedExponent n (realPositionExponent (characterList p z)) = z + normalization := by
  ext i
  simp only [shiftedExponent, realPositionExponent_characterList, Pi.add_apply, normalization]

/-- Restriction to the orthogonal subgroup, indexed by orthogonal matrices. -/
def compactRestriction : (G → ℂ) →ₗ[ℂ] (U → ℂ) where
  toFun f k := f (Unitary.toUnits k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem compactRestriction_standardSection (φ : U → ℂ) (z : P) :
    compactRestriction (standardSection z φ) = φ := by
  funext k
  exact extension_unitary (z + normalization) φ k

private def compactPart (g : G) : U := ⟨(kpart g).val.val, (kpart g).property⟩

private theorem continuous_compactPart : Continuous (compactPart (n := n)) :=
  (Units.continuous_val.comp (continuous_subtype_val.comp continuous_kpart)).subtype_mk _

theorem standardSection_eq (φ : U → ℂ) (z : P) (g : G) :
    standardSection z φ g = Complex.exp (∑ i : Fin n, (alpha g i : ℂ) * (z i + normalization i)) *
      φ (compactPart g) := by
  let b := bpart g
  have hb := isPosUpper_bpart g
  have hx : g.val = b.val * (compactPart g).val := congrArg Units.val (bpart_mul_kpart g).symm
  have hsign : signDiagonal (fun i => b.val i i) = 1 := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => signReal (b.val i i)) = (1 : Matrix (Fin n) (Fin n) ℝ)
    have hb' (i : Fin n) : 0 < b.val i i := hb.2 i
    simp only [signReal, hb', ite_true, Matrix.diagonal_one]
  rw [standardSection, extension_eq _ φ hb.1 (fun i => (hb.2 i).ne') (compactPart g).property hx,
    hsign, one_mul, Complex.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [abs_of_pos (hb.2 i), ← exp_alpha g i,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  rfl

theorem continuous_standardSection_family {φ : U → ℂ} (hφ : Continuous φ) :
    Continuous (fun q : P × G => standardSection q.1 φ q.2) := by
  simp_rw [standardSection_eq]
  refine (continuous_finsetSum _ fun i _ => ?_).cexp.mul (hφ.comp (continuous_compactPart.comp continuous_snd))
  have hα : Continuous (fun q : P × G => (alpha q.2 i : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_apply i).comp (continuous_alpha.comp continuous_snd))
  exact hα.mul (((continuous_apply i).comp continuous_fst).add continuous_const)

theorem differentiable_standardSection (φ : U → ℂ) (g : G) :
    Differentiable ℂ (fun z : P => standardSection z φ g) := by
  simp_rw [standardSection_eq]
  refine (Differentiable.fun_sum fun i _ => ?_).cexp.mul_const _
  exact (((ContinuousLinearMap.proj i : P →L[ℂ] ℂ).differentiable).add_const _).const_mul _

theorem standardSection_mem {p : Fin n → Fin 2} {φ : U → ℂ} (hφ : IsCompactProfile p φ) (z : P) :
    standardSection z φ ∈ Automorphic.realStandardKFinite n (characterList p z) := by
  have hM (a : Fin n → ℝˣ) (κ : U) :
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ n (realPositionCharacter (characterList p z)) (fun i => signUnit (a i)) * φ κ := by
    rw [signBorel_characterList]
    exact hφ.2.2 a κ
  have h := extension_mem_kFiniteFunctions (realPositionExponent (characterList p z))
    (realPositionCharacter_eq_signUnit_mul _) hφ.1 hφ.2.1 hM
  rw [shiftedExponent_characterList] at h
  rw [characterList, standardKFinite_map_character]
  exact h

theorem isCompactProfile_of_mem_principalSeries {p : Fin n → Fin 2} {z : P} {f : G → ℂ}
    (hf : f ∈ principalSeries ℝ n (realPositionCharacter (characterList p z)))
    (hFin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : U =>
      fun x => compactRestriction f (x * k)))) : IsCompactProfile p (compactRestriction f) := by
  refine ⟨hf.1.continuous.comp continuous_unitary_toUnits, hFin, ?_⟩
  intro a k
  change f (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * k)) = _
  rw [PartialJacquet.signDiagonal_toUnits, ← signBorel_characterList p z]
  have h := hf.2 (fun i => signUnit (a i)) 1 (Unitary.toUnits k)
  change f _ = _ * f (Unitary.toUnits k)
  simpa only [OneMemClass.coe_one, mul_one] using h

theorem isCompactProfile_compactRestriction {p : Fin n → Fin 2} {z : P} {f : G → ℂ}
    (hf : f ∈ Automorphic.realStandardKFinite n (characterList p z)) :
    IsCompactProfile p (compactRestriction f) := by
  apply isCompactProfile_of_mem_principalSeries hf.1.1
  let V : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun k : K => ρ k.val f)
  let : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hf.2
  apply Submodule.finiteDimensional_of_le (S₂ := V.map compactRestriction)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let q : K := ⟨Unitary.toUnits k, k.property⟩
  refine ⟨ρ q.val f, Submodule.subset_span ⟨q, rfl⟩, ?_⟩
  funext x
  change f (Unitary.toUnits x * Unitary.toUnits k) = f (Unitary.toUnits (x * k))
  rw [map_mul]

theorem standardSection_compactRestriction {p : Fin n → Fin 2} {z : P} {f : G → ℂ}
    (hf : f ∈ Automorphic.realStandardKFinite n (characterList p z)) :
    standardSection z (compactRestriction f) = f := by
  apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (standardSection_mem (isCompactProfile_compactRestriction hf) z).1.1 hf.1.1
  intro g hg
  let k : U := ⟨g.val, hg⟩
  have he : Unitary.toUnits k = g := Units.ext rfl
  rw [← he, standardSection, extension_unitary]
  rfl

/-- Compact profiles for fixed real parities extend jointly continuously and pointwise
holomorphically to the K-finite standard sections at every exponent. -/
def RealGodementCompactProfileStatement : Prop :=
  ∀ (p : Fin n → Fin 2) (φ : U → ℂ), IsCompactProfile p φ →
    (∀ z : P, standardSection z φ ∈ Automorphic.realStandardKFinite n (characterList p z)) ∧
    Continuous (fun q : P × G => standardSection q.1 φ q.2) ∧
    ∀ g : G, Differentiable ℂ (fun z : P => standardSection z φ g)

theorem realGodementCompactProfile : RealGodementCompactProfileStatement (n := n) := by
  intro p φ hφ
  exact ⟨standardSection_mem hφ, continuous_standardSection_family hφ.1, differentiable_standardSection φ⟩

end Langlands.Global.RankinSelbergGlobal.RealGodementProfiles
