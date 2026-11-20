import Langlands.Representation.Archimedean.ComplexStrictSwapCovariance
import Langlands.Representation.Archimedean.ComplexSphericalLieGroup

/-! # A positive spherical majorant for complex standard modules -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator
open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexSwapJacquet

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

variable {n : ℕ}

/-- The inducing character obtained by taking the absolute value of a complex character. -/
def modulusCharacterData (d : ComplexCharacterData) : ComplexCharacterData :=
  characterOfParams 0 (d.exponent.re : ℂ)

@[simp]
theorem modulusCharacterData_exponent (d : ComplexCharacterData) :
    (modulusCharacterData d).exponent = (d.exponent.re : ℂ) := rfl

@[simp]
theorem modulusCharacterData_weight (d : ComplexCharacterData) :
    (modulusCharacterData d).weight = 0 := rfl

private theorem modulusCharacterData_apply (d : ComplexCharacterData) (z : ℂˣ) :
    ((modulusCharacterData d).character z : ℂ) = (‖(d.character z : ℂ)‖ : ℂ) := by
  rw [(modulusCharacterData d).character_eq, modulusCharacterData_weight, zpow_zero, one_mul,
    modulusCharacterData_exponent, norm_character, Complex.ofReal_cpow (norm_nonneg _)]
  push_cast
  rfl

private theorem complexPositionCharacter_modulus :
    ∀ (ds : List ComplexCharacterData) (k : ℕ) (z : ℂˣ),
      complexPositionCharacter (ds.map modulusCharacterData) k z =
        (‖complexPositionCharacter ds k z‖ : ℂ)
  | [], _, _ => by simp [complexPositionCharacter]
  | d :: _, 0, z => modulusCharacterData_apply d z
  | _ :: ds, k + 1, z => complexPositionCharacter_modulus ds k z

private theorem complexPositionCharacter_ne_zero :
    ∀ (ds : List ComplexCharacterData) (k : ℕ) (z : ℂˣ),
      complexPositionCharacter ds k z ≠ 0
  | [], _, _ => one_ne_zero
  | d :: _, 0, z => (d.character z).ne_zero
  | _ :: ds, k + 1, z => complexPositionCharacter_ne_zero ds k z

/-- Taking absolute values of the inducing characters commutes with the normalized
Borel character, since the modulus factor is positive. -/
theorem principalSeriesCharacter_modulus (ds : List ComplexCharacterData) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter (ds.map modulusCharacterData)) a =
      (‖principalSeriesCharacter ℂ n (complexPositionCharacter ds) a‖ : ℂ) := by
  unfold principalSeriesCharacter
  rw [norm_prod, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [norm_mul, Complex.ofReal_mul, complexPositionCharacter_modulus]
  congr 1
  let q : ℝ := ((n : ℝ) - 1) / 2 - (k : ℕ)
  have hq : (q : ℂ) = ((n : ℂ) - 1) / 2 - (k : ℕ) := by
    dsimp only [q]
    push_cast
    rfl
  rw [← hq, ← Complex.ofReal_cpow (by positivity), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

private theorem exists_modulusSpherical (n : ℕ) (ds : List ComplexCharacterData) :
    ∃ P : KFs n (ds.map modulusCharacterData),
      ∀ k ∈ unitaryCompact ℂ n, P.val k = 1 := by
  have hw : ∀ d ∈ ds.map modulusCharacterData, d.weight = 0 := by
    intro d hd
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hd
    rfl
  obtain ⟨P, hPK, hP₁⟩ := ComplexSphericalLieGroup.exists_spherical (n := n) hw
  refine ⟨P, fun k hk => ?_⟩
  let k' : unitaryCompact ℂ n := ⟨k, hk⟩
  have h := congrArg (fun Q : KFs n (ds.map modulusCharacterData) => Q.val 1)
    (hPK (ComplexPermutation.toUnitary k'))
  change ((complexStandardRep n (ds.map modulusCharacterData)
      (ComplexPermutation.toUnitary k') P : KFs n (ds.map modulusCharacterData)) :
      Langlands.GeneralLinear n ℂ → ℂ) 1 = P.val 1 at h
  rw [principalSeriesRep_apply_coe, ComplexPermutation.toUnits_toUnitary] at h
  change P.val (1 * k) = P.val 1 at h
  change P.val 1 = 1 at hP₁
  simpa only [one_mul, hP₁] using h

/-- The spherical vector of the standard module of the absolute inducing characters,
normalized to have value one at every compact element. -/
def modulusSpherical (n : ℕ) (ds : List ComplexCharacterData) :
    KFs n (ds.map modulusCharacterData) :=
  (exists_modulusSpherical n ds).choose

theorem modulusSpherical_apply_unitary (ds : List ComplexCharacterData)
    {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    (modulusSpherical n ds).val k = 1 :=
  (exists_modulusSpherical n ds).choose_spec k hk

private theorem modulusSpherical_apply_iwasawa (ds : List ComplexCharacterData)
    (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    (modulusSpherical n ds).val (Iwasawa.diagonalUnits a * u.val * k) =
      (‖principalSeriesCharacter ℂ n (complexPositionCharacter ds) a‖ : ℂ) := by
  rw [(mem_of_mem_kFs (modulusSpherical n ds).2).2 a u k,
    modulusSpherical_apply_unitary ds hk, mul_one, principalSeriesCharacter_modulus]

theorem modulusSpherical_pos (ds : List ComplexCharacterData) (g : Langlands.GeneralLinear n ℂ) :
    0 < ((modulusSpherical n ds).val g).re := by
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [modulusSpherical_apply_iwasawa ds a u hk, Complex.ofReal_re]
  apply norm_pos_iff.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro k' _
  refine mul_ne_zero (complexPositionCharacter_ne_zero ds k' (a k')) ?_
  apply Complex.cpow_ne_zero_iff.mpr
  left
  exact Complex.ofReal_ne_zero.mpr
    (pow_ne_zero _ (norm_ne_zero_iff.mpr (a k').ne_zero))

theorem modulusSpherical_real (ds : List ComplexCharacterData) (g : Langlands.GeneralLinear n ℂ) :
    (((modulusSpherical n ds).val g).re : ℂ) = (modulusSpherical n ds).val g := by
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [modulusSpherical_apply_iwasawa ds a u hk, Complex.ofReal_re]

private theorem modulusSpherical_mul_unitary (ds : List ComplexCharacterData)
    (g : Langlands.GeneralLinear n ℂ) {k : Langlands.GeneralLinear n ℂ}
    (hk : k ∈ unitaryCompact ℂ n) :
    (modulusSpherical n ds).val (g * k) = (modulusSpherical n ds).val g := by
  obtain ⟨a, u, k', hk', rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [mul_assoc, modulusSpherical_apply_iwasawa ds a u (mul_mem hk' hk),
    modulusSpherical_apply_iwasawa ds a u hk']

theorem norm_le_mul_modulusSpherical {ds : List ComplexCharacterData}
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ complexStandardModule n ds)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℂ n, ‖f k‖ ≤ C)
    (g : Langlands.GeneralLinear n ℂ) :
    ‖f g‖ ≤ C * ((modulusSpherical n ds).val g).re := by
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [hf.2 a u k, norm_mul, modulusSpherical_apply_iwasawa ds a u hk, Complex.ofReal_re, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC k hk) (norm_nonneg _)

theorem exists_norm_le_mul_modulusSpherical {ds : List ComplexCharacterData}
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ complexStandardModule n ds) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖f g‖ ≤ C * ((modulusSpherical n ds).val g).re := by
  obtain ⟨C, hC⟩ := (ComplexDuality.isCompact_unitaryCompact n).exists_bound_of_continuousOn
    hf.1.continuous.continuousOn
  exact ⟨max C 0, le_max_right _ _, norm_le_mul_modulusSpherical hf
    (fun k hk => (hC k hk).trans (le_max_left _ _))⟩

section Swap

variable (pre post : List ComplexCharacterData) (d e : ComplexCharacterData)
  (hn : (pre ++ d :: e :: post).length = n)
  (i j : Fin n) (hi : (i : ℕ) = pre.length) (hj : (j : ℕ) = i + 1)
  (hre : 0 < (d.exponent - e.exponent).re)

local notation "ds" => (pre ++ d :: e :: post)
local notation "es" => (pre ++ e :: d :: post)

include hn hi hre in
/-- The chart integral of the positive spherical majorant is a positive scalar
multiple of the positive spherical majorant for the swapped list. -/
theorem integral_modulusSpherical_strictSwap :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Langlands.GeneralLinear n ℂ,
      (∫ z, ((modulusSpherical n ds).val (chart i j hj z * g)).re) =
        C * ((modulusSpherical n es).val g).re := by
  let m := modulusCharacterData
  have hn' : (pre.map m ++ m d :: m e :: post.map m).length = n := by simpa [m] using hn
  have hi' : (i : ℕ) = (pre.map m).length := by simpa using hi
  have hre' : 0 < ((m d).exponent - (m e).exponent).re := by
    simpa only [m, modulusCharacterData_exponent, Complex.sub_re, Complex.ofReal_re] using hre
  obtain ⟨T, hT⟩ :
      ∃ T : KFs n ((ds).map m) →ₗ[ℂ] KFs n ((es).map m),
        ∀ (g : Langlands.GeneralLinear n ℂ) (f : KFs n ((ds).map m)),
          (T f).val g = strictSwapFunction hj f.val g := by
    let HasMap (a b : List ComplexCharacterData) : Prop :=
      ∃ T : KFs n a →ₗ[ℂ] KFs n b, ∀ (g : Langlands.GeneralLinear n ℂ) (f : KFs n a),
        (T f).val g = strictSwapFunction hj f.val g
    change HasMap ((ds).map m) ((es).map m)
    simp only [List.map_append, List.map_cons]
    have h := exists_strictSwapIntertwining_apply hj (pre.map m) (post.map m)
      (m d) (m e) hn' hi' hre'
    exact h.imp (fun _ hT => hT.2.2)
  let P := modulusSpherical n ds
  have hPint (g : Langlands.GeneralLinear n ℂ) : Integrable
      (fun z => P.val (chart i j hj z * g)) := by
    have hmem : P.val ∈ complexStandardModule n (pre.map m ++ m d :: m e :: post.map m) := by
      simpa only [List.map_append, List.map_cons] using mem_of_mem_kFs P.2
    exact integrable_strictSwapFunction hj (pre.map m) (post.map m) (m d) (m e) hi' hre' hmem g
  have hKT (k : Langlands.GeneralLinear n ℂ) (hk : k ∈ unitaryCompact ℂ n) :
      (T P).val k = (T P).val 1 := by
    simp only [hT, strictSwapFunction, mul_one]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun z => modulusSpherical_mul_unitary ds (chart i j hj z) hk)
  have hval (g : Langlands.GeneralLinear n ℂ) :
      (T P).val g = (T P).val 1 * (modulusSpherical n es).val g := by
    obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
    rw [(mem_of_mem_kFs (T P).2).2 a u k, hKT k hk,
      (mem_of_mem_kFs (modulusSpherical n es).2).2 a u k,
      modulusSpherical_apply_unitary es hk, mul_one, mul_comm]
  have hrealInt (g : Langlands.GeneralLinear n ℂ) :
      (∫ z, (P.val (chart i j hj z * g)).re) = ((T P).val g).re := by
    rw [hT]
    exact integral_re (hPint g)
  refine ⟨((T P).val 1).re, ?_, fun g => ?_⟩
  · rw [← hrealInt 1]
    refine integral_pos_of_integrable_nonneg_nonzero (x := (0 : ℂ)) ?_
      (Complex.reCLM.integrable_comp (hPint 1)) (fun z => (modulusSpherical_pos ds _).le)
      (modulusSpherical_pos ds _).ne'
    simp only [mul_one]
    exact Complex.continuous_re.comp (contDiff_apply_chart (mem_of_mem_kFs P.2).1 i j hj).continuous
  · rw [hrealInt, hval g, ← modulusSpherical_real es g]
    simp

end Swap

end Langlands.Archimedean.ComplexSwapJacquet
