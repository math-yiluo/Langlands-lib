import Langlands.Representation.Archimedean.RealLeviTorus
import Langlands.Representation.Archimedean.RealInducedStandardBound
import Langlands.Representation.Archimedean.RealBlockFourierPropagation
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.Archimedean.JacquetKernel

/-!
# Torus modes of principal-series functions and the annihilator of a standard module

Let `ds` be a list of real blocks of rank `n`, `χ` its position characters and `S` the slots of its
induction blocks. The standard module `X` of `ds` is the subspace of the principal series of `χ`
cut out by the vanishing of the Fourier modes `|j| < m` along the rotations of every induction
block of weight `m`. This module characterizes, inside the `O(n)`-finite principal series of the
inverse characters `χ⁻¹`, the functions `v` with `∫_{O(n)} v x = 0` for every `O(n)`-finite
`x ∈ X`: they are exactly the functions whose jointly allowed torus modes vanish on `O(n)`
(`IsNull`). Dually, an `O(n)`-finite `x` of the principal series of `χ` lies in `X` if and only if
it pairs to zero with every such `v` (`RealLeviModesStatement`, proof `realLeviModes`).

The tools are: sign reflections and block Fourier coefficients, the phase of iterated
coefficients under block rotations, the torus average of `O(n)`-integrals, an orthogonality
relation, symmetrized coefficients (the sum over the modes `±j` at every slot) and the extension
of conjugated functions on `O(n)` to the principal series.
-/

noncomputable section

open MeasureTheory Matrix ComplexConjugate

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviModes

open RealInducedBlockBound RealInducedTorusCore RealLeviTorus RealBlockRotation
  RealBlockFourierFinite RealPrincipalSeriesDuality RealBlockJacquet PrincipalSeriesExtension
  GramFormula PartialJacquet RealInducedStandardBound

attribute [local instance] measurableSpaceK

local instance borelSpaceK_lm (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

attribute [local instance] RealBlockLimit.secondCountableTopology_unitaryCompact

variable {N : ℕ}

/-! ## Sign reflections -/

section Signs

/-- `r_p(θ) s_i = s_i r_p(-θ)` for `i ∈ {p, p + 1}`. -/
theorem blockRotation_mul_signReflection_of_mem {p : ℕ} (hp : p + 1 < N) (i : Fin N)
    (hi : (i : ℕ) = p ∨ (i : ℕ) = p + 1) (θ : ℝ) (g : Langlands.GeneralLinear N ℝ) :
    blockRotation N p θ * ((Unitary.toUnits (signReflection N i) :
        Langlands.GeneralLinear N ℝ) * g) =
      Unitary.toUnits (signReflection N i) * (blockRotation N p (-θ) * g) := by
  rw [← signReflection_mul_blockRotation_mul_of_mem hp i hi θ]
  simp only [mul_assoc, toUnits_signReflection_mul_mul_self]

/-- `r_p(θ) s_i = s_i r_p(θ)` for `i ∉ {p, p + 1}`. -/
theorem blockRotation_mul_signReflection_of_not_mem {p : ℕ} (hp : p + 1 < N) (i : Fin N)
    (hi : (i : ℕ) ≠ p ∧ (i : ℕ) ≠ p + 1) (θ : ℝ) (g : Langlands.GeneralLinear N ℝ) :
    blockRotation N p θ * ((Unitary.toUnits (signReflection N i) :
        Langlands.GeneralLinear N ℝ) * g) =
      Unitary.toUnits (signReflection N i) * (blockRotation N p θ * g) := by
  conv_lhs => rw [← signReflection_mul_blockRotation_mul_of_not_mem hp i hi θ]
  simp only [mul_assoc, toUnits_signReflection_mul_mul_self]

/-- **Sign reflections and block Fourier coefficients.** If `f(s_i g) = c f'(g)` for all `g`,
then `Φ_j f (s_i g) = c Φ_{∓j} f' (g)`, with `-j` if `i ∈ {p, p + 1}` and `j` otherwise. -/
theorem blockFourierCoefficient_signReflection_mul {p : ℕ} (hp : p + 1 < N) (i : Fin N)
    {f f' : Langlands.GeneralLinear N ℝ → ℂ} {c : ℂ}
    (hf : ∀ g, f (Unitary.toUnits (signReflection N i) * g) = c * f' g) (j : ℤ)
    (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p j f (Unitary.toUnits (signReflection N i) * g) =
      c * blockFourierCoefficient N p (if (i : ℕ) = p ∨ (i : ℕ) = p + 1 then -j else j) f' g := by
  split_ifs with hi
  · rw [blockFourierCoefficient_eq_coeff, blockFourierCoefficient_eq_coeff]
    have e : (fun θ => f (blockRotation N p θ * (Unitary.toUnits (signReflection N i) * g))) =
        c • fun θ => (fun θ => f' (blockRotation N p θ * g)) (-θ) := by
      funext θ
      rw [Pi.smul_apply, smul_eq_mul, blockRotation_mul_signReflection_of_mem hp i hi, hf]
    rw [e, coeff_smul, coeff_comp_neg (periodic_blockRotation_mul hp f' g)]
  · unfold blockFourierCoefficient
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext θ
    rw [blockRotation_mul_signReflection_of_not_mem hp i (by omega) θ, hf, mul_assoc]

/-- The symmetrized iterated Fourier coefficient: at every slot `s`, the sum of the
coefficients of the modes `s.j` and `-s.j`. -/
def symCoeffs : List (Slot N) → (Langlands.GeneralLinear N ℝ → ℂ) →
    Langlands.GeneralLinear N ℝ → ℂ
  | [], F => F
  | s :: rest, F => fun g => blockFourierCoefficient N s.p s.j (symCoeffs rest F) g +
      blockFourierCoefficient N s.p (-s.j) (symCoeffs rest F) g

theorem symCoeffs_signReflection_mul (i : Fin N) {F F' : Langlands.GeneralLinear N ℝ → ℂ}
    {c : ℂ} (hF : ∀ g, F (Unitary.toUnits (signReflection N i) * g) = c * F' g) :
    ∀ (L : List (Slot N)) (g : Langlands.GeneralLinear N ℝ),
      symCoeffs L F (Unitary.toUnits (signReflection N i) * g) = c * symCoeffs L F' g
  | [], g => hF g
  | s :: rest, g => by
    have ih := symCoeffs_signReflection_mul i hF rest
    simp only [symCoeffs]
    rw [blockFourierCoefficient_signReflection_mul s.hp i ih,
      blockFourierCoefficient_signReflection_mul s.hp i ih]
    split_ifs
    · rw [neg_neg, mul_add, add_comm]
    · rw [mul_add]

theorem continuous_symCoeffs {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) :
    ∀ L : List (Slot N), Continuous (symCoeffs L F)
  | [] => hF
  | s :: rest =>
    (continuous_blockFourierCoefficient s.p s.j (continuous_symCoeffs hF rest)).add
      (continuous_blockFourierCoefficient s.p (-s.j) (continuous_symCoeffs hF rest))

theorem isKFin_symCoeffs {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F)
    (hK : IsKFin F) : ∀ L : List (Slot N), IsKFin (symCoeffs L F)
  | [] => hK
  | s :: rest => by
    have h1 := isKFin_blockFourierCoefficient (continuous_symCoeffs hF rest)
      (isKFin_symCoeffs hF hK rest) s.p s.j
    have h2 := isKFin_blockFourierCoefficient (continuous_symCoeffs hF rest)
      (isKFin_symCoeffs hF hK rest) s.p (-s.j)
    exact Submodule.add_mem _ h1 h2

theorem signReal_of_pos {r : ℝ} (hr : 0 < r) : signReal r = 1 := ite_eq_left hr

theorem signReal_of_neg {r : ℝ} (hr : r < 0) : signReal r = -1 :=
  ite_eq_right (not_lt.mpr hr.le)

theorem signUnit_of_pos {x : ℝˣ} (hx : 0 < (x : ℝ)) : signUnit x = 1 := ite_eq_left hx

theorem signUnit_of_neg {x : ℝˣ} (hx : (x : ℝ) < 0) : signUnit x = -1 :=
  ite_eq_right (not_lt.mpr hx.le)

/-- Equivariance under all sign reflections gives equivariance under all diagonal sign
matrices, in the form used by the extension to the principal series. -/
theorem apply_signDiagonal_mul {χ : ℕ → ℝˣ → ℂ} (hχ : ∀ l, χ l 1 = 1)
    {φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ}
    (hφ : ∀ (i : Fin N) (κ : Matrix.unitaryGroup (Fin N) ℝ),
      φ (signReflection N i * κ) = χ i (-1) * φ κ)
    (a : Fin N → ℝˣ) (κ : Matrix.unitaryGroup (Fin N) ℝ) :
    φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
      principalSeriesCharacter ℝ N χ (fun i => signUnit (a i)) * φ κ := by
  rw [JacquetKernel.principalSeriesCharacter_sign]
  -- partial sign vectors
  set d : ℕ → Fin N → ℝ := fun m i => if (i : ℕ) < m then (a i : ℝ) else 1 with hd
  have hd0 : ∀ m i, d m i ≠ 0 := fun m i => by
    simp only [hd]
    split_ifs
    · exact (a i).ne_zero
    · exact one_ne_zero
  have key : ∀ m : ℕ, ∀ κ : Matrix.unitaryGroup (Fin N) ℝ,
      φ (signDiagonal (d m) * κ) =
        (∏ i : Fin N, if (i : ℕ) < m then χ i (signUnit (a i)) else 1) * φ κ := by
    intro m
    induction m with
    | zero =>
      intro κ
      have h1 : signDiagonal (d 0) = 1 := by
        apply Subtype.ext
        change Matrix.diagonal (fun i => signReal (d 0 i)) = 1
        rw [← Matrix.diagonal_one]
        congr 1
        funext i
        simp [hd, signReal]
      simp [h1]
    | succ m ih =>
      intro κ
      by_cases hm : m < N
      · set i0 : Fin N := ⟨m, hm⟩
        set e : Fin N → ℝ := fun i => if i = i0 then (a i0 : ℝ) else 1 with he
        have he0 : ∀ i, e i ≠ 0 := fun i => by
          simp only [he]
          split_ifs
          · exact (a i0).ne_zero
          · exact one_ne_zero
        have hsplit : d (m + 1) = fun i => d m i * e i := by
          funext i
          simp only [hd, he]
          by_cases hi : i = i0
          · subst hi
            simp [i0]
          · have : (i : ℕ) ≠ m := fun h => hi (Fin.ext h)
            by_cases hlt : (i : ℕ) < m
            · simp [hi, hlt, show (i : ℕ) < m + 1 by omega]
            · simp [hi, hlt, show ¬ (i : ℕ) < m + 1 by omega]
        have hstep : φ (signDiagonal e * κ) = χ i0 (signUnit (a i0)) * φ κ := by
          by_cases hneg : (a i0 : ℝ) < 0
          · have hs : signDiagonal e = signReflection N i0 := by
              apply Subtype.ext
              change Matrix.diagonal (fun i => signReal (e i)) =
                Matrix.diagonal fun i => if i = i0 then -1 else 1
              congr 1
              funext i
              simp only [he]
              split_ifs with h
              · exact signReal_of_neg hneg
              · exact signReal_of_pos one_pos
            have hu : signUnit (a i0) = -1 := signUnit_of_neg hneg
            rw [hs, hφ, hu]
          · have hpos : 0 < (a i0 : ℝ) :=
              lt_of_le_of_ne (not_lt.mp hneg) (a i0).ne_zero.symm
            have hs : signDiagonal e = 1 := by
              apply Subtype.ext
              change Matrix.diagonal (fun i => signReal (e i)) = 1
              rw [← Matrix.diagonal_one]
              congr 1
              funext i
              simp only [he]
              split_ifs with h
              · exact signReal_of_pos hpos
              · exact signReal_of_pos one_pos
            have hu : signUnit (a i0) = 1 := signUnit_of_pos hpos
            rw [hs, one_mul, hu, hχ, one_mul]
        have hprod : (∏ i : Fin N, if (i : ℕ) < m + 1 then χ i (signUnit (a i)) else 1) =
            ∏ i : Fin N, ((if (i : ℕ) < m then χ i (signUnit (a i)) else 1) *
              (if i = i0 then χ i (signUnit (a i)) else 1)) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          by_cases hi : (i : ℕ) = m
          · have hi' : i = i0 := Fin.ext hi
            rw [ite_eq_left (show (i : ℕ) < m + 1 by omega),
              ite_eq_right (show ¬ (i : ℕ) < m by omega), ite_eq_left hi', one_mul]
          · have hi' : i ≠ i0 := fun h => hi (by rw [h])
            rw [ite_eq_right hi', mul_one]
            by_cases hlt : (i : ℕ) < m
            · rw [ite_eq_left hlt, ite_eq_left (show (i : ℕ) < m + 1 by omega)]
            · rw [ite_eq_right hlt, ite_eq_right (show ¬ (i : ℕ) < m + 1 by omega)]
        rw [hsplit, signDiagonal_mul (fun i => hd0 m i) he0, mul_assoc, ih, hstep, ← mul_assoc,
          hprod, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i0]
        simp
      · have hdm : d (m + 1) = d m := by
          funext i
          simp only [hd]
          rw [ite_eq_left (show (i : ℕ) < m + 1 by omega), ite_eq_left (show (i : ℕ) < m by omega)]
        rw [hdm, ih]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [ite_eq_left (show (i : ℕ) < m + 1 by omega), ite_eq_left (show (i : ℕ) < m by omega)]
  have hdN : d N = fun i => (a i : ℝ) := by
    funext i
    simp only [hd]
    rw [ite_eq_left i.2]
  have := key N κ
  rw [hdN] at this
  rw [this]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ite_eq_left i.2]

end Signs

/-! ## The phase of iterated coefficients under block rotations -/

section Phase

/-- **Phase.** For pairwise disjoint slots and a slot `t` of the list,
`coeffs L F (r_{t.p}(φ) g) = e^{i t.j φ} coeffs L F g`. -/
theorem coeffs_blockRotation_mul : ∀ (L : List (Slot N)), L.Pairwise Slot.Disjoint →
    ∀ t ∈ L, ∀ (F : Langlands.GeneralLinear N ℝ → ℂ) (φ : ℝ) (g : Langlands.GeneralLinear N ℝ),
      coeffs L F (blockRotation N t.p φ * g) =
        Complex.exp ((t.j : ℂ) * (φ : ℂ) * Complex.I) * coeffs L F g
  | [], _, t, ht, _, _, _ => absurd ht List.not_mem_nil
  | s :: rest, hpw, t, ht, F, φ, g => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact blockFourierCoefficient_blockRotation_mul t.hp _ _ φ g
    · simp only [coeffs]
      unfold blockFourierCoefficient
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      have hc : blockRotation N s.p θ * (blockRotation N t.p φ * g) =
          blockRotation N t.p φ * (blockRotation N s.p θ * g) := by
        rw [← mul_assoc, blockRotation_commute (hsd t ht') θ φ, mul_assoc]
      rw [hc, coeffs_blockRotation_mul rest hrest t ht' F φ, mul_assoc]

/-- A function with the phase `e^{ijθ}` along `r_p` has no Fourier mode `m ≠ j` along `r_p`. -/
theorem blockFourierCoefficient_eq_zero_of_phase {c : Langlands.GeneralLinear N ℝ → ℂ} {p : ℕ}
    {j m : ℤ}
    (hc : ∀ (θ : ℝ) (y : Langlands.GeneralLinear N ℝ),
      c (blockRotation N p θ * y) = Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I) * c y)
    (hm : m ≠ j) (g : Langlands.GeneralLinear N ℝ) : blockFourierCoefficient N p m c g = 0 := by
  rw [blockFourierCoefficient_eq_coeff]
  have e : (fun θ => c (blockRotation N p θ * g)) = c g • expMode j := by
    funext θ
    rw [hc, Pi.smul_apply, smul_eq_mul, expMode, mul_comm]
  rw [e, coeff_smul, coeff_expMode, ite_eq_right_iff.mpr fun h => absurd h.symm hm, mul_zero]

end Phase

/-! ## Torus averages of integrals over `O(N)` -/

section Average

theorem integral_blockRotation_mul (G : Langlands.GeneralLinear N ℝ → ℂ) (p : ℕ) (θ : ℝ) :
    ∫ k : unitaryCompact ℝ N, G (blockRotation N p θ * k) ∂haarK N =
      ∫ k : unitaryCompact ℝ N, G k ∂haarK N := by
  have h := integral_mul_left_eq_self (μ := haarK N)
    (fun k : unitaryCompact ℝ N => G (k : Langlands.GeneralLinear N ℝ))
    ⟨blockRotation N p θ, blockRotation_mem_unitaryCompact N p θ⟩
  exact h

theorem exists_bound_of_continuous {G : Langlands.GeneralLinear N ℝ → ℂ} (hG : Continuous G) :
    ∃ M : ℝ, ∀ k ∈ unitaryCompact ℝ N, ‖G k‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_mul hG 1
  exact ⟨M, fun k hk => by simpa using hM k hk⟩

theorem integrable_of_continuous {G : Langlands.GeneralLinear N ℝ → ℂ} (hG : Continuous G) :
    Integrable (fun k : unitaryCompact ℝ N => G k) (haarK N) := by
  obtain ⟨M, hM⟩ := exists_bound_of_continuous hG
  exact Integrable.of_bound (hG.comp continuous_subtype_val).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun k => hM k k.2)

/-- `∫_{O(N)} Φ^p_0 G = 2π ∫_{O(N)} G`. -/
theorem integral_blockFourierCoefficient_zero {G : Langlands.GeneralLinear N ℝ → ℂ}
    (hG : Continuous G) (p : ℕ) :
    ∫ k : unitaryCompact ℝ N, blockFourierCoefficient N p 0 G k ∂haarK N =
      2 * Real.pi * ∫ k : unitaryCompact ℝ N, G k ∂haarK N := by
  have e : ∀ k : unitaryCompact ℝ N, blockFourierCoefficient N p 0 G k =
      ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), G (blockRotation N p θ * k) := by
    intro k
    unfold blockFourierCoefficient
    rw [intervalIntegral.integral_of_le (by positivity)]
    simp only [Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
  simp_rw [e]
  set F : unitaryCompact ℝ N × ℝ → ℂ := fun q => G (blockRotation N p q.2 * q.1) with hF
  have hFc : Continuous F :=
    hG.comp (((continuous_blockRotation N p).comp continuous_snd).mul
      (continuous_subtype_val.comp continuous_fst))
  obtain ⟨M, hM⟩ := exists_bound_of_continuous hG
  have hFi : Integrable F ((haarK N).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) := by
      rw [isFiniteMeasure_restrict]
      exact measure_Ioc_lt_top.ne
    exact Integrable.of_bound hFc.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun q =>
        hM _ (mul_mem (blockRotation_mem_unitaryCompact N p q.2) q.1.2))
  rw [integral_integral_swap hFi]
  simp_rw [integral_blockRotation_mul G p]
  rw [setIntegral_const, Real.volume_real_Ioc, sub_zero,
    max_eq_left (by positivity), Complex.real_smul]
  push_cast
  ring

/-- `∫_{O(N)} coeffs (zeroModes L) G = (2π)^r ∫_{O(N)} G`. -/
theorem integral_coeffs_zeroModes {G : Langlands.GeneralLinear N ℝ → ℂ} (hG : Continuous G) :
    ∀ L : List (Slot N),
      ∫ k : unitaryCompact ℝ N, coeffs (zeroModes L) G k ∂haarK N =
        (2 * Real.pi) ^ L.length * ∫ k : unitaryCompact ℝ N, G k ∂haarK N
  | [] => by simp [zeroModes, coeffs]
  | s :: rest => by
    have h := integral_blockFourierCoefficient_zero (continuous_coeffs hG (zeroModes rest)) s.p
    have ih := integral_coeffs_zeroModes hG rest
    change ∫ k : unitaryCompact ℝ N, blockFourierCoefficient N s.p 0
      (coeffs (zeroModes rest) G) k ∂haarK N = _
    rw [h, ih, List.length_cons, pow_succ]
    ring

end Average

/-! ## Orthogonality -/

section Orthogonality

theorem conj_exp_mul_I (j : ℤ) (θ : ℝ) :
    conj (Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I)) =
      Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_I]

theorem coeffs_zeroModes_mul_conj {c F : Langlands.GeneralLinear N ℝ → ℂ} :
    ∀ L : List (Slot N),
      (∀ t ∈ L, ∀ (φ : ℝ) (y : Langlands.GeneralLinear N ℝ),
        c (blockRotation N t.p φ * y) = Complex.exp ((t.j : ℂ) * (φ : ℂ) * Complex.I) * c y) →
      ∀ g : Langlands.GeneralLinear N ℝ,
        coeffs (zeroModes L) (fun y => F y * conj (c y)) g = conj (c g) * coeffs L F g
  | [], _, g => by simp [zeroModes, coeffs, mul_comm]
  | s :: rest, hc, g => by
    have ih := coeffs_zeroModes_mul_conj (c := c) (F := F) rest
      fun t ht => hc t (List.mem_cons_of_mem _ ht)
    change blockFourierCoefficient N s.p 0 (coeffs (zeroModes rest)
      (fun y => F y * conj (c y))) g = conj (c g) * blockFourierCoefficient N s.p s.j
        (coeffs rest F) g
    unfold blockFourierCoefficient
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [ih, hc s List.mem_cons_self θ g, map_mul, conj_exp_mul_I]
    simp only [Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
    ring

/-- **Orthogonality.** `∫_{O(N)} F conj(c_L F) = (2π)^{-r} ∫_{O(N)} |c_L F|²`. -/
theorem integral_mul_conj_coeffs {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F)
    {L : List (Slot N)} (hL : L.Pairwise Slot.Disjoint) :
    ∫ k : unitaryCompact ℝ N, F k * conj (coeffs L F k) ∂haarK N =
      ((2 * Real.pi : ℂ) ^ L.length)⁻¹ *
        ∫ k : unitaryCompact ℝ N, ((‖coeffs L F k‖ ^ 2 : ℝ) : ℂ) ∂haarK N := by
  have hcc : Continuous (coeffs L F) := continuous_coeffs hF L
  have hGc : Continuous fun y => F y * conj (coeffs L F y) :=
    hF.mul (Complex.continuous_conj.comp hcc)
  have h := integral_coeffs_zeroModes hGc L
  have hph : ∀ t ∈ L, ∀ (φ : ℝ) (y : Langlands.GeneralLinear N ℝ),
      coeffs L F (blockRotation N t.p φ * y) =
        Complex.exp ((t.j : ℂ) * (φ : ℂ) * Complex.I) * coeffs L F y :=
    fun t ht φ y => coeffs_blockRotation_mul L hL t ht F φ y
  simp_rw [coeffs_zeroModes_mul_conj L hph, Complex.conj_mul'] at h
  simp_rw [Complex.ofReal_pow]
  rw [h]
  have h2 : (2 * (Real.pi : ℂ)) ^ L.length ≠ 0 := pow_ne_zero _ (by
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  field_simp

end Orthogonality

/-! ## Symmetrized coefficients as sums over sign variants -/

section Variants

/-- The `2^r` sign variants of a list of slots: the modes `s.j` replaced by `±s.j`. -/
def variants : List (Slot N) → List (List (Slot N))
  | [] => [[]]
  | s :: rest => (variants rest).map (fun L => s :: L) ++
      (variants rest).map (fun L => setMode s (-s.j) :: L)

theorem mem_variants_self : ∀ L : List (Slot N), L ∈ variants L
  | [] => by simp [variants]
  | s :: rest => by
    simp only [variants, List.mem_append, List.mem_map]
    exact Or.inl ⟨rest, mem_variants_self rest, rfl⟩

/-- A sign variant has the same blocks and weights, with modes `±`. -/
theorem forall₂_of_mem_variants : ∀ {L L' : List (Slot N)}, L' ∈ variants L →
    List.Forall₂ (fun t s => t.p = s.p ∧ t.M = s.M ∧ (t.j = s.j ∨ t.j = -s.j)) L' L
  | [], L', h => by
    simp only [variants, List.mem_singleton] at h
    subst h
    exact List.Forall₂.nil
  | s :: rest, L', h => by
    simp only [variants, List.mem_append, List.mem_map] at h
    rcases h with ⟨L, hL, rfl⟩ | ⟨L, hL, rfl⟩
    · exact List.Forall₂.cons ⟨rfl, rfl, Or.inl rfl⟩ (forall₂_of_mem_variants hL)
    · exact List.Forall₂.cons ⟨rfl, rfl, Or.inr rfl⟩ (forall₂_of_mem_variants hL)

theorem exists_of_mem_of_forall₂ {P : Slot N → Slot N → Prop} :
    ∀ {L' L : List (Slot N)}, List.Forall₂ P L' L → ∀ t ∈ L', ∃ s ∈ L, P t s
  | [], [], _, t, ht => absurd ht List.not_mem_nil
  | t0 :: L', s0 :: L, h, t, ht => by
    rw [List.forall₂_cons] at h
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨s0, List.mem_cons_self, h.1⟩
    · obtain ⟨s, hs, hP⟩ := exists_of_mem_of_forall₂ h.2 t ht'
      exact ⟨s, List.mem_cons_of_mem _ hs, hP⟩

theorem pairwise_of_forall₂ {P : Slot N → Slot N → Prop} (hP : ∀ t s, P t s → t.p = s.p) :
    ∀ {L' L : List (Slot N)}, List.Forall₂ P L' L → L.Pairwise Slot.Disjoint →
      L'.Pairwise Slot.Disjoint
  | [], [], _, _ => List.Pairwise.nil
  | t :: L', s :: L, h, hL => by
    rw [List.forall₂_cons] at h
    obtain ⟨hts, h'⟩ := h
    obtain ⟨hs, hL'⟩ := List.pairwise_cons.mp hL
    refine List.Pairwise.cons ?_ (pairwise_of_forall₂ hP h' hL')
    intro t' ht'
    obtain ⟨s', hs', hP'⟩ := exists_of_mem_of_forall₂ h' t' ht'
    have e1 := hP t s hts
    have e2 := hP t' s' hP'
    have := hs s' hs'
    unfold Slot.Disjoint at this ⊢
    rw [e1, e2]
    exact this

theorem length_eq_of_forall₂ {P : Slot N → Slot N → Prop} :
    ∀ {L' L : List (Slot N)}, List.Forall₂ P L' L → L'.length = L.length :=
  fun h => h.length_eq

theorem continuous_list_sum :
    ∀ (fs : List (Langlands.GeneralLinear N ℝ → ℂ)), (∀ f ∈ fs, Continuous f) →
      Continuous fun y => (fs.map fun f => f y).sum
  | [], _ => by simpa using continuous_const
  | f :: fs, hfs => by
    simp only [List.map_cons, List.sum_cons]
    exact (hfs f List.mem_cons_self).add
      (continuous_list_sum fs fun f' h => hfs f' (List.mem_cons_of_mem _ h))

theorem blockFourierCoefficient_list_sum {p : ℕ} (j : ℤ) :
    ∀ (fs : List (Langlands.GeneralLinear N ℝ → ℂ)), (∀ f ∈ fs, Continuous f) →
      ∀ g : Langlands.GeneralLinear N ℝ,
        blockFourierCoefficient N p j (fun y => (fs.map fun f => f y).sum) g =
          (fs.map fun f => blockFourierCoefficient N p j f g).sum
  | [], _, g => by simp [blockFourierCoefficient]
  | f :: fs, hfs, g => by
    have hf := hfs f List.mem_cons_self
    have hrest : ∀ f' ∈ fs, Continuous f' := fun f' h => hfs f' (List.mem_cons_of_mem _ h)
    have hsum : Continuous fun y => (fs.map fun f => f y).sum := continuous_list_sum fs hrest
    simp only [List.map_cons, List.sum_cons]
    have e : (fun y => f y + (fs.map fun f => f y).sum) = f + fun y => (fs.map fun f => f y).sum :=
      rfl
    rw [e, RealBlockJacquet.blockFourierCoefficient_add p j hf hsum,
      blockFourierCoefficient_list_sum j fs hrest g]

/-- `symCoeffs L F = ∑_{L' ∈ variants L} coeffs L' F`. -/
theorem symCoeffs_eq_sum {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) :
    ∀ (L : List (Slot N)) (g : Langlands.GeneralLinear N ℝ),
      symCoeffs L F g = ((variants L).map fun L' => coeffs L' F g).sum
  | [], g => by simp [symCoeffs, variants, coeffs]
  | s :: rest, g => by
    have ih : symCoeffs rest F = fun y => (((variants rest).map fun L' => coeffs L' F).map
        fun f => f y).sum := by
      funext y
      rw [symCoeffs_eq_sum hF rest y, List.map_map]
      rfl
    have hc : ∀ f ∈ (variants rest).map fun L' => coeffs L' F, Continuous f := by
      intro f hf
      obtain ⟨L', -, rfl⟩ := List.mem_map.mp hf
      exact continuous_coeffs hF L'
    simp only [symCoeffs]
    rw [ih, blockFourierCoefficient_list_sum s.j _ hc g,
      blockFourierCoefficient_list_sum (-s.j) _ hc g]
    simp only [variants, List.map_append, List.map_map, List.sum_append]
    rfl

end Variants

/-! ## Vanishing of block coefficients of symmetrized coefficients -/

section Vanishing

theorem exists_of_mem_right_of_forall₂ {P : Slot N → Slot N → Prop} :
    ∀ {L' L : List (Slot N)}, List.Forall₂ P L' L → ∀ s ∈ L, ∃ t ∈ L', P t s
  | [], [], _, s, hs => absurd hs List.not_mem_nil
  | t0 :: L', s0 :: L, h, s, hs => by
    rw [List.forall₂_cons] at h
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact ⟨t0, List.mem_cons_self, h.1⟩
    · obtain ⟨t, ht, hP⟩ := exists_of_mem_right_of_forall₂ h.2 s hs'
      exact ⟨t, List.mem_cons_of_mem _ ht, hP⟩

/-- `Φ^{t.p}_j (symCoeffs L F) = 0` for a slot `t` of `L` and `j ≠ ±t.j`. -/
theorem blockFourierCoefficient_symCoeffs_eq_zero {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : Continuous F) {L : List (Slot N)} (hL : L.Pairwise Slot.Disjoint) {t : Slot N}
    (ht : t ∈ L) {j : ℤ} (hj1 : j ≠ t.j) (hj2 : j ≠ -t.j) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N t.p j (symCoeffs L F) g = 0 := by
  have e : symCoeffs L F = fun y => (((variants L).map fun L' => coeffs L' F).map
      fun f => f y).sum := by
    funext y
    rw [symCoeffs_eq_sum hF L y, List.map_map]
    rfl
  have hc : ∀ f ∈ (variants L).map fun L' => coeffs L' F, Continuous f := by
    intro f hf
    obtain ⟨L', -, rfl⟩ := List.mem_map.mp hf
    exact continuous_coeffs hF L'
  rw [e, blockFourierCoefficient_list_sum j _ hc g, List.map_map]
  refine List.sum_eq_zero fun z hz => ?_
  obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hz
  have h2 := forall₂_of_mem_variants hL'
  have hpw' : L'.Pairwise Slot.Disjoint := pairwise_of_forall₂ (fun _ _ h => h.1) h2 hL
  obtain ⟨t', ht', hp, -, hjj⟩ := exists_of_mem_right_of_forall₂ h2 t ht
  show blockFourierCoefficient N t.p j (coeffs L' F) g = 0
  rw [← hp]
  refine blockFourierCoefficient_eq_zero_of_phase
    (fun θ y => coeffs_blockRotation_mul L' hpw' t' ht' F θ y) ?_ g
  rcases hjj with h | h
  · rw [h]; exact hj1
  · rw [h]; exact hj2

/-- Block coefficients of a function equal to `conj F` on `O(N)`. -/
theorem blockFourierCoefficient_of_eq_conj {f F : Langlands.GeneralLinear N ℝ → ℂ}
    (hfF : ∀ k ∈ unitaryCompact ℝ N, f k = conj (F k)) (p : ℕ) (j : ℤ)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    blockFourierCoefficient N p j f k = conj (blockFourierCoefficient N p (-j) F k) := by
  unfold blockFourierCoefficient
  rw [← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [hfF _ (mul_mem (blockRotation_mem_unitaryCompact N p θ) hk), map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, Int.cast_neg, map_intCast]
  ring

/-- Iterated coefficients vanish on `O(N)` if one block coefficient does. -/
theorem coeffs_eq_zero_of_mem {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) :
    ∀ (L : List (Slot N)), L.Pairwise Slot.Disjoint → ∀ t ∈ L,
      (∀ k ∈ unitaryCompact ℝ N, blockFourierCoefficient N t.p t.j F k = 0) →
      ∀ k ∈ unitaryCompact ℝ N, coeffs L F k = 0
  | [], _, t, ht, _, _, _ => absurd ht List.not_mem_nil
  | s :: rest, hpw, t, ht, h0, k, hk => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    have hsd' : ∀ t' ∈ rest, s.p + 1 < t'.p ∨ t'.p + 1 < s.p := hsd
    rcases List.mem_cons.mp ht with rfl | ht'
    · show blockFourierCoefficient N t.p t.j (coeffs rest F) k = 0
      rw [blockFourierCoefficient_coeffs t.j hF rest hsd']
      exact coeffs_eq_zero_of_eqOn h0 rest k hk
    · show blockFourierCoefficient N s.p s.j (coeffs rest F) k = 0
      exact blockFourierCoefficient_eq_zero_of s.j fun θ =>
        coeffs_eq_zero_of_mem hF rest hrest t ht' h0 _
          (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk)

theorem setMode_neg_mem_withModes : ∀ {S : List (Slot N)} {J : List ℤ} {t : Slot N},
    t ∈ withModes S J → setMode t (-t.j) ∈ withModes S (J.map Neg.neg)
  | [], _, _, ht => by simp [withModes] at ht
  | _ :: _, [], _, ht => by simp [withModes] at ht
  | s :: rest, j :: J, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (setMode_neg_mem_withModes ht)

theorem exists_setMode_mem_withModes : ∀ {S : List (Slot N)} {J : List ℤ},
    J.length = S.length → ∀ s ∈ S, ∃ j : ℤ, setMode s j ∈ withModes S J
  | [], _, _, s, hs => absurd hs List.not_mem_nil
  | _ :: _, [], hJ, _, _ => by simp at hJ
  | s0 :: rest, j :: J, hJ, s, hs => by
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact ⟨j, List.mem_cons_self⟩
    · obtain ⟨j', hj'⟩ := exists_setMode_mem_withModes (S := rest) (J := J)
        (by simpa using hJ) s hs'
      exact ⟨j', List.mem_cons_of_mem _ hj'⟩

end Vanishing

/-! ## Positivity -/

section Positivity

theorem eq_zero_of_integral_norm_sq_eq_zero {G : Langlands.GeneralLinear N ℝ → ℂ}
    (hG : Continuous G) (h : ∫ k : unitaryCompact ℝ N, ‖G k‖ ^ 2 ∂haarK N = 0) :
    ∀ k ∈ unitaryCompact ℝ N, G k = 0 := by
  have hcont : Continuous fun k : unitaryCompact ℝ N => ‖G k‖ ^ 2 :=
    (continuous_norm.comp (hG.comp continuous_subtype_val)).pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg _)
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp h
  have heq := (Continuous.ae_eq_iff_eq (haarK N) hcont continuous_const).mp hae
  intro k hk
  have h0 : ‖G k‖ ^ 2 = 0 := congrFun heq ⟨k, hk⟩
  exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)

/-- The pairing of `F` with the conjugate of a sum of iterated coefficients over lists of
the same length `r` is `(2π)^{-r}` times the sum of the `L²` norms. -/
theorem integral_mul_conj_sum {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) (r : ℕ) :
    ∀ Ls : List (List (Slot N)), (∀ L ∈ Ls, L.Pairwise Slot.Disjoint ∧ L.length = r) →
      ∫ k : unitaryCompact ℝ N, F k * conj ((Ls.map fun L => coeffs L F k).sum) ∂haarK N =
        ((2 * Real.pi : ℂ) ^ r)⁻¹ *
          (((Ls.map fun L => ∫ k : unitaryCompact ℝ N, ‖coeffs L F k‖ ^ 2 ∂haarK N).sum : ℝ) : ℂ)
  | [], _ => by simp
  | L :: Ls, hLs => by
    obtain ⟨hL, hlen⟩ := hLs L List.mem_cons_self
    have ih := integral_mul_conj_sum hF r Ls fun L' h => hLs L' (List.mem_cons_of_mem _ h)
    have hc1 : Continuous fun y => F y * conj (coeffs L F y) :=
      hF.mul (Complex.continuous_conj.comp (continuous_coeffs hF L))
    have hc2 : Continuous fun y => F y * conj ((Ls.map fun L => coeffs L F y).sum) := by
      refine hF.mul (Complex.continuous_conj.comp ?_)
      have := continuous_list_sum (Ls.map fun L => coeffs L F) (by
        intro f hf
        obtain ⟨L', -, rfl⟩ := List.mem_map.mp hf
        exact continuous_coeffs hF L')
      simpa [List.map_map, Function.comp_def] using this
    simp only [List.map_cons, List.sum_cons, map_add, mul_add]
    rw [integral_add (integrable_of_continuous hc1) (integrable_of_continuous hc2), ih,
      integral_mul_conj_coeffs hF hL, hlen, integral_complex_ofReal]
    push_cast
    ring

/-- **Positivity.** If `∫_{O(N)} F conj(symCoeffs L F) = 0` then `coeffs L F = 0` on `O(N)`. -/
theorem coeffs_eq_zero_of_integral_symCoeffs {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : Continuous F) {L : List (Slot N)} (hL : L.Pairwise Slot.Disjoint)
    (h : ∫ k : unitaryCompact ℝ N, F k * conj (symCoeffs L F k) ∂haarK N = 0) :
    ∀ k ∈ unitaryCompact ℝ N, coeffs L F k = 0 := by
  have hvar : ∀ L' ∈ variants L, L'.Pairwise Slot.Disjoint ∧ L'.length = L.length := by
    intro L' hL'
    have h2 := forall₂_of_mem_variants hL'
    exact ⟨pairwise_of_forall₂ (fun _ _ h => h.1) h2 hL, h2.length_eq⟩
  have e := integral_mul_conj_sum hF L.length (variants L) hvar
  simp_rw [← symCoeffs_eq_sum hF L] at e
  rw [h] at e
  have h2 : ((2 * Real.pi : ℂ) ^ L.length)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (by
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hsum := (mul_eq_zero.mp e.symm).resolve_left h2
  rw [Complex.ofReal_eq_zero] at hsum
  have hnn : ∀ a ∈ (variants L).map fun L' => ∫ k : unitaryCompact ℝ N,
      ‖coeffs L' F k‖ ^ 2 ∂haarK N, 0 ≤ a := by
    intro a ha
    obtain ⟨L', -, rfl⟩ := List.mem_map.mp ha
    exact integral_nonneg fun k => sq_nonneg _
  have hle := List.single_le_sum hnn _ (List.mem_map_of_mem (mem_variants_self L))
  rw [hsum] at hle
  have h0 : ∫ k : unitaryCompact ℝ N, ‖coeffs L F k‖ ^ 2 ∂haarK N = 0 :=
    le_antisymm hle (integral_nonneg fun k => sq_nonneg _)
  exact eq_zero_of_integral_norm_sq_eq_zero (continuous_coeffs hF L) h0

end Positivity

/-! ## Extension of conjugates -/

section Extension

/-- A continuous `O(N)`-finite function `F` with `F(s_i g) = conj(χ_i(-1)) F(g)` has the
conjugate restriction to `O(N)` of an `O(N)`-finite function of the principal series of `χ`. -/
theorem exists_ext_conj {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (hχ : IsSignedPower χ e)
    {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) (hK : IsKFin F)
    (hs : ∀ (i : Fin N) (g : Langlands.GeneralLinear N ℝ),
      F (Unitary.toUnits (signReflection N i) * g) = conj (χ i (-1)) * F g) :
    ∃ f ∈ kFiniteFunctions (principalSeries ℝ N χ) (unitaryCompact ℝ N),
      ∀ k ∈ unitaryCompact ℝ N, f k = conj (F k) := by
  obtain ⟨P, hP⟩ := OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors hF hK 1
  set φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ := fun κ => conj (F (Unitary.toUnits κ)) with hφdef
  have hφP : ∀ κ : Matrix.unitaryGroup (Fin N) ℝ, φ κ = MvPolynomial.eval
      (fun ij => (((κ : Matrix (Fin N) (Fin N) ℝ) ij.1 ij.2 : ℝ) : ℂ))
        (MvPolynomial.map (starRingEnd ℂ) P) := by
    intro κ
    rw [hφdef]
    simp only
    rw [← one_mul (Unitary.toUnits κ), hP κ]
    exact JacquetKernel.conj_eval_ofReal P (fun ij => (κ : Matrix (Fin N) (Fin N) ℝ) ij.1 ij.2)
  have hφc : Continuous φ := Complex.continuous_conj.comp (hF.comp continuous_unitary_toUnits)
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin N) ℝ => fun x => φ (x * k))) := by
    have h := TranslateFinite.finiteDimensional_span_eval (n := N)
      (MvPolynomial.map (starRingEnd ℂ) P)
    have heq : (fun k : Matrix.unitaryGroup (Fin N) ℝ => fun x => φ (x * k)) =
        fun k x => MvPolynomial.eval (fun ij => (((x * k : Matrix.unitaryGroup (Fin N) ℝ) :
          Matrix (Fin N) (Fin N) ℝ) ij.1 ij.2 : ℂ)) (MvPolynomial.map (starRingEnd ℂ) P) :=
      funext fun k => funext fun x => hφP (x * k)
    rw [heq]
    exact h
  have hφs : ∀ (i : Fin N) (κ : Matrix.unitaryGroup (Fin N) ℝ),
      φ (signReflection N i * κ) = χ i (-1) * φ κ := by
    intro i κ
    simp only [hφdef]
    rw [map_mul, hs, map_mul, Complex.conj_conj]
  have hφM := apply_signDiagonal_mul hχ.one hφs
  have hE := extension_mem_kFiniteFunctions e hχ.eq hφc hfin hφM
  refine ⟨_, hE, fun k hk => ?_⟩
  have hk' : k = Unitary.toUnits (⟨(k : Matrix (Fin N) (Fin N) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin N) ℝ) := Units.ext rfl
  rw [hk', extension_unitary]

end Extension

/-! ## Null functions -/

section Null

/-- `v` is null along the slots `S` if all its jointly allowed iterated coefficients (modes
`|j| ≥ m` at every slot of weight `m`) vanish on `O(N)`. -/
def IsNull (S : List (Slot N)) (v : Langlands.GeneralLinear N ℝ → ℂ) : Prop :=
  ∀ J : List ℤ, J.length = S.length → (∀ t ∈ withModes S J, (t.M : ℤ) ≤ |t.j|) →
    ∀ k ∈ unitaryCompact ℝ N, coeffs (withModes S J) v k = 0

/-- **Parseval vanishing.** A null `v` pairs to zero with every continuous `x` whose window
coefficients vanish. -/
theorem integral_mul_eq_zero_of_isNull {S : List (Slot N)} (hS : S.Pairwise Slot.Disjoint)
    {v x : Langlands.GeneralLinear N ℝ → ℂ} (hv : Continuous v) (hvK : IsKFin v)
    (hx : Continuous x) (hnull : IsNull S v)
    (hwin : ∀ s ∈ S, ∀ j : ℤ, |j| < s.M → ∀ g, blockFourierCoefficient N s.p j x g = 0) :
    ∫ k : unitaryCompact ℝ N, v k * x k ∂haarK N = 0 := by
  obtain ⟨D, hD⟩ := exists_hasDegree hv hvK S
  have hpt : ∀ k ∈ unitaryCompact ℝ N, coeffs (zeroModes S) (fun y => v y * x y) k = 0 := by
    intro k hk
    have e1 : coeffs (zeroModes S) (fun y => v y * x y) k =
        coeffs (zeroModes S) (fun y => v (y * k) * x (y * k)) 1 := by
      have := coeffs_mul_right (fun y => v y * x y) k (zeroModes S) 1
      rw [one_mul] at this
      exact this
    rw [e1, coeffs_zeroModes_mul_eq_sum D S hS hv hvK hD hx k hk k]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun J hJ => ?_)
    have hlen : J.length = S.length := (mem_modeLists hJ).1
    by_cases hall : ∀ t ∈ withModes S J, (t.M : ℤ) ≤ |t.j|
    · rw [hnull J hlen hall k hk, zero_mul]
    · push Not at hall
      obtain ⟨t, ht, hlt⟩ := hall
      refine mul_eq_zero_of_right _ ?_
      obtain ⟨s, hs, j, rfl⟩ := mem_withModes ht
      have ht' := setMode_neg_mem_withModes ht
      refine coeffs_eq_zero_of_mem hx _ (pairwise_withModes _ hS) _ ht' (fun k' _ => ?_) k hk
      exact hwin s hs (-j) (by rw [abs_neg]; exact hlt) k'
  have h := integral_coeffs_zeroModes (G := fun y => v y * x y) (hv.mul hx) S
  have hz : ∫ k : unitaryCompact ℝ N, coeffs (zeroModes S)
      (fun y => v y * x y) k ∂haarK N = 0 := by
    rw [integral_congr_ae (ae_of_all _ fun k : unitaryCompact ℝ N => hpt k k.2)]
    simp
  rw [hz] at h
  have h2 : (2 * (Real.pi : ℂ)) ^ S.length ≠ 0 := pow_ne_zero _ (by
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact (mul_eq_zero.mp h.symm).resolve_left h2

end Null

/-! ## The standard module and its annihilator -/

section Standard

theorem even_of_neg_one_zpow_eq {j : ℤ} {M : ℕ} (h : (-1 : ℂ) ^ j = (-1) ^ (M + 1)) :
    Even (j + M + 1) := by
  rcases Int.even_or_odd j with hj | hj <;> rcases Nat.even_or_odd (M + 1) with hm | hm
  · obtain ⟨r, rfl⟩ := hj
    obtain ⟨q, hq⟩ := hm
    exact ⟨r + q, by omega⟩
  · rw [hj.neg_one_zpow, hm.neg_one_pow] at h
    norm_num at h
  · rw [hj.neg_one_zpow, hm.neg_one_pow] at h
    norm_num at h
  · obtain ⟨r, rfl⟩ := hj
    obtain ⟨q, hq⟩ := hm
    exact ⟨r + q + 1, by omega⟩

/-- **Windows on `O(N)`.** An `O(N)`-finite function of the principal series of the position
characters lies in the standard module as soon as its block coefficients of the modes `|j| < m`
vanish on `O(N)` at every slot of weight `m`. -/
theorem mem_kFin_standard_of_window {ds : List RealBlock} (hN : realRank ds = N)
    {x : Langlands.GeneralLinear N ℝ → ℂ}
    (hx : x ∈ kFiniteFunctions (principalSeries ℝ N (realPositionCharacter ds))
      (unitaryCompact ℝ N))
    (hwin : ∀ s ∈ slots ds N, ∀ j : ℤ, |j| < s.M → ∀ k ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N s.p j x k = 0) :
    x ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N) := by
  refine ⟨⟨hx.1, fun p d hd j hj g => ?_⟩, hx.2⟩
  have hp : p + 1 < N := hN ▸ realInducedBlockAt_lt hd
  have hs := mkSlot_mem_slots hd hp
  obtain ⟨hc1, hc2, he1, he2, -, -, -⟩ := induced_at hd
  have hps : x ∈ principalSeries ℝ N (realPositionCharacter ds) := hx.1
  rw [Int.abs_eq_natAbs d.weight] at hj
  by_cases hev : Even (j + (d.weight.natAbs : ℤ) + 1)
  · have hα := isExpEquivariant_of_mem (RealStrictCharacterLanglandsQuotient.isSignedPower ds) hps
    have hδ : shiftExp N (realPositionExponent ds) (ia hp) -
        shiftExp N (realPositionExponent ds) (ib hp) = (d.weight.natAbs : ℕ) + 1 := by
      show realPositionExponent ds p + ((N : ℂ) - 1) / 2 - (p : ℂ) -
        (realPositionExponent ds (p + 1) + ((N : ℂ) - 1) / 2 - ((p + 1 : ℕ) : ℂ)) = _
      rw [he1, he2]
      push_cast
      ring
    refine RealBlockPropagation.blockFourierCoefficient_window_eq_zero hp hps.1 hα hδ
      (fun k hk j' hj' => ?_) g j (RealBlockPropagation.mem_window.mpr ⟨hj, hev⟩)
    exact hwin _ hs j' (RealBlockPropagation.mem_window.mp hj').1 k hk
  · refine blockFourierCoefficient_eq_zero_of_parity hp
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one ds) hps ?_ g
    rw [hc1, hc2]
    have a1 : realInducedFirstCharacter d (-1) = (-1) ^ (d.weight.natAbs + 1) := by
      simp [realInducedFirstCharacter]
    have a2 : realInducedSecondCharacter d (-1) = 1 := by
      simp [realInducedSecondCharacter]
    rw [a1, a2, mul_one]
    exact fun h => hev (even_of_neg_one_zpow_eq h)

/-- If `f = conj (symCoeffs L F)` on `O(N)` and `t ∈ L`, then `Φ^{t.p}_j f = 0` on `O(N)` for
`|j| ≠ |t.j|`. -/
theorem blockFourierCoefficient_conj_symCoeffs_eq_zero {F f : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : Continuous F) {L : List (Slot N)} (hL : L.Pairwise Slot.Disjoint)
    (hfF : ∀ k ∈ unitaryCompact ℝ N, f k = conj (symCoeffs L F k)) {t : Slot N} (ht : t ∈ L)
    {j : ℤ} (hj : |j| ≠ |t.j|) {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    blockFourierCoefficient N t.p j f k = 0 := by
  rw [blockFourierCoefficient_of_eq_conj hfF t.p j hk,
    blockFourierCoefficient_symCoeffs_eq_zero hF hL ht ?_ ?_ k, map_zero]
  · intro h
    rw [← h, abs_neg] at hj
    exact hj rfl
  · intro h
    rw [neg_inj] at h
    rw [h] at hj
    exact hj rfl

/-- **Annihilators are null.** An `O(N)`-finite `v` of the principal series of the inverse
characters with `∫_{O(N)} v x = 0` for every `O(N)`-finite `x` of the standard module is null. -/
theorem isNull_of_annihilates {ds : List RealBlock} (hN : realRank ds = N)
    {v : Langlands.GeneralLinear N ℝ → ℂ}
    (hv : v ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ N))
    (hann : ∀ x ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N),
      ∫ k : unitaryCompact ℝ N, v k * x k ∂haarK N = 0) :
    IsNull (slots ds N) v := by
  intro J hJ hall
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  have hS := pairwise_slots ds N
  set L := withModes (slots ds N) J with hLdef
  have hL : L.Pairwise Slot.Disjoint := pairwise_withModes J hS
  have hvc : Continuous v := hv.1.1.continuous
  have hvs : ∀ (i : Fin N) (g : Langlands.GeneralLinear N ℝ),
      symCoeffs L v (Unitary.toUnits (signReflection N i) * g) =
        conj (realPositionCharacter ds i (-1)) * symCoeffs L v g := by
    intro i g
    refine symCoeffs_signReflection_mul i (fun g' => ?_) L g
    rw [apply_signReflection_mul hχ.dual.one hv.1 i g', dualChar,
      JacquetKernel.conj_eq_inv_of_norm_eq_one (hχ.norm_neg_one i)]
  obtain ⟨f, hf, hfP⟩ := exists_ext_conj hχ (continuous_symCoeffs hvc L)
    (isKFin_symCoeffs hvc hv.2 L) hvs
  have hfX : f ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N) := by
    refine mem_kFin_standard_of_window hN hf fun s hs j hj k hk => ?_
    obtain ⟨j', hj'⟩ := exists_setMode_mem_withModes hJ s hs
    have hM := hall _ hj'
    exact blockFourierCoefficient_conj_symCoeffs_eq_zero hvc hL hfP hj'
      (lt_of_lt_of_le hj hM).ne hk
  have h0 := hann f hfX
  have h1 : ∫ k : unitaryCompact ℝ N, v k * conj (symCoeffs L v k) ∂haarK N = 0 := by
    rw [← h0]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only
    rw [hfP k k.2]
  exact coeffs_eq_zero_of_integral_symCoeffs hvc hL h1

/-- **The double annihilator.** An `O(N)`-finite `x` of the principal series of the position
characters with `∫_{O(N)} v x = 0` for every null `O(N)`-finite `v` of the principal series of
the inverse characters lies in the standard module. -/
theorem mem_kFin_standard_of_annihilates {ds : List RealBlock} (hN : realRank ds = N)
    {x : Langlands.GeneralLinear N ℝ → ℂ}
    (hx : x ∈ kFiniteFunctions (principalSeries ℝ N (realPositionCharacter ds))
      (unitaryCompact ℝ N))
    (hann : ∀ v ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ N), IsNull (slots ds N) v →
        ∫ k : unitaryCompact ℝ N, v k * x k ∂haarK N = 0) :
    x ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N) := by
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  have hS := pairwise_slots ds N
  have hxc : Continuous x := hx.1.1.continuous
  refine mem_kFin_standard_of_window hN hx fun s hs m hm k hk => ?_
  set L : List (Slot N) := [setMode s m] with hLdef
  have hL : L.Pairwise Slot.Disjoint := List.pairwise_singleton _ _
  have hxs : ∀ (i : Fin N) (g : Langlands.GeneralLinear N ℝ),
      symCoeffs L x (Unitary.toUnits (signReflection N i) * g) =
        conj (dualChar (realPositionCharacter ds) i (-1)) * symCoeffs L x g := by
    intro i g
    refine symCoeffs_signReflection_mul i (fun g' => ?_) L g
    rw [apply_signReflection_mul hχ.one hx.1 i g',
      JacquetKernel.conj_eq_inv_of_norm_eq_one (hχ.dual.norm_neg_one i), dualChar, inv_inv]
  obtain ⟨v, hv, hvP⟩ := exists_ext_conj hχ.dual (continuous_symCoeffs hxc L)
    (isKFin_symCoeffs hxc hx.2 L) hxs
  have hvc : Continuous v := hv.1.1.continuous
  have hnull : IsNull (slots ds N) v := by
    intro J hJ hall k' hk'
    obtain ⟨j', hj'⟩ := exists_setMode_mem_withModes hJ s hs
    have hM := hall _ hj'
    refine coeffs_eq_zero_of_mem hvc _ (pairwise_withModes J hS) _ hj' (fun k'' hk'' => ?_) k' hk'
    exact blockFourierCoefficient_conj_symCoeffs_eq_zero hxc hL hvP (List.mem_singleton_self _)
      (lt_of_lt_of_le hm hM).ne' hk''
  have h0 := hann v hv hnull
  have h1 : ∫ k : unitaryCompact ℝ N, x k * conj (symCoeffs L x k) ∂haarK N = 0 := by
    rw [← h0]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only
    rw [hvP k k.2, mul_comm]
  exact coeffs_eq_zero_of_integral_symCoeffs hxc hL h1 k hk

/-- Functions of the standard module have vanishing window coefficients at every slot. -/
theorem window_of_mem_standard {ds : List RealBlock} {x : Langlands.GeneralLinear N ℝ → ℂ}
    (hx : x ∈ realStandardModule N ds) :
    ∀ s ∈ slots ds N, ∀ j : ℤ, |j| < s.M → ∀ g, blockFourierCoefficient N s.p j x g = 0 := by
  intro s hs j hj g
  obtain ⟨p, hp, d, hd, rfl⟩ := mem_slots hs
  refine hx.2 p d hd j ?_ g
  rw [Int.abs_eq_natAbs d.weight]
  exact hj

/-- Null functions annihilate the standard module. -/
theorem integral_mul_eq_zero_of_mem_standard {ds : List RealBlock}
    {v x : Langlands.GeneralLinear N ℝ → ℂ}
    (hv : v ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ N))
    (hnull : IsNull (slots ds N) v)
    (hx : x ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)) :
    ∫ k : unitaryCompact ℝ N, v k * x k ∂haarK N = 0 :=
  integral_mul_eq_zero_of_isNull (pairwise_slots ds N) hv.1.1.continuous hv.2
    hx.1.1.1.continuous hnull (window_of_mem_standard hx.1)

end Standard

end RealLeviModes

open RealPrincipalSeriesDuality RealInducedStandardBound PartialJacquet in
attribute [local instance] measurableSpaceK in
/-- **Torus modes and the annihilator of a real standard module.** Let `ds` be a list of real
blocks of rank `N`, `χ` its position characters and `X` its standard module. For an
`O(N)`-finite function `v` of the principal series of the inverse characters `χ⁻¹`,
`∫_{O(N)} v x = 0` for every `O(N)`-finite `x ∈ X` if and only if `v` is null along the slots of
the induction blocks of `ds` (all iterated block Fourier coefficients of `v` whose mode `j`
satisfies `|j| ≥ m` at every slot of weight `m` vanish on `O(N)`). An `O(N)`-finite function `x`
of the principal series of `χ` lies in `X` if and only if `∫_{O(N)} v x = 0` for every null
`O(N)`-finite `v` of the principal series of `χ⁻¹`. -/
def RealLeviModesStatement : Prop :=
  ∀ (N : ℕ) (ds : List RealBlock), realRank ds = N →
    (∀ v ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ N),
      (∀ x ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N),
        ∫ k : unitaryCompact ℝ N, v k * x k ∂haarK N = 0) ↔
        RealLeviModes.IsNull (slots ds N) v) ∧
    (∀ x ∈ kFiniteFunctions (principalSeries ℝ N (realPositionCharacter ds)) (unitaryCompact ℝ N),
      (∀ v ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
          (unitaryCompact ℝ N), RealLeviModes.IsNull (slots ds N) v →
        ∫ k : unitaryCompact ℝ N, v k * x k ∂haarK N = 0) ↔
        x ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N))

theorem realLeviModes : RealLeviModesStatement := fun _ _ hN =>
  ⟨fun _ hv => ⟨RealLeviModes.isNull_of_annihilates hN hv,
      fun hnull _ hx => RealLeviModes.integral_mul_eq_zero_of_mem_standard hv hnull hx⟩,
    fun _ hx => ⟨RealLeviModes.mem_kFin_standard_of_annihilates hN hx,
      fun hX _ hv hnull => RealLeviModes.integral_mul_eq_zero_of_mem_standard hv hnull hX⟩⟩

end Langlands.Archimedean
