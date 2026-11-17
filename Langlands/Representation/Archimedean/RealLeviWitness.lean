import Langlands.Representation.Archimedean.RealLeviNonvanishing

/-!
# A witness for the nonvanishing of the pairing along a standard parabolic subgroup

Let `ds = dss_0 ++ ⋯ ++ dss_{c-1}` satisfy the exponent conditions of the limit argument along
the standard parabolic subgroup `Q` with blocks of sizes `sz_i = rank dss_i`, and let every
class standard module (of the twisted class list `cl_i`) be irreducible. This module produces
`O(sz_i)`-finite vectors `φ_i` of the principal series of the inverse characters of `cl_i` and an
`O(N)`-finite vector `h_0` of the standard module of `ds` such that the pairing `Θ(u, h_0)` of
`RealLeviPairing` is nonzero for every `u` whose jointly allowed iterated coefficients at the
points `diag(κ)` are the products of those of the `φ_i` (`RealLeviWitnessStatement`).

On the way it proves that the `O(N)`-finite standard module of every list of real blocks
contains a vector `x` with `x(1) ≠ 0` (`exists_std_ne_zero`): on `O(N)`, `x` is the polynomial
`∏_l fac_l` in the matrix entries, with `fac_l = (k_{ll} + i k_{l+1,l})^{m+1} +
(k_{ll} - i k_{l+1,l})^{m+1}` at the first position `l` of an induction block of weight `m`,
`fac_l = k_{ll}` at a position with `χ_l(-1) = -1` outside the induction blocks, and `fac_l = 1`
otherwise.
-/

noncomputable section

open MeasureTheory Matrix ComplexConjugate

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealLeviWitness

open RealInducedBlockBound RealInducedTorusCore RealLeviChart GramFormula RealLeviTorus
  RealLeviLimit RealPrincipalSeriesDuality PartialJacquet RealInducedStandardBound
  RealStrictCharacterLanglandsQuotient RealLeviModes RealLeviPairing RealBlockFourierFinite
  PrincipalSeriesExtension

attribute [local instance] measurableSpaceK

local instance borelSpaceK_lw (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

attribute [local instance] RealBlockLimit.secondCountableTopology_unitaryCompact

/-! ## A nonzero vector of the standard module -/

section Nontrivial

variable {N : ℕ}

/-- The entry `k_{ab}` of a matrix, `0` outside the range. -/
def entC (k : Matrix (Fin N) (Fin N) ℝ) (a b : ℕ) : ℂ :=
  if h : a < N ∧ b < N then ((k ⟨a, h.1⟩ ⟨b, h.2⟩ : ℝ) : ℂ) else 0

/-- The coordinate polynomial of the entry `(a, b)`, `0` outside the range. -/
def entP (N : ℕ) (a b : ℕ) : MvPolynomial (Fin N × Fin N) ℂ :=
  if h : a < N ∧ b < N then MvPolynomial.X (⟨a, h.1⟩, ⟨b, h.2⟩) else 0

theorem eval_entP (k : Matrix (Fin N) (Fin N) ℝ) (a b : ℕ) :
    MvPolynomial.eval (fun ij => ((k ij.1 ij.2 : ℝ) : ℂ)) (entP N a b) = entC k a b := by
  unfold entP entC
  split_ifs <;> simp

/-- The factor of the position `l`. -/
def fac (ds : List RealBlock) (l : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) : ℂ :=
  match realInducedBlockAt ds l with
  | some d => (entC k l l + Complex.I * entC k (l + 1) l) ^ (d.weight.natAbs + 1) +
      (entC k l l - Complex.I * entC k (l + 1) l) ^ (d.weight.natAbs + 1)
  | none => if realPositionCharacter ds l (-1) = 1 then 1 else entC k l l

/-- The factor of the position `l` as a polynomial in the matrix entries. -/
def facP (N : ℕ) (ds : List RealBlock) (l : ℕ) : MvPolynomial (Fin N × Fin N) ℂ :=
  match realInducedBlockAt ds l with
  | some d => (entP N l l + MvPolynomial.C Complex.I * entP N (l + 1) l) ^ (d.weight.natAbs + 1) +
      (entP N l l - MvPolynomial.C Complex.I * entP N (l + 1) l) ^ (d.weight.natAbs + 1)
  | none => if realPositionCharacter ds l (-1) = 1 then 1 else entP N l l

theorem eval_facP (ds : List RealBlock) (l : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) :
    MvPolynomial.eval (fun ij => ((k ij.1 ij.2 : ℝ) : ℂ)) (facP N ds l) = fac ds l k := by
  rcases hd : realInducedBlockAt ds l with _ | d
  · simp only [fac, facP, hd]
    split_ifs <;> simp [eval_entP]
  · simp [fac, facP, hd, eval_entP]

/-- The product of the factors. -/
def phiM (ds : List RealBlock) (k : Matrix (Fin N) (Fin N) ℝ) : ℂ :=
  ∏ l : Fin N, fac ds (l : ℕ) k

/-- The product of the factors as a polynomial in the matrix entries. -/
def phiP (N : ℕ) (ds : List RealBlock) : MvPolynomial (Fin N × Fin N) ℂ :=
  ∏ l : Fin N, facP N ds (l : ℕ)

theorem eval_phiP (ds : List RealBlock) (k : Matrix (Fin N) (Fin N) ℝ) :
    MvPolynomial.eval (fun ij => ((k ij.1 ij.2 : ℝ) : ℂ)) (phiP N ds) = phiM ds k := by
  unfold phiP phiM
  rw [map_prod]
  exact Finset.prod_congr rfl fun l _ => eval_facP ds l k

/-! ### Sign reflections -/

theorem entC_sign (i : Fin N) (k : Matrix (Fin N) (Fin N) ℝ) (a b : ℕ) :
    entC (Matrix.diagonal (fun i' => if i' = i then (-1 : ℝ) else 1) * k) a b =
      (if a = (i : ℕ) then -1 else 1) * entC k a b := by
  unfold entC
  by_cases h1 : a < N ∧ b < N
  · simp only [h1, and_self, dite_true, Matrix.diagonal_mul]
    by_cases h2 : a = (i : ℕ)
    · have h3 : (⟨a, h1.1⟩ : Fin N) = i := Fin.ext h2
      simp only [h2, ite_true]
      push_cast
      ring
    · have h3 : (⟨a, h1.1⟩ : Fin N) ≠ i := fun h => h2 (congrArg Fin.val h)
      simp only [h3, h2, ite_false]
      push_cast
      ring
  · simp only [h1, dite_false, mul_zero]

theorem neg_one_pow_mul_add (A B : ℂ) (m : ℕ) :
    (-B) ^ m + (-A) ^ m = (-1) ^ m * (A ^ m + B ^ m) := by
  rw [neg_pow, neg_pow]
  ring

theorem fac_sign (ds : List RealBlock) (l : ℕ) (i : Fin N) (k : Matrix (Fin N) (Fin N) ℝ) :
    fac ds l (Matrix.diagonal (fun i' => if i' = i then (-1 : ℝ) else 1) * k) =
      (if (i : ℕ) = l then realPositionCharacter ds l (-1) else 1) * fac ds l k := by
  rcases hd : realInducedBlockAt ds l with _ | d
  · simp only [fac, hd, entC_sign]
    by_cases hχ : realPositionCharacter ds l (-1) = 1
    · simp [hχ]
    · rcases realPositionCharacter_neg_one ds l with h | h
      · exact absurd h hχ
      · by_cases hil : (i : ℕ) = l
        · subst hil
          simp only [hχ, ite_false, ite_true]
          rw [h]
        · have hli : ¬ l = (i : ℕ) := fun h' => hil h'.symm
          simp only [hχ, hil, hli, ite_false, one_mul]
  · simp only [fac, hd, entC_sign]
    obtain ⟨hc1, -⟩ := induced_at hd
    set m := d.weight.natAbs + 1 with hm
    set a := entC k l l
    set b := entC k (l + 1) l
    by_cases hil : (i : ℕ) = l
    · have h2 : ¬ (l + 1 = (i : ℕ)) := by omega
      have h3 : l = (i : ℕ) := hil.symm
      have a1 : realPositionCharacter ds l (-1) = (-1) ^ m := by
        rw [hc1]
        simp [realInducedFirstCharacter, hm]
      rw [ite_eq_left_of_eq_true _ _ (eq_true h3), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_left_of_eq_true _ _ (eq_true hil), a1]
      have e1 : -1 * a + Complex.I * (1 * b) = -(a - Complex.I * b) := by ring
      have e2 : -1 * a - Complex.I * (1 * b) = -(a + Complex.I * b) := by ring
      rw [e1, e2, neg_one_pow_mul_add]
    · by_cases hil' : (i : ℕ) = l + 1
      · have h2 : ¬ l = (i : ℕ) := by omega
        have h3 : l + 1 = (i : ℕ) := hil'.symm
        rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_left_of_eq_true _ _ (eq_true h3),
          ite_eq_right_of_eq_false _ _ (eq_false hil), one_mul]
        have e1 : a + Complex.I * (-1 * b) = a - Complex.I * b := by ring
        have e2 : a - Complex.I * (-1 * b) = a + Complex.I * b := by ring
        rw [e1, e2]
        ring
      · have h2 : ¬ l = (i : ℕ) := fun h => hil h.symm
        have h3 : ¬ l + 1 = (i : ℕ) := fun h => hil' h.symm
        simp only [h2, h3, hil, ite_false, one_mul]

theorem phiM_sign (ds : List RealBlock) (i : Fin N) (k : Matrix (Fin N) (Fin N) ℝ) :
    phiM ds (Matrix.diagonal (fun i' => if i' = i then (-1 : ℝ) else 1) * k) =
      realPositionCharacter ds i (-1) * phiM ds k := by
  unfold phiM
  simp_rw [fac_sign ds _ i k]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    have : ¬ (i : ℕ) = (l : ℕ) := fun h => hl (Fin.ext h).symm
    simp [this]
  · simp

/-! ### Rotations -/

theorem entC_rot {p : ℕ} (hp : p + 1 < N) (θ : ℝ) (k : Matrix (Fin N) (Fin N) ℝ) (a b : ℕ) :
    entC ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * k) a b =
      if a = p then (Real.cos θ : ℂ) * entC k p b - (Real.sin θ : ℂ) * entC k (p + 1) b
      else if a = p + 1 then (Real.sin θ : ℂ) * entC k p b + (Real.cos θ : ℂ) * entC k (p + 1) b
      else entC k a b := by
  unfold entC
  by_cases hb : b < N
  · by_cases ha : a < N
    · have h1 : a < N ∧ b < N := ⟨ha, hb⟩
      have hp1 : p < N ∧ b < N := ⟨by omega, hb⟩
      have hp2 : p + 1 < N ∧ b < N := ⟨hp, hb⟩
      simp only [h1, hp1, hp2, and_self, dite_true]
      rw [RealBlockDerivative.blockRotation_mul_apply hp]
      split_ifs <;> simp [RealBlockRotation.ia, RealBlockRotation.ib]
    · have h1 : ¬ (a < N ∧ b < N) := fun h => ha h.1
      have hap : ¬ a = p := by omega
      have hap' : ¬ a = p + 1 := by omega
      simp only [h1, hap, hap', dite_false, ite_false]
  · have h1 : ∀ a', ¬ (a' < N ∧ b < N) := fun a' h => hb h.2
    simp only [h1, dite_false, mul_zero, sub_zero, add_zero, ite_self]

theorem exp_pow_eq_expMode (θ : ℝ) (m : ℕ) :
    Complex.exp ((θ : ℂ) * Complex.I) ^ m = expMode (m : ℤ) θ := by
  rw [← Complex.exp_nat_mul, expMode]
  congr 1
  push_cast
  ring

theorem exp_neg_pow_eq_expMode (θ : ℝ) (m : ℕ) :
    Complex.exp (-((θ : ℂ) * Complex.I)) ^ m = expMode (-(m : ℤ)) θ := by
  rw [← Complex.exp_nat_mul, expMode]
  congr 1
  push_cast
  ring

/-- The factor of the first position of an induction block along the rotations of the block. -/
theorem fac_rot_self {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds p = some d) (hp : p + 1 < N) (θ : ℝ)
    (k : Matrix (Fin N) (Fin N) ℝ) :
    fac ds p ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * k) =
      expMode ((d.weight.natAbs + 1 : ℕ) : ℤ) θ *
          (entC k p p + Complex.I * entC k (p + 1) p) ^ (d.weight.natAbs + 1) +
        expMode (-((d.weight.natAbs + 1 : ℕ) : ℤ)) θ *
          (entC k p p - Complex.I * entC k (p + 1) p) ^ (d.weight.natAbs + 1) := by
  simp only [fac, hd, entC_rot hp, ite_true]
  have hne : ¬ p + 1 = p := by omega
  simp only [hne, ite_false]
  set a := entC k p p
  set b := entC k (p + 1) p
  have eA : (Real.cos θ : ℂ) * a - (Real.sin θ : ℂ) * b +
      Complex.I * ((Real.sin θ : ℂ) * a + (Real.cos θ : ℂ) * b) =
        Complex.exp ((θ : ℂ) * Complex.I) * (a + Complex.I * b) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination (-((Real.sin θ : ℂ) * b)) * Complex.I_sq
  have eB : (Real.cos θ : ℂ) * a - (Real.sin θ : ℂ) * b -
      Complex.I * ((Real.sin θ : ℂ) * a + (Real.cos θ : ℂ) * b) =
        Complex.exp (-((θ : ℂ) * Complex.I)) * (a - Complex.I * b) := by
    have : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg, Complex.ofReal_neg]
    linear_combination (-((Real.sin θ : ℂ) * b)) * Complex.I_sq
  rw [eA, eB, mul_pow, mul_pow, exp_pow_eq_expMode, exp_neg_pow_eq_expMode]

/-- The other factors are invariant under the rotations of an induction block. -/
theorem fac_rot_ne {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds p = some d) (hp : p + 1 < N) (θ : ℝ)
    (k : Matrix (Fin N) (Fin N) ℝ) {l : ℕ} (hl : l ≠ p) :
    fac ds l ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * k) = fac ds l k := by
  obtain ⟨-, hc2, -, -, -, -, hnone⟩ := induced_at hd
  rcases hd' : realInducedBlockAt ds l with _ | d'
  · simp only [fac, hd']
    by_cases hχ : realPositionCharacter ds l (-1) = 1
    · simp only [hχ, ite_true]
    · have hl1 : l ≠ p + 1 := by
        rintro rfl
        apply hχ
        rw [hc2]
        simp [realInducedSecondCharacter]
      simp only [hχ, ite_false, entC_rot hp, hl, hl1]
  · have hl1 : l ≠ p + 1 := by
      rintro rfl
      rw [hnone] at hd'
      cases hd'
    have hl2 : l + 1 ≠ p := by
      rintro rfl
      rw [(induced_at hd').2.2.2.2.2.2] at hd
      cases hd
    have hl3 : l + 1 ≠ p + 1 := by omega
    simp only [fac, hd', entC_rot hp, hl, hl1, hl2, hl3, ite_false]

/-- Along the rotations of an induction block of weight `m`, the product of the factors has only
the Fourier modes `±(m + 1)`. -/
theorem phiM_rot {ds : List RealBlock} {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt ds p = some d) (hp : p + 1 < N)
    (k : Matrix (Fin N) (Fin N) ℝ) :
    ∃ A B : ℂ, ∀ θ : ℝ, phiM ds ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * k) =
      A * expMode ((d.weight.natAbs + 1 : ℕ) : ℤ) θ +
        B * expMode (-((d.weight.natAbs + 1 : ℕ) : ℤ)) θ := by
  set i0 : Fin N := ⟨p, by omega⟩
  set C := ∏ l ∈ Finset.univ.erase i0, fac ds (l : ℕ) k
  refine ⟨(entC k p p + Complex.I * entC k (p + 1) p) ^ (d.weight.natAbs + 1) * C,
    (entC k p p - Complex.I * entC k (p + 1) p) ^ (d.weight.natAbs + 1) * C, fun θ => ?_⟩
  unfold phiM
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
  have hC : ∏ l ∈ Finset.univ.erase i0,
      fac ds (l : ℕ) ((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * k) = C := by
    refine Finset.prod_congr rfl fun l hl => fac_rot_ne hd hp θ k ?_
    intro h
    exact Finset.ne_of_mem_erase hl (Fin.ext h)
  rw [hC]
  show fac ds p _ * C = _
  rw [fac_rot_self hd hp θ k]
  ring

/-! ### The vector -/

theorem entC_one_self {l : ℕ} (hl : l < N) : entC (1 : Matrix (Fin N) (Fin N) ℝ) l l = 1 := by
  unfold entC
  simp [hl]

theorem entC_one_succ (l : ℕ) : entC (1 : Matrix (Fin N) (Fin N) ℝ) (l + 1) l = 0 := by
  unfold entC
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    · simp
    · intro h'
      have := congrArg Fin.val h'
      simp at this
  · rfl

theorem fac_one_ne_zero (ds : List RealBlock) {l : ℕ} (hl : l < N) :
    fac ds l (1 : Matrix (Fin N) (Fin N) ℝ) ≠ 0 := by
  rcases hd : realInducedBlockAt ds l with _ | d
  · simp only [fac, hd]
    split_ifs
    · exact one_ne_zero
    · rw [entC_one_self hl]
      exact one_ne_zero
  · simp only [fac, hd, entC_one_self hl, entC_one_succ, mul_zero, add_zero, sub_zero, one_pow]
    norm_num

theorem phiM_one_ne_zero (ds : List RealBlock) : phiM ds (1 : Matrix (Fin N) (Fin N) ℝ) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun l _ => fac_one_ne_zero ds l.2

/-- **The standard module is nonzero.** The `O(N)`-finite standard module of every list of real
blocks of rank `N` contains a vector `x` with `x(1) ≠ 0`. -/
theorem exists_std_ne_zero {ds : List RealBlock} (hN : realRank ds = N) :
    ∃ x ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N), x 1 ≠ 0 := by
  have hχ := isSignedPower ds
  let φ : Matrix.unitaryGroup (Fin N) ℝ → ℂ := fun κ => MvPolynomial.eval
    (fun ij => (((κ : Matrix (Fin N) (Fin N) ℝ) ij.1 ij.2 : ℝ) : ℂ)) (phiP N ds)
  have hφval : ∀ κ, φ κ = phiM ds (κ : Matrix (Fin N) (Fin N) ℝ) := fun κ => eval_phiP ds _
  have hφc : Continuous φ :=
    (MvPolynomial.continuous_eval (phiP N ds)).comp (continuous_pi fun ij =>
      Complex.continuous_ofReal.comp
        ((continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_subtype_val)))
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin N) ℝ => fun x => φ (x * k))) :=
    TranslateFinite.finiteDimensional_span_eval (n := N) (phiP N ds)
  have hφs : ∀ (i : Fin N) (κ : Matrix.unitaryGroup (Fin N) ℝ),
      φ (signReflection N i * κ) = realPositionCharacter ds i (-1) * φ κ := by
    intro i κ
    have e : ((signReflection N i * κ : Matrix.unitaryGroup (Fin N) ℝ) :
        Matrix (Fin N) (Fin N) ℝ) =
        Matrix.diagonal (fun i' => if i' = i then (-1 : ℝ) else 1) *
          (κ : Matrix (Fin N) (Fin N) ℝ) := rfl
    rw [hφval, hφval, e, phiM_sign]
  have hφM := apply_signDiagonal_mul hχ.one hφs
  have hE := extension_mem_kFiniteFunctions (realPositionExponent ds) hχ.eq hφc hfin hφM
  set x := extension (shiftedExponent N (realPositionExponent ds)) φ with hxdef
  have hxK : ∀ g ∈ unitaryCompact ℝ N, x g = phiM ds (g : Matrix (Fin N) (Fin N) ℝ) := by
    intro g hg
    have hgu : g = Unitary.toUnits (⟨(g : Matrix (Fin N) (Fin N) ℝ), hg⟩ :
        Matrix.unitaryGroup (Fin N) ℝ) := Units.ext rfl
    rw [hgu, hxdef, extension_unitary, hφval]
    rfl
  refine ⟨x, mem_kFin_standard_of_window hN hE fun s hs j hj k hk => ?_, ?_⟩
  · obtain ⟨p, hp, d, hd, rfl⟩ := mem_slots hs
    change |j| < (d.weight.natAbs : ℤ) at hj
    change blockFourierCoefficient N p j x k = 0
    obtain ⟨A, B, hAB⟩ := phiM_rot hd hp (k : Matrix (Fin N) (Fin N) ℝ)
    have e : (fun θ : ℝ => x (blockRotation N p θ * k)) =
        A • expMode ((d.weight.natAbs + 1 : ℕ) : ℤ) +
          B • expMode (-((d.weight.natAbs + 1 : ℕ) : ℤ)) := by
      funext θ
      rw [hxK _ (Subgroup.mul_mem _ (blockRotation_mem_unitaryCompact N p θ) hk), Units.val_mul,
        hAB θ]
      rfl
    rw [blockFourierCoefficient_eq_coeff, e,
      coeff_add ((continuous_expMode _).const_smul A) ((continuous_expMode _).const_smul B),
      coeff_smul, coeff_smul, coeff_expMode, coeff_expMode]
    have h1 : ¬ (((d.weight.natAbs + 1 : ℕ) : ℤ) = j) := by
      intro h
      rw [← h] at hj
      push_cast at hj
      rw [abs_of_nonneg (by positivity)] at hj
      omega
    have h2 : ¬ (-((d.weight.natAbs + 1 : ℕ) : ℤ) = j) := by
      intro h
      rw [← h] at hj
      push_cast at hj
      rw [abs_neg, abs_of_nonneg (by positivity)] at hj
      omega
    simp only [h1, h2, ite_false, mul_zero, add_zero]
  · rw [hxK 1 (one_mem _), Units.val_one]
    exact phiM_one_ne_zero ds

end Nontrivial

/-! ## Vectors of the dual principal series which are not null -/

section NonNull

variable {N : ℕ}

/-- The `O(N)`-finite principal series of the inverse position characters contains a vector
which is not null along the slots: some jointly allowed iterated coefficient is nonzero at a point
of `O(N)`. -/
theorem exists_nonNull {ds : List RealBlock} (hN : realRank ds = N) :
    ∃ φ ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ N),
      ∃ J : List ℤ, J.length = (slots ds N).length ∧
        (∀ t ∈ withModes (slots ds N) J, (t.M : ℤ) ≤ |t.j|) ∧
        ∃ k ∈ unitaryCompact ℝ N, coeffs (withModes (slots ds N) J) φ k ≠ 0 := by
  obtain ⟨x, hx, hx1⟩ := exists_std_ne_zero hN
  have hχ := isSignedPower ds
  have hxc : Continuous x := hx.1.1.1.continuous
  have hs : ∀ (i : Fin N) (g : Langlands.GeneralLinear N ℝ),
      x (Unitary.toUnits (signReflection N i) * g) =
        conj (dualChar (realPositionCharacter ds) i (-1)) * x g := by
    intro i g
    rw [apply_signReflection_mul hχ.one hx.1.1 i g,
      JacquetKernel.conj_eq_inv_of_norm_eq_one (hχ.dual.norm_neg_one i), dualChar, inv_inv]
  obtain ⟨φ, hφ, hφx⟩ := exists_ext_conj hχ.dual hxc hx.2 hs
  refine ⟨φ, hφ, ?_⟩
  by_contra hcon
  have hnull : IsNull (slots ds N) φ := by
    intro J hJ hall k hk
    by_contra hne
    exact hcon ⟨J, hJ, hall, k, hk, hne⟩
  have h0 := integral_mul_eq_zero_of_mem_standard hφ hnull hx
  have e : ∫ k : unitaryCompact ℝ N, φ k * x k ∂haarK N =
      ((∫ k : unitaryCompact ℝ N, ‖x k‖ ^ 2 ∂haarK N : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    show φ k * x k = ((‖x k‖ ^ 2 : ℝ) : ℂ)
    rw [hφx k k.2, Complex.conj_mul', Complex.ofReal_pow]
  rw [e, Complex.ofReal_eq_zero] at h0
  exact hx1 (eq_zero_of_integral_norm_sq_eq_zero hxc h0 1 (one_mem _))

end NonNull

/-! ## Sums of iterated coefficients -/

section Sums

variable {N : ℕ}

theorem ofReal_list_sum {ι : Type*} (f : ι → ℝ) :
    ∀ l : List ι, (((l.map f).sum : ℝ) : ℂ) = (l.map fun i => ((f i : ℝ) : ℂ)).sum
  | [] => by simp
  | i :: l => by
    simp only [List.map_cons, List.sum_cons, Complex.ofReal_add, ofReal_list_sum f l]

theorem coeffs_list_sum {ι : Type*} (F : ι → Langlands.GeneralLinear N ℝ → ℂ)
    (hF : ∀ i, Continuous (F i)) (L : List (Slot N)) (g : Langlands.GeneralLinear N ℝ) :
    ∀ l : List ι, coeffs L (fun y => (l.map fun i => F i y).sum) g =
      (l.map fun i => coeffs L (F i) g).sum
  | [] => by
    simp only [List.map_nil, List.sum_nil]
    exact coeffs_zero_fun L g
  | i :: l => by
    simp only [List.map_cons, List.sum_cons]
    have e : (fun y => F i y + (l.map fun i => F i y).sum) =
        F i + fun y => (l.map fun i => F i y).sum := rfl
    rw [e, RealLeviDensity.coeffs_add (hF i)
      (_root_.continuous_list_sum l fun i _ => hF i) L g, coeffs_list_sum F hF L g l]

theorem forall₂_withModes : ∀ (S : List (Slot N)) (J : List ℤ), J.length = S.length →
    List.Forall₂ (fun t s : Slot N => t.p = s.p) (withModes S J) S
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: S, _ :: J, h => List.Forall₂.cons rfl (forall₂_withModes S J (by simpa using h))

theorem map_zeroModes_of_forall₂ {P : Slot N → Slot N → Prop} (hP : ∀ t s, P t s → t.p = s.p) :
    ∀ {L' L : List (Slot N)}, List.Forall₂ P L' L →
      (zeroModes L').map (fun s => (s.p, s.j)) = (zeroModes L).map (fun s => (s.p, s.j))
  | [], [], _ => rfl
  | t :: L', s :: L, h => by
    rw [List.forall₂_cons] at h
    have ih := map_zeroModes_of_forall₂ hP h.2
    unfold zeroModes at ih ⊢
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨by simp [setMode, hP t s h.1], ih⟩

end Sums

/-! ## The witness -/

section Witness

open RealLeviSlices RealLeviProducts RealLeviDensity

variable {c : ℕ}

/-- `u` has the product coefficients of the family `φ`: its jointly allowed iterated coefficients
at the points `diag(κ)` are the products of those of the `φ_i`. -/
def ProdCoeffs (dss : Fin c → List RealBlock) (φ : ∀ i, Langlands.GeneralLinear (sz dss i) ℝ → ℂ)
    (u : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) : Prop :=
  ∀ Js : Fin c → List ℤ, (∀ i, (Js i).length = (slots (cl dss i) (sz dss i)).length) →
    (∀ i, ∀ t ∈ withModes (slots (cl dss i) (sz dss i)) (Js i), (t.M : ℤ) ≤ |t.j|) →
    ∀ κ : ∀ i, Langlands.GeneralLinear (sz dss i) ℝ, (∀ i, κ i ∈ unitaryCompact ℝ (sz dss i)) →
      coeffs (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn Js).flatten) u
          (blockDiagGL (sz dss) κ) =
        ∏ i, coeffs (withModes (slots (cl dss i) (sz dss i)) (Js i)) (φ i) (κ i)

theorem allowed_flat {dss : Fin c → List RealBlock} {Js : Fin c → List ℤ}
    (hJs : ∀ i, (Js i).length = (slots (cl dss i) (sz dss i)).length)
    (hall : ∀ i, ∀ t ∈ withModes (slots (cl dss i) (sz dss i)) (Js i), (t.M : ℤ) ≤ |t.j|) :
    ∀ t ∈ withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn Js).flatten,
      (t.M : ℤ) ≤ |t.j| := by
  refine allowed_of_map_key3 (map_key3_flat dss Js hJs).symm ?_
  intro t ht
  unfold globalSlots at ht
  obtain ⟨l, hl, htl⟩ := List.mem_flatten.mp ht
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hl
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp htl
  exact hall i t' ht'

theorem allowed_split {dss : Fin c → List RealBlock} {Js : Fin c → List ℤ}
    (hJs : ∀ i, (Js i).length = (slots (cl dss i) (sz dss i)).length)
    (hall : ∀ t ∈ withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn Js).flatten,
      (t.M : ℤ) ≤ |t.j|) (i : Fin c) :
    ∀ t ∈ withModes (slots (cl dss i) (sz dss i)) (Js i), (t.M : ℤ) ≤ |t.j| := fun _ ht =>
  allowed_of_map_key3 (map_key3_flat dss Js hJs) hall _
    (liftSlot_mem_globalSlots (fun i => withModes (slots (cl dss i) (sz dss i)) (Js i))
      (List.mem_finRange i) ht)

/-- Two functions with the product coefficients of the same family have the same jointly
allowed coefficients at the points `diag(κ)`. -/
theorem coeffs_eq_of_prodCoeffs {dss : Fin c → List RealBlock}
    {φ : ∀ i, Langlands.GeneralLinear (sz dss i) ℝ → ℂ}
    {u u' : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ}
    (hu : ProdCoeffs dss φ u) (hu' : ProdCoeffs dss φ u') :
    ∀ J : List ℤ, J.length = (slots (flat dss) (∑ i, sz dss i)).length →
      (∀ t ∈ withModes (slots (flat dss) (∑ i, sz dss i)) J, (t.M : ℤ) ≤ |t.j|) →
        ∀ κ : ∀ i, unitaryCompact ℝ (sz dss i),
          coeffs (withModes (slots (flat dss) (∑ i, sz dss i)) J) u (bdK (sz dss) κ) =
            coeffs (withModes (slots (flat dss) (∑ i, sz dss i)) J) u' (bdK (sz dss) κ) := by
  intro J hJ hall κ
  obtain ⟨Js, hJs, rfl⟩ := exists_split (fun i => (slots (cl dss i) (sz dss i)).length) J
    (hJ.trans (length_slots_flat dss))
  have hκ : ∀ i, (κ i : Langlands.GeneralLinear (sz dss i) ℝ) ∈ unitaryCompact ℝ (sz dss i) :=
    fun i => (κ i).2
  have e : bdK (sz dss) κ = blockDiagGL (sz dss) fun i => (κ i : Langlands.GeneralLinear _ ℝ) :=
    rfl
  rw [e, hu Js hJs (allowed_split hJs hall) _ hκ, hu' Js hJs (allowed_split hJs hall) _ hκ]

/-- With `f = conj (symCoeffs L u)` on `O(N)` for `L = withModes S J`, the integrand of the
pairing at `X = 0` is the sum of the squared absolute values of the coefficients of `u` at
`diag(κ)` along the sign variants of `L`. -/
theorem psi_zero_eq {sz : Fin c → ℕ} {ds : List RealBlock}
    {u f : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (hu : Continuous u)
    {J : List ℤ} (hJ : J.length = (slots ds (∑ i, sz i)).length)
    (hfu : ∀ k ∈ unitaryCompact ℝ (∑ i, sz i),
      f k = conj (symCoeffs (withModes (slots ds (∑ i, sz i)) J) u k))
    (κ : ∀ i, unitaryCompact ℝ (sz i)) :
    psi (slots ds (∑ i, sz i)) u f κ 0 =
      ((variants (withModes (slots ds (∑ i, sz i)) J)).map fun V =>
        ((‖coeffs V u (bdK sz κ)‖ ^ 2 : ℝ) : ℂ)).sum := by
  have hS := pairwise_slots ds (∑ i, sz i)
  have hL : (withModes (slots ds (∑ i, sz i)) J).Pairwise Slot.Disjoint :=
    pairwise_withModes J hS
  have hb : bdK sz κ ∈ unitaryCompact ℝ (∑ i, sz i) :=
    mem_unitaryCompact_of_mem_blockOrth (bdK_mem_blockOrth κ)
  have hF : ∀ V : List (Slot (∑ i, sz i)), Continuous fun y => u y * conj (coeffs V u y) :=
    fun V => hu.mul (Complex.continuous_conj.comp (continuous_coeffs hu V))
  have e1 : psi (slots ds (∑ i, sz i)) u f κ 0 =
      coeffs (zeroModes (slots ds (∑ i, sz i))) (fun y => u y * f y) (bdK sz κ) := by
    unfold psi
    rw [lowerGL_zero]
    have := coeffs_mul_right (fun y => u y * f y) (bdK sz κ) (zeroModes (slots ds (∑ i, sz i))) 1
    rw [one_mul] at this
    simp only [one_mul]
    exact this.symm
  have e2 : coeffs (zeroModes (slots ds (∑ i, sz i))) (fun y => u y * f y) (bdK sz κ) =
      coeffs (zeroModes (slots ds (∑ i, sz i)))
        (fun y => ((variants (withModes (slots ds (∑ i, sz i)) J)).map fun V =>
          u y * conj (coeffs V u y)).sum) (bdK sz κ) := by
    refine coeffs_congr_of_eqOn (fun y hy => ?_) _ _ hb
    show u y * f y = _
    rw [hfu y hy, symCoeffs_eq_sum hu _ y, map_list_sum, List.map_map, ← List.sum_map_mul_left]
    rfl
  rw [e1, e2, coeffs_list_sum (fun V y => u y * conj (coeffs V u y)) hF]
  refine congrArg List.sum (List.map_congr_left fun V hV => ?_)
  have h2 := forall₂_of_mem_variants hV
  have hV' : V.Pairwise Slot.Disjoint := pairwise_of_forall₂ (fun _ _ h => h.1) h2 hL
  have hz : (zeroModes (slots ds (∑ i, sz i))).map (fun s => (s.p, s.j)) =
      (zeroModes V).map (fun s => (s.p, s.j)) :=
    ((map_zeroModes_of_forall₂ (fun _ _ h => h.1) h2).trans
      (map_zeroModes_of_forall₂ (fun _ _ h => h) (forall₂_withModes _ J hJ))).symm
  rw [RealInducedTorusReduction.coeffs_congr_map _ _ hz, coeffs_zeroModes_mul_conj V
    (fun t ht θ y => coeffs_blockRotation_mul V hV' t ht u θ y) (bdK sz κ), Complex.conj_mul',
    Complex.ofReal_pow]

/-- **The witness.** Under the hypotheses of the limit argument along `Q` and the irreducibility
of the class standard modules, there are non-null `φ_i` and `h_0` with `Θ(u, h_0) ≠ 0` for every
`u` with the product coefficients of the `φ_i`. -/
theorem exists_witness (hT1 : RealLeviChartIntegrableStatement) {dss : Fin c → List RealBlock}
    (hanti : ∀ p q : Fin (∑ i, sz dss i), p ≤ q →
      realPositionBlockExponent (flat dss) q ≤ realPositionBlockExponent (flat dss) p)
    (hstrict : ∀ p q : Fin (∑ i, sz dss i), cls (sz dss) p < cls (sz dss) q →
      realPositionBlockExponent (flat dss) q < realPositionBlockExponent (flat dss) p)
    (hX : ∀ i, IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
      (realStandardLie (sz dss i) (cl dss i))) :
    ∃ φ : ∀ i, Langlands.GeneralLinear (sz dss i) ℝ → ℂ,
      (∀ i, φ i ∈ kFiniteFunctions (principalSeries ℝ (sz dss i)
        (dualChar (realPositionCharacter (cl dss i)))) (unitaryCompact ℝ (sz dss i))) ∧
      ∃ h0 ∈ kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss))
          (unitaryCompact ℝ (∑ j, sz dss j)),
        ∀ u ∈ kFiniteFunctions (principalSeries ℝ (∑ j, sz dss j)
            (dualChar (realPositionCharacter (flat dss)))) (unitaryCompact ℝ (∑ j, sz dss j)),
          ProdCoeffs dss φ u → theta (slots (flat dss) (∑ i, sz dss i)) u h0 ≠ 0 := by
  classical
  -- non-null class vectors
  choose φ hφ J hJlen hJall k hk hne using fun i => exists_nonNull (realRank_cl dss i)
  refine ⟨φ, hφ, ?_⟩
  have hN : realRank (flat dss) = ∑ j, sz dss j := realRank_flat dss
  have hχ := isSignedPower (flat dss)
  -- the density vector for `W = ⊥`
  have hbot : (⊥ : Submodule ℂ (kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss))
      (unitaryCompact ℝ (∑ j, sz dss j)))) ≠ ⊤ := by
    obtain ⟨x, hx, hx1⟩ := exists_std_ne_zero hN
    intro h
    have hmem : (⟨x, hx⟩ : kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss))
        (unitaryCompact ℝ (∑ j, sz dss j))) ∈ (⊥ : Submodule ℂ _) := by
      rw [h]
      exact Submodule.mem_top
    rw [Submodule.mem_bot] at hmem
    apply hx1
    have := congrArg (fun v : kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss))
      (unitaryCompact ℝ (∑ j, sz dss j)) =>
        (v : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) 1) hmem
    simpa using this
  obtain ⟨u0, hu0, -, hprod⟩ := realLeviDensity c dss hX φ hφ ⊥
    (fun _ w hw => by
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw, map_zero])
    (fun _ w hw => by
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw, map_zero]) hbot
  have hu0c : Continuous u0 := hu0.1.1.continuous
  -- the slots with the nonzero modes
  have hJlen' : (List.ofFn J).flatten.length = (slots (flat dss) (∑ j, sz dss j)).length := by
    rw [length_slots_flat, List.length_flatten, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => hJlen i
  have hall := allowed_flat hJlen hJall
  have hL0 := pairwise_withModes (List.ofFn J).flatten (pairwise_slots (flat dss) (∑ j, sz dss j))
  -- the test vector `f = conj (symCoeffs L₀ u₀)` of the standard module
  have hvs : ∀ (i : Fin (∑ j, sz dss j)) (g : Langlands.GeneralLinear (∑ j, sz dss j) ℝ),
      symCoeffs (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn J).flatten) u0
          (Unitary.toUnits (signReflection (∑ j, sz dss j) i) * g) =
        conj (realPositionCharacter (flat dss) i (-1)) *
          symCoeffs (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn J).flatten) u0 g := by
    intro i g
    refine symCoeffs_signReflection_mul i (fun g' => ?_) _ g
    rw [apply_signReflection_mul hχ.dual.one hu0.1 i g', dualChar,
      JacquetKernel.conj_eq_inv_of_norm_eq_one (hχ.norm_neg_one i)]
  obtain ⟨f, hf, hfP⟩ := exists_ext_conj hχ (continuous_symCoeffs hu0c _)
    (isKFin_symCoeffs hu0c hu0.2 _) hvs
  have hfX : f ∈ kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss))
      (unitaryCompact ℝ (∑ j, sz dss j)) := by
    refine mem_kFin_standard_of_window hN hf fun s hs m hm g hg => ?_
    obtain ⟨j', hj'⟩ := exists_setMode_mem_withModes hJlen' s hs
    have hM := hall _ hj'
    exact blockFourierCoefficient_conj_symCoeffs_eq_zero hu0c hL0 hfP hj'
      (lt_of_lt_of_le hm hM).ne hg
  -- positivity of the integrand at `X = 0`
  obtain ⟨G, hG⟩ : ∃ G : (∀ i, unitaryCompact ℝ (sz dss i)) → ℝ, ∀ κ, G κ =
      ((variants (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn J).flatten)).map
        fun V => ‖coeffs V u0 (bdK (sz dss) κ)‖ ^ 2).sum := ⟨_, fun _ => rfl⟩
  have hGc : Continuous G := by
    have : G = fun κ =>
        ((variants (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn J).flatten)).map
          fun V => ‖coeffs V u0 (bdK (sz dss) κ)‖ ^ 2).sum := funext hG
    rw [this]
    exact _root_.continuous_list_sum _ fun V _ =>
      (((continuous_coeffs hu0c V).comp continuous_bdK).norm).pow 2
  have hnn : ∀ κ, ∀ a ∈ (variants (withModes (slots (flat dss) (∑ j, sz dss j))
      (List.ofFn J).flatten)).map fun V => ‖coeffs V u0 (bdK (sz dss) κ)‖ ^ 2, 0 ≤ a := by
    intro κ a ha
    obtain ⟨V, -, rfl⟩ := List.mem_map.mp ha
    positivity
  have hGnn : 0 ≤ G := fun κ => by
    rw [hG]
    exact List.sum_nonneg (hnn κ)
  obtain ⟨κ0, hκ0⟩ : ∃ κ0 : ∀ i, unitaryCompact ℝ (sz dss i),
      bdK (sz dss) κ0 = blockDiagGL (sz dss) k := ⟨fun i => ⟨k i, hk i⟩, rfl⟩
  have hc0 : coeffs (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn J).flatten) u0
      (bdK (sz dss) κ0) ≠ 0 := by
    rw [hκ0, hprod J hJlen hJall k hk]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  have hG0 : G κ0 ≠ 0 := by
    rw [hG]
    have hle := List.single_le_sum (hnn κ0) _ (List.mem_map_of_mem
      (f := fun V => ‖coeffs V u0 (bdK (sz dss) κ0)‖ ^ 2)
      (mem_variants_self (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn J).flatten)))
    exact (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hc0) 2) hle).ne'
  have hint : 0 < ∫ κ, G κ ∂Measure.pi (fun i => haarK (sz dss i)) :=
    hGc.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace G)
      hGnn hG0
  have hpsi : ∀ κ, psi (slots (flat dss) (∑ j, sz dss j)) u0 f κ 0 = ((G κ : ℝ) : ℂ) := by
    intro κ
    rw [psi_zero_eq hu0c hJlen' hfP κ, hG, ofReal_list_sum]
  have h0 : ∫ κ, psi (slots (flat dss) (∑ j, sz dss j)) u0 f κ 0
      ∂Measure.pi (fun i => haarK (sz dss i)) ≠ 0 := by
    simp_rw [hpsi]
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr hint.ne'
  -- the nonvanishing of the pairing, and its dependence on the product coefficients only
  obtain ⟨h, hh, hθ⟩ := RealLeviNonvanishing.exists_theta_ne_zero hT1 ⟨hN, hanti, hstrict⟩ hu0 hfX h0
  refine ⟨h, hh, fun u hu hpu => ?_⟩
  rw [theta_congr hu hu0 hh (coeffs_eq_of_prodCoeffs hpu hprod)]
  exact hθ

end Witness

end RealLeviWitness

open RealInducedBlockBound RealInducedTorusCore RealLeviChart RealPrincipalSeriesDuality
  PartialJacquet RealInducedStandardBound RealStrictCharacterLanglandsQuotient RealLeviSlices in
attribute [local instance] measurableSpaceK in
/-- **Statement (a witness for the pairing along `Q`).** Assume
`RealLeviChartIntegrableStatement`. Let `dss_0, …, dss_{c-1}` be lists of real blocks of ranks
`sz_i`, `N = ∑_i sz_i`, `ds = dss_0 ++ ⋯ ++ dss_{c-1}` and `cl_i` the twisted class lists, such
that the block exponents of `ds` decrease weakly along the positions and strictly from one block
of `Q` to the next, and every class standard module (of `cl_i`) is irreducible. Then there are
`O(sz_i)`-finite vectors `φ_i` of the principal series of the inverse position characters of
`cl_i` and an `O(N)`-finite vector `h_0` of the standard module of `ds` such that
`∫_{K_M} ∫_{N̄_Q} c_Z(x ↦ u(x diag(κ)) h_0(x n̄(X) diag(κ))) dX dκ ≠ 0` for every
`O(N)`-finite vector `u` of the principal series of the inverse position characters of `ds`
whose jointly allowed iterated block Fourier coefficients along the induction slots of `ds` at
every `diag(κ_0, …, κ_{c-1})`, `κ_i ∈ O(sz_i)`, are the products of the coefficients of the
`φ_i` at `κ_i` along the induction slots of `cl_i`. -/
def RealLeviWitnessStatement : Prop :=
  RealLeviChartIntegrableStatement →
  ∀ (c : ℕ) (dss : Fin c → List RealBlock),
    (∀ p q : Fin (∑ i, sz dss i), p ≤ q →
      realPositionBlockExponent (flat dss) q ≤ realPositionBlockExponent (flat dss) p) →
    (∀ p q : Fin (∑ i, sz dss i), cls (sz dss) p < cls (sz dss) q →
      realPositionBlockExponent (flat dss) q < realPositionBlockExponent (flat dss) p) →
    (∀ i, IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
      (realStandardLie (sz dss i) (cl dss i))) →
    ∃ φ : ∀ i, Langlands.GeneralLinear (sz dss i) ℝ → ℂ,
      (∀ i, φ i ∈ kFiniteFunctions (principalSeries ℝ (sz dss i)
        (dualChar (realPositionCharacter (cl dss i)))) (unitaryCompact ℝ (sz dss i))) ∧
      ∃ h0 ∈ kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss))
          (unitaryCompact ℝ (∑ j, sz dss j)),
        ∀ u ∈ kFiniteFunctions (principalSeries ℝ (∑ j, sz dss j)
            (dualChar (realPositionCharacter (flat dss)))) (unitaryCompact ℝ (∑ j, sz dss j)),
          (∀ Js : Fin c → List ℤ,
            (∀ i, (Js i).length = (slots (cl dss i) (sz dss i)).length) →
            (∀ i, ∀ t ∈ withModes (slots (cl dss i) (sz dss i)) (Js i), (t.M : ℤ) ≤ |t.j|) →
            ∀ κ : ∀ i, Langlands.GeneralLinear (sz dss i) ℝ,
              (∀ i, κ i ∈ unitaryCompact ℝ (sz dss i)) →
              coeffs (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn Js).flatten) u
                  (blockDiagGL (sz dss) κ) =
                ∏ i, coeffs (withModes (slots (cl dss i) (sz dss i)) (Js i)) (φ i) (κ i)) →
          ∫ κ : (∀ i, unitaryCompact ℝ (sz dss i)),
            (∫ X : Coord (sz dss) → ℝ, coeffs (zeroModes (slots (flat dss) (∑ i, sz dss i)))
              (fun x => u (x * blockDiagGL (sz dss)
                  (fun i => (κ i : Langlands.GeneralLinear (sz dss i) ℝ))) *
                h0 (x * (lowerGL (sz dss) X * blockDiagGL (sz dss)
                  (fun i => (κ i : Langlands.GeneralLinear (sz dss i) ℝ))))) 1)
            ∂Measure.pi (fun i => haarK (sz dss i)) ≠ 0

theorem realLeviWitness : RealLeviWitnessStatement := by
  intro hT1 c dss hanti hstrict hX
  exact RealLeviWitness.exists_witness hT1 hanti hstrict hX

end Langlands.Archimedean
