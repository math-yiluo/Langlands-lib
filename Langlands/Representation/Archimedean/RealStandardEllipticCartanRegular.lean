import Langlands.Representation.Archimedean.RealStandardEllipticCartanNumerator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Baire.Lemmas

/-! # Regular coordinates for the real standard Cartan numerator -/

noncomputable section

set_option autoImplicit false

open Set

namespace Langlands.Archimedean.RealStandardEllipticCartan

/-- Coordinates with distinct logarithmic radii within each kind of slot and with
nonreal eigenvalues in each complex slot. -/
def regularCoordinates (r s : ℕ) : Set (Coordinates r s) :=
  {x | Function.Injective (fun i => (x.1 i).toAdd.1) ∧
    Function.Injective (fun j => (x.2 j).toAdd.1) ∧ ∀ i, Real.sin (x.1 i).toAdd.2 ≠ 0}

private theorem dense_iInter_finite {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {U : ι → Set X} (ho : ∀ i, IsOpen (U i)) (hd : ∀ i, Dense (U i)) :
    Dense (⋂ i, U i) := by
  rw [← sInter_range]
  exact (Set.toFinite _).dense_sInter (fun _ ⟨i, hi⟩ => hi ▸ ho i)
    (fun _ ⟨i, hi⟩ => hi ▸ hd i)

private theorem dense_injective_radii {ι A : Type*} [Finite ι] [DecidableEq ι]
    [TopologicalSpace A] :
    Dense {x : ι → ℝ × A | Function.Injective (fun i => (x i).1)} := by
  let U (ij : {ij : ι × ι // ij.1 ≠ ij.2}) : Set (ι → ℝ × A) :=
    {x | (x ij.1.1).1 ≠ (x ij.1.2).1}
  have hU : ∀ ij, IsOpen (U ij) := fun ij =>
    isOpen_ne_fun (continuous_fst.comp (continuous_apply ij.1.1))
      (continuous_fst.comp (continuous_apply ij.1.2))
  refine (dense_iInter_finite hU ?_).mono ?_
  · rintro ⟨⟨i, j⟩, hij⟩
    rw [dense_iff_inter_open]
    rintro V hV ⟨x, hx⟩
    let f (t : ℝ) := Function.update x i (t, (x i).2)
    have hf : Continuous f := continuous_const.update i (continuous_id.prodMk continuous_const)
    have hfx : f (x i).1 = x := Function.update_eq_self i x
    have hxV : (x i).1 ∈ f ⁻¹' V := by
      change f (x i).1 ∈ V
      simpa only [hfx] using hx
    obtain ⟨t, ht, htV⟩ := (dense_compl_singleton (x j).1).exists_mem_open
      (hV.preimage hf) ⟨(x i).1, hxV⟩
    exact ⟨f t, htV, by simpa [U, f, Function.update_of_ne hij.symm] using ht⟩
  · intro x hx i j heq
    by_contra hij
    exact (mem_iInter.mp hx ⟨(i, j), hij⟩) heq

private theorem dense_angles (r : ℕ) :
    Dense {x : Fin r → ℝ × ℝ | ∀ i, Real.sin (x i).2 ≠ 0} := by
  let S : Set ℝ := {θ | Real.sin θ ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun Real.continuous_sin continuous_const
  have hcount : (Sᶜ).Countable := by
    have heq : Sᶜ = range (fun m : ℤ => (m : ℝ) * Real.pi) := by
      ext θ
      simpa [S, mem_range] using (Real.sin_eq_zero_iff (x := θ))
    rw [heq]
    exact countable_range _
  have hd : Dense S := by simpa using hcount.dense_compl ℝ
  let f (i : Fin r) (x : Fin r → ℝ × ℝ) := (x i).2
  convert dense_iInter_finite (U := fun i => f i ⁻¹' S)
    (fun i => hS.preimage (continuous_snd.comp (continuous_apply i)))
    (fun i => hd.preimage (isOpenMap_snd.comp (isOpenMap_eval i))) using 1
  ext x
  simp [S, f]

/-- Regular coordinates are dense, including for each choice of real signs. -/
theorem dense_regularCoordinates (r s : ℕ) : Dense (regularCoordinates r s) := by
  have hangle : IsOpen {x : Fin r → ℝ × ℝ | ∀ i, Real.sin (x i).2 ≠ 0} := by
    have h : {x : Fin r → ℝ × ℝ | ∀ i, Real.sin (x i).2 ≠ 0} =
        ⋂ i, {x | Real.sin (x i).2 ≠ 0} := by ext x; simp
    rw [h]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_ne_fun (Real.continuous_sin.comp (continuous_snd.comp (continuous_apply i)))
        continuous_const
  refine ((dense_injective_radii (ι := Fin r) (A := ℝ)).inter_of_isOpen_right
    (dense_angles r) hangle).prod (dense_injective_radii (ι := Fin s) (A := ℤ)) |>.mono ?_
  exact fun _ h => ⟨h.1.1, h.2, h.1.2⟩

/-- The finite Cartan numerator is continuous in the coordinate product topology. -/
theorem continuous_numerator {r s : ℕ} (p : Parameters r s) : Continuous (numerator p) := by
  have hc (a : ℤ × ℂ) : Continuous (complexTerm a : Multiplicative (ℝ × ℝ) → ℂ) := by
    change Continuous (fun x : ℝ × ℝ => Complex.exp
      ((x.1 : ℂ) * (2 * a.2) + (x.2 : ℂ) * (Complex.I * (a.1 : ℂ))))
    fun_prop
  have hr (a : Fin 2 × ℂ) : Continuous (realTerm a : Multiplicative (ℝ × ℤ) → ℂ) := by
    change Continuous (fun x : ℝ × ℤ => Complex.exp ((x.1 : ℂ) * a.2) *
      (-1 : ℂ) ^ ((a.1.val : ℤ) * x.2))
    exact (by fun_prop : Continuous fun x : ℝ × ℤ => Complex.exp ((x.1 : ℂ) * a.2)).mul
      ((continuous_of_discreteTopology :
        Continuous fun z : ℤ => (-1 : ℂ) ^ ((a.1.val : ℤ) * z)).comp continuous_snd)
  change Continuous (fun x => numerator p x)
  simp_rw [numerator_apply]
  have hcomplex (a : ℤ × ℂ) (i : Fin r) :
      Continuous fun x : Coordinates r s => complexTerm a (x.1 i) :=
    (hc a).comp ((continuous_apply i).comp continuous_fst)
  have hreal (a : Fin 2 × ℂ) (j : Fin s) :
      Continuous fun x : Coordinates r s => realTerm a (x.2 j) :=
    (hr a).comp ((continuous_apply j).comp continuous_snd)
  fun_prop

private theorem complexTerm_sub_ne_zero {m : ℤ} (t : ℂ) {θ : ℝ}
    (h : Real.sin (θ * (m : ℝ)) ≠ 0) :
    complexTerm (m, t) (Multiplicative.ofAdd (0, θ)) -
      complexTerm (-m, t) (Multiplicative.ofAdd (0, θ)) ≠ 0 := by
  intro hnum
  have hexp : Complex.exp (((θ : ℂ) * (m : ℂ)) * Complex.I) =
      Complex.exp (-((θ : ℂ) * (m : ℂ)) * Complex.I) := by
    simpa [complexTerm, mul_left_comm, mul_comm, mul_assoc, neg_mul, mul_neg]
      using sub_eq_zero.mp hnum
  have hsin : Complex.sin ((θ : ℂ) * (m : ℂ)) = 0 := by
    rw [Complex.sin, ← hexp, sub_self, zero_mul, zero_div]
  apply h
  have : (Real.sin (θ * (m : ℝ)) : ℂ) = 0 := by
    simpa only [Complex.ofReal_sin, Complex.ofReal_mul, Complex.ofReal_intCast] using hsin
  exact_mod_cast this

private theorem numerator_ne_zero {r s : ℕ} {p : Parameters r s}
    (hp : ∀ i, 0 < (p.1 i).1) : numerator p ≠ 0 := by
  let M : ℝ := ∑ i, ((p.1 i).1 : ℝ)
  let θ := Real.pi / (1 + M)
  have hw (i : Fin r) : 0 < ((p.1 i).1 : ℝ) := by exact_mod_cast hp i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => (hw i).le
  have hden : 0 < 1 + M := by positivity
  have hθ : 0 < θ := div_pos Real.pi_pos hden
  let a : Multiplicative (ℝ × ℝ) := Multiplicative.ofAdd (0, θ)
  let f (i : Fin r) := complexTerm (p.1 i) a - complexTerm (-(p.1 i).1, (p.1 i).2) a
  have hf (i : Fin r) : f i ≠ 0 := by
    have hle : ((p.1 i).1 : ℝ) ≤ M :=
      Finset.single_le_sum (fun j _ => (hw j).le) (Finset.mem_univ i)
    have hlt : θ * ((p.1 i).1 : ℝ) < Real.pi := by
      rw [mul_comm θ, show θ = Real.pi / (1 + M) by rfl, ← mul_div_assoc,
        div_lt_iff₀ hden, mul_comm Real.pi]
      exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
    exact complexTerm_sub_ne_zero _ (Real.sin_pos_of_pos_of_lt_pi (mul_pos hθ (hw i)) hlt).ne'
  intro h
  have he := congrFun h ((fun _ => a, 1) : Coordinates r s)
  rw [numerator_apply] at he
  change (∑ π : Equiv.Perm (Fin r), ∑ σ : Equiv.Perm (Fin s),
    (∏ i, f (π i)) * ∏ j, realTerm (p.2 (σ j)) 1) = 0 at he
  simp_rw [map_one, Finset.prod_const_one, mul_one, Equiv.prod_comp] at he
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
  have hcard (k : ℕ) : (Fintype.card (Equiv.Perm (Fin k)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_ne_zero (hcard r)
    (mul_ne_zero (hcard s) (Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)))) he

/-- A numerator of strictly positive induced weights is nonzero at some regular coordinates. -/
theorem exists_regular_numerator_ne_zero {r s : ℕ} {p : Parameters r s}
    (hp : ∀ i, 0 < (p.1 i).1) : ∃ x ∈ regularCoordinates r s, numerator p x ≠ 0 := by
  by_contra! h
  exact numerator_ne_zero hp
    (Continuous.ext_on (dense_regularCoordinates r s) (continuous_numerator p) continuous_const h)

/-- Equality of Cartan numerators on the regular coordinates extends to all coordinates. -/
theorem numerator_eq_of_eqOn_regular {r s : ℕ} {p q : Parameters r s}
    (h : EqOn (numerator p) (numerator q) (regularCoordinates r s)) :
    numerator p = numerator q :=
  Continuous.ext_on (dense_regularCoordinates r s) (continuous_numerator p)
    (continuous_numerator q) h

/-- Regular coordinate nonvanishing and extension of equality for the finite Cartan numerator. -/
def RealStandardEllipticCartanRegularStatement : Prop :=
  ∀ (r s : ℕ), Dense (regularCoordinates r s) ∧
    (∀ p : Parameters r s, (∀ i, 0 < (p.1 i).1) →
      ∃ x ∈ regularCoordinates r s, numerator p x ≠ 0) ∧
    ∀ p q : Parameters r s, EqOn (numerator p) (numerator q) (regularCoordinates r s) →
      numerator p = numerator q

theorem realStandardEllipticCartanRegular : RealStandardEllipticCartanRegularStatement :=
  fun r s => ⟨dense_regularCoordinates r s, fun _ => exists_regular_numerator_ne_zero,
    fun _ _ => numerator_eq_of_eqOn_regular⟩

end Langlands.Archimedean.RealStandardEllipticCartan
