import Langlands.Group.GL.UpperBruhatCells
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-!
# Principal-series functions are determined by their values on the lower unipotent group

`eq_zero_of_eqOn_lowerUnipotent`: a function of the smooth principal series of `GL_n(ℂ)` that
vanishes on the lower unipotent subgroup is zero. The proof is the density of the big cell
`B · N̄`: a matrix whose lower-right corner minors are all nonzero factors as an upper
triangular matrix times a lower unipotent one (`exists_upper_mul_lower_of_cornerNonzero`), and
every invertible matrix `g` is the limit of `g + t` with all corner minors of `g + t` nonzero.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear

set_option backward.isDefEq.respectTransparency false

namespace LowerUnipotentRestriction

variable {K : Type*} [Field K]

/-- All lower-right corner minors of a square matrix are nonzero, stated recursively: the
determinant is nonzero, and so are the corner minors of the block obtained by deleting the
first row and column. -/
def CornerNonzero : (m : ℕ) → Matrix (Fin m) (Fin m) K → Prop
  | 0, _ => True
  | m + 1, h => h.det ≠ 0 ∧ CornerNonzero m (h.submatrix Fin.succ Fin.succ)

theorem det_ne_zero_of_cornerNonzero : ∀ {m : ℕ} {h : Matrix (Fin m) (Fin m) K},
    CornerNonzero m h → h.det ≠ 0
  | 0, h, _ => by simp [Matrix.det_fin_zero]
  | _ + 1, _, hh => hh.1

/-- Lower unipotent: zero above the diagonal and one on it. -/
def IsLowerUnipotent {m : ℕ} (L : Matrix (Fin m) (Fin m) K) : Prop :=
  (∀ i j : Fin m, i < j → L i j = 0) ∧ ∀ i : Fin m, L i i = 1

theorem det_eq_one_of_isLowerUnipotent {m : ℕ} {L : Matrix (Fin m) (Fin m) K}
    (hL : IsLowerUnipotent L) : L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular L (fun i j hij => hL.1 i j hij)]
  simp [hL.2]

/-- **LU decomposition on the big cell.** A matrix with nonzero lower-right corner minors is an
upper triangular matrix times a lower unipotent one. -/
theorem exists_upper_mul_lower_of_cornerNonzero : ∀ (m : ℕ) (h : Matrix (Fin m) (Fin m) K),
    CornerNonzero m h → ∃ b L : Matrix (Fin m) (Fin m) K,
      b.IsUpperTriangular ∧ IsLowerUnipotent L ∧ h = b * L
  | 0, h, _ => ⟨h, 1, fun i => Fin.elim0 i, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      by ext i; exact Fin.elim0 i⟩
  | m + 1, h, hh => by
    set h' := h.submatrix Fin.succ Fin.succ
    obtain ⟨b', L', hb', hL', he⟩ := exists_upper_mul_lower_of_cornerNonzero m h' hh.2
    have hdet' : h'.det ≠ 0 := det_ne_zero_of_cornerNonzero hh.2
    have hL'det : L'.det = 1 := det_eq_one_of_isLowerUnipotent hL'
    have hb'det : b'.det ≠ 0 := by
      intro h0
      apply hdet'
      rw [he, Matrix.det_mul, h0, zero_mul]
    let col : Fin m → K := fun i => h i.succ 0
    let row : Fin m → K := fun j => h 0 j.succ
    let ℓ : Fin m → K := b'⁻¹ *ᵥ col
    let rb : Fin m → K := row ᵥ* L'⁻¹
    let β : K := h 0 0 - rb ⬝ᵥ ℓ
    let b : Matrix (Fin (m + 1)) (Fin (m + 1)) K := Matrix.of fun i j =>
      Fin.cases (Fin.cases β rb j) (fun i' => Fin.cases 0 (fun j' => b' i' j') j) i
    let L : Matrix (Fin (m + 1)) (Fin (m + 1)) K := Matrix.of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases (ℓ i') (fun j' => L' i' j') j) i
    have hb'inv : b' * b'⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hb'det)
    have hL'inv : L'⁻¹ * L' = 1 :=
      Matrix.nonsing_inv_mul _ (by rw [hL'det]; exact isUnit_one)
    refine ⟨b, L, ?_, ⟨?_, ?_⟩, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ i =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => exact hb' (Fin.succ_lt_succ_iff.1 hij)
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl _)
        | succ j => rfl
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd hij (Fin.not_lt_zero _)
        | succ j => exact hL'.1 i j (Fin.succ_lt_succ_iff.1 hij)
    · intro i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => exact hL'.2 i
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero =>
          simp only [b, L, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, mul_one]
          have : ∑ x : Fin m, rb x * ℓ x = rb ⬝ᵥ ℓ := rfl
          rw [this]
          simp [β]
        | succ j =>
          simp only [b, L, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add]
          have : ∑ x : Fin m, rb x * L' x j = (rb ᵥ* L') j := by
            simp [Matrix.vecMul, dotProduct]
          rw [this]
          simp only [rb, Matrix.vecMul_vecMul, hL'inv, Matrix.vecMul_one, row]
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [b, L, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add]
          have : ∑ x : Fin m, b' i x * ℓ x = (b' *ᵥ ℓ) i := by
            simp [Matrix.mulVec, dotProduct]
          rw [this]
          simp only [ℓ, Matrix.mulVec_mulVec, hb'inv, Matrix.one_mulVec, col]
        | succ j =>
          simp only [b, L, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add]
          have h1 : h i.succ j.succ = h' i j := rfl
          rw [h1, he, Matrix.mul_apply]

/-- The corner minors of `g + t` are nonzero for all but finitely many `t`. -/
theorem finite_setOf_not_cornerNonzero : ∀ (m : ℕ) (g : Matrix (Fin m) (Fin m) K),
    {t : K | ¬ CornerNonzero m (g + t • (1 : Matrix (Fin m) (Fin m) K))}.Finite
  | 0, g => by simp [CornerNonzero]
  | m + 1, g => by
    have hsub : ∀ t : K,
        (g + t • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).submatrix Fin.succ Fin.succ
          = g.submatrix Fin.succ Fin.succ + t • (1 : Matrix (Fin m) (Fin m) K) := by
      intro t
      ext i j
      simp [Matrix.one_apply, Fin.succ_inj]
    have hdet : {t : K | (g + t • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det = 0}.Finite := by
      have hp : (Matrix.charpoly (-g)) ≠ 0 := (Matrix.charpoly_monic _).ne_zero
      refine (Polynomial.finite_setOfPred_isRoot hp).subset fun t ht => ?_
      simp only [Set.mem_ofPred_eq] at ht ⊢
      rw [Polynomial.IsRoot, Matrix.eval_charpoly]
      rw [← ht]
      congr 1
      ext i j
      simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs <;> ring
    refine (hdet.union (finite_setOf_not_cornerNonzero m (g.submatrix Fin.succ Fin.succ))).subset
      fun t ht => ?_
    simp only [Set.mem_ofPred_eq, CornerNonzero, not_and_or, not_not, hsub] at ht
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr ht

end LowerUnipotentRestriction

open LowerUnipotentRestriction

variable {n : ℕ} {χ : ℕ → ℂˣ → ℂ}

/-- A function of the smooth principal series vanishing on the lower unipotent group vanishes
on every invertible matrix with nonzero corner minors. -/
theorem eq_zero_of_cornerNonzero {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ principalSeries ℂ n χ) (h0 : ∀ L ∈ lowerUnipotent n ℂ, f L = 0)
    {g : Langlands.GeneralLinear n ℂ} (hg : CornerNonzero n (g : Matrix (Fin n) (Fin n) ℂ)) :
    f g = 0 := by
  obtain ⟨b, L, hb, hL, he⟩ := exists_upper_mul_lower_of_cornerNonzero n _ hg
  have hLu : IsUnit L := by
    rw [Matrix.isUnit_iff_isUnit_det, det_eq_one_of_isLowerUnipotent hL]
    exact isUnit_one
  have hbdet : b.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det he
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact (g.isUnit.map Matrix.detMonoidHom).ne_zero this
  have hdiag : ∀ i, b i i ≠ 0 := by
    intro i hi
    apply hbdet
    rw [Matrix.det_of_isUpperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  let a : Fin n → ℂˣ := fun i => Units.mk0 (b i i) (hdiag i)
  let D := Iwasawa.diagonalUnits a
  -- `u = D⁻¹ b` is upper unipotent.
  have hbu : IsUnit b := (Matrix.isUnit_iff_isUnit_det b).2 (isUnit_iff_ne_zero.2 hbdet)
  let bU : Langlands.GeneralLinear n ℂ := hbu.unit
  let LU : Langlands.GeneralLinear n ℂ := hLu.unit
  have hLmem : LU ∈ lowerUnipotent n ℂ := (mem_lowerUnipotent_iff n ℂ LU).2 hL
  have humem : D⁻¹ * bU ∈ upperUnipotent n ℂ := by
    refine (mem_upperUnipotent_iff n ℂ _).2 ⟨fun i j hji => ?_, fun i => ?_⟩
    · change (((D⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * b) i j = 0
      rw [show ((D⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
          Matrix.diagonal fun i => (((a i)⁻¹ : ℂˣ) : ℂ) by
        rw [← map_inv]; exact Iwasawa.diagonalUnits_val _, Matrix.diagonal_mul, hb hji, mul_zero]
    · change (((D⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * b) i i = 1
      rw [show ((D⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
          Matrix.diagonal fun i => (((a i)⁻¹ : ℂˣ) : ℂ) by
        rw [← map_inv]; exact Iwasawa.diagonalUnits_val _, Matrix.diagonal_mul]
      simp [a, hdiag i]
  have hgeq : g = D * (⟨_, humem⟩ : upperUnipotent n ℂ) * LU := by
    apply Units.ext
    change (g : Matrix (Fin n) (Fin n) ℂ) =
      ((D * (D⁻¹ * bU) : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * L
    rw [mul_inv_cancel_left]
    exact he
  rw [hgeq, ((mem_principalSeries_iff ℂ n χ f).1 hf).2 a ⟨_, humem⟩ LU, h0 LU hLmem, mul_zero]

/-- **Restriction to the lower unipotent group is injective** on the smooth principal series:
a function of the principal series vanishing on the lower unipotent group is zero. -/
theorem eq_zero_of_eqOn_lowerUnipotent {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ principalSeries ℂ n χ) (h0 : ∀ L ∈ lowerUnipotent n ℂ, f L = 0) : f = 0 := by
  funext g
  set φ := unitsExtension f
  have hcont : ContinuousAt φ (g : Matrix (Fin n) (Fin n) ℂ) :=
    ((contDiffOn_unitsExtension ((mem_principalSeries_iff ℂ n χ f).1 hf).1).continuousOn
      ).continuousAt (isOpen_setOf_isUnit_matrix.mem_nhds g.isUnit)
  let γ : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => (g : Matrix (Fin n) (Fin n) ℂ) +
    ((t : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)
  have hγ : Filter.Tendsto γ (𝓝[≠] (0 : ℝ)) (𝓝 (g : Matrix (Fin n) (Fin n) ℂ)) := by
    have hc : Continuous γ := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    simpa [γ] using this
  have hlim := hcont.tendsto.comp hγ
  have hfin := finite_setOf_not_cornerNonzero n (g : Matrix (Fin n) (Fin n) ℂ)
  have hfinR : {t : ℝ | ¬ CornerNonzero n (γ t)}.Finite :=
    (hfin.preimage (Complex.ofReal_injective.injOn)).subset fun t ht => ht
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), φ (γ t) = 0 := by
    have hnot : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∉ {t : ℝ | ¬ CornerNonzero n (γ t)} \ {0} := by
      have hclosed : IsClosed ({t : ℝ | ¬ CornerNonzero n (γ t)} \ {0}) :=
        (hfinR.subset Set.sdiff_subset).isClosed
      have hmem : (0 : ℝ) ∉ {t : ℝ | ¬ CornerNonzero n (γ t)} \ {0} := fun h => h.2 rfl
      exact nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hmem)
    filter_upwards [hnot, self_mem_nhdsWithin] with t ht ht0
    have hc : CornerNonzero n (γ t) := by
      by_contra hc
      exact ht ⟨hc, ht0⟩
    have hu : IsUnit (γ t) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_ne_zero_of_cornerNonzero hc))
    have := eq_zero_of_cornerNonzero hf h0 (g := hu.unit) hc
    simpa [φ, unitsExtension, hu] using this
  have hlim0 : Filter.Tendsto (φ ∘ γ) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhds_of_eventually_eq hev
  have := tendsto_nhds_unique hlim hlim0
  simpa [φ, unitsExtension_val] using this

/-- **Restriction to the lower unipotent group is injective on the complex principal series.**
For every `n`, all characters `χ` and every function `f` of the smooth principal series
`principalSeries ℂ n χ` of `GL_n(ℂ)`: if `f` vanishes on the lower unipotent subgroup, then
`f = 0`. -/
def ComplexPrincipalSeriesLowerUnipotentDeterminingStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℂˣ → ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ),
    f ∈ principalSeries ℂ n χ → (∀ L ∈ lowerUnipotent n ℂ, f L = 0) → f = 0

/-- Proof of `ComplexPrincipalSeriesLowerUnipotentDeterminingStatement`. -/
theorem complexPrincipalSeriesLowerUnipotentDetermining :
    ComplexPrincipalSeriesLowerUnipotentDeterminingStatement :=
  fun _ _ _ hf h0 => eq_zero_of_eqOn_lowerUnipotent hf h0

end Langlands.Archimedean
