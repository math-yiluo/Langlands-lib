import Langlands.Representation.Archimedean.ComplexLowerUnipotentRestriction

/-!
# Real principal-series functions are determined on the lower unipotent group

`RealLowerUnipotent.eq_zero_of_eqOn_lowerUnipotent`: a function of the smooth principal series of
`GL_n(ℝ)` that vanishes on the lower unipotent subgroup is zero. This is the real case of the
Library theorem `eq_zero_of_eqOn_lowerUnipotent` (module `ComplexLowerUnipotentRestriction`), with
the same proof: the density of the big cell, through the field-general lemmas
`LowerUnipotentRestriction.exists_upper_mul_lower_of_cornerNonzero` and
`LowerUnipotentRestriction.finite_setOf_not_cornerNonzero`.

The module also introduces coordinates on the lower unipotent group: `nbar v` is the lower
unipotent matrix whose entries strictly below the diagonal are given by `v : LowIdx n → ℝ`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear LowerUnipotentRestriction

set_option backward.isDefEq.respectTransparency false

namespace RealLowerUnipotent

variable {n : ℕ} {χ : ℕ → ℝˣ → ℂ}

/-- A function of the real smooth principal series vanishing on the lower unipotent group
vanishes on every invertible matrix with nonzero corner minors. -/
theorem eq_zero_of_cornerNonzero {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ n χ) (h0 : ∀ L ∈ lowerUnipotent n ℝ, f L = 0)
    {g : Langlands.GeneralLinear n ℝ} (hg : CornerNonzero n (g : Matrix (Fin n) (Fin n) ℝ)) :
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
  let a : Fin n → ℝˣ := fun i => Units.mk0 (b i i) (hdiag i)
  let D := Iwasawa.diagonalUnits a
  have hbu : IsUnit b := (Matrix.isUnit_iff_isUnit_det b).2 (isUnit_iff_ne_zero.2 hbdet)
  let bU : Langlands.GeneralLinear n ℝ := hbu.unit
  let LU : Langlands.GeneralLinear n ℝ := hLu.unit
  have hLmem : LU ∈ lowerUnipotent n ℝ := (mem_lowerUnipotent_iff n ℝ LU).2 hL
  have humem : D⁻¹ * bU ∈ upperUnipotent n ℝ := by
    refine (mem_upperUnipotent_iff n ℝ _).2 ⟨fun i j hji => ?_, fun i => ?_⟩
    · change (((D⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * b) i j = 0
      rw [show ((D⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
          Matrix.diagonal fun i => (((a i)⁻¹ : ℝˣ) : ℝ) by
        rw [← map_inv]; exact Iwasawa.diagonalUnits_val _, Matrix.diagonal_mul, hb hji, mul_zero]
    · change (((D⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * b) i i = 1
      rw [show ((D⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
          Matrix.diagonal fun i => (((a i)⁻¹ : ℝˣ) : ℝ) by
        rw [← map_inv]; exact Iwasawa.diagonalUnits_val _, Matrix.diagonal_mul]
      simp [a, hdiag i]
  have hgeq : g = D * (⟨_, humem⟩ : upperUnipotent n ℝ) * LU := by
    apply Units.ext
    change (g : Matrix (Fin n) (Fin n) ℝ) =
      ((D * (D⁻¹ * bU) : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * L
    rw [mul_inv_cancel_left]
    exact he
  rw [hgeq, ((mem_principalSeries_iff ℝ n χ f).1 hf).2 a ⟨_, humem⟩ LU, h0 LU hLmem, mul_zero]

/-- **Restriction to the lower unipotent group is injective** on the real smooth principal
series: a function of the principal series vanishing on the lower unipotent group is zero. -/
theorem eq_zero_of_eqOn_lowerUnipotent {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ n χ) (h0 : ∀ L ∈ lowerUnipotent n ℝ, f L = 0) : f = 0 := by
  funext g
  set φ := unitsExtension f
  have hcont : ContinuousAt φ (g : Matrix (Fin n) (Fin n) ℝ) :=
    ((contDiffOn_unitsExtension ((mem_principalSeries_iff ℝ n χ f).1 hf).1).continuousOn
      ).continuousAt (isOpen_setOf_isUnit_matrix.mem_nhds g.isUnit)
  let γ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => (g : Matrix (Fin n) (Fin n) ℝ) +
    t • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hγ : Filter.Tendsto γ (𝓝[≠] (0 : ℝ)) (𝓝 (g : Matrix (Fin n) (Fin n) ℝ)) := by
    have hc : Continuous γ := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    simpa [γ] using this
  have hlim := hcont.tendsto.comp hγ
  have hfinR : {t : ℝ | ¬ CornerNonzero n (γ t)}.Finite :=
    finite_setOf_not_cornerNonzero n (g : Matrix (Fin n) (Fin n) ℝ)
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

/-! ## Coordinates on the lower unipotent group -/

variable (n) in
/-- The positions `(i, j)` strictly below the diagonal (`j < i`). -/
abbrev LowIdx : Type := {c : Fin n × Fin n // c.2 < c.1}

/-- The lower unipotent matrix whose entry at a position `(i, j)` with `j < i` is `v (i, j)`. -/
def nbarMat (v : LowIdx n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : j < i then v ⟨(i, j), h⟩ else if i = j then 1 else 0

theorem isLowerUnipotent_nbarMat (v : LowIdx n → ℝ) : IsLowerUnipotent (nbarMat v) :=
  ⟨fun i j hij => by simp [nbarMat, not_lt.2 hij.le, hij.ne], fun i => by simp [nbarMat]⟩

theorem det_nbarMat (v : LowIdx n → ℝ) : (nbarMat v).det = 1 :=
  det_eq_one_of_isLowerUnipotent (isLowerUnipotent_nbarMat v)

theorem isUnit_nbarMat (v : LowIdx n → ℝ) : IsUnit (nbarMat v) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_nbarMat]
  exact isUnit_one

/-- The element of `GL_n(ℝ)` with coordinates `v`. -/
def nbar (v : LowIdx n → ℝ) : Langlands.GeneralLinear n ℝ :=
  (isUnit_nbarMat v).unit

theorem nbar_val (v : LowIdx n → ℝ) :
    (nbar v : Matrix (Fin n) (Fin n) ℝ) = nbarMat v :=
  IsUnit.unit_spec _

/-- The inverse of `nbar v` is the adjugate of `nbarMat v`, since its determinant is `1`. -/
theorem nbar_inv_val (v : LowIdx n → ℝ) :
    (((nbar v)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      (nbarMat v).adjugate := by
  rw [Matrix.coe_units_inv, nbar_val, Matrix.inv_def, det_nbarMat, Ring.inverse_one, one_smul]

theorem nbar_mem_lowerUnipotent (v : LowIdx n → ℝ) : nbar v ∈ lowerUnipotent n ℝ := by
  rw [mem_lowerUnipotent_iff]
  have h := isLowerUnipotent_nbarMat v
  rw [← nbar_val] at h
  exact h

/-- Every lower unipotent element is `nbar v` for its entries `v` below the diagonal. -/
theorem exists_nbar_eq {L : Langlands.GeneralLinear n ℝ} (hL : L ∈ lowerUnipotent n ℝ) :
    ∃ v : LowIdx n → ℝ, nbar v = L := by
  rw [mem_lowerUnipotent_iff] at hL
  refine ⟨fun c => (L : Matrix (Fin n) (Fin n) ℝ) c.1.1 c.1.2, Units.ext ?_⟩
  rw [nbar_val]
  ext i j
  unfold nbarMat
  by_cases hji : j < i
  · rw [dite_eq_left hji]
  · rw [dite_eq_right hji]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      exact (hL.2 i).symm
    · rw [ite_eq_right hij]
      exact (hL.1 i j (lt_of_le_of_ne (not_lt.1 hji) hij)).symm

/-- A function of the real principal series vanishing at every `nbar v` is zero. -/
theorem eq_zero_of_nbar {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ n χ) (h0 : ∀ v : LowIdx n → ℝ, f (nbar v) = 0) : f = 0 :=
  eq_zero_of_eqOn_lowerUnipotent hf fun L hL => by
    obtain ⟨v, rfl⟩ := exists_nbar_eq hL
    exact h0 v

end RealLowerUnipotent

end Langlands.Archimedean
