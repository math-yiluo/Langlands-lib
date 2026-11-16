import Langlands.Representation.Archimedean.ComplexNoncompactFiltration

/-!
# The dimension of the filtration levels

Fix `i < r` in `Fin n`, the root element `rootUnit z = 1 + z E_{r,i}` and the root position
`(r, i)` among the coordinates of the lower unipotent group. Every lower unipotent element is
`rootUnit z · nbUnit (extCoords m)` with `m` the coordinates off the root position
(`exists_rootUnit_mul_eq`). On a block-polynomial function the slice
`z ↦ F(rootUnit z · g)` lies in the finite-dimensional space `bidegLT p q`, so it is determined
by finitely many values (a unisolvent set `S`). Hence `F ∈ filtrationLevel N` is determined by the
polynomials `m ↦ P_F(slice z m)` (`z ∈ S`), which have degree `≤ c (N + 1)` in the
`n(n-1) - 2` real coordinates `m`, and
`finrank (filtrationLevel N) ≤ |S| (c (N + 1) + 1)^{n(n-1) - 2}`
(`finrank_filtrationLevel_le`).
-/

noncomputable section

open scoped Matrix ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean.NoncompactPicture

open Langlands.GeneralLinear Langlands.Archimedean.RealPolynomialFunctions
open Langlands.Archimedean.BlockPolynomial

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The number of positions strictly below the diagonal. -/
theorem card_Lw_mul_two : Fintype.card (Lw n) * 2 = n * (n - 1) := by
  classical
  have h1 : Fintype.card (Lw n) = ∑ a : Fin n, (a : ℕ) := by
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  rw [h1, Fin.sum_univ_eq_sum_range (fun a => a) n, Finset.sum_range_id_mul_two]

theorem nbUnit_lowCoords {L : Langlands.GeneralLinear n ℂ} (hL : L ∈ lowerUnipotent n ℂ) :
    nbUnit (lowCoords (L : Matrix (Fin n) (Fin n) ℂ)) = L := by
  obtain ⟨hup, hdiag⟩ := (mem_lowerUnipotent_iff n ℂ L).1 hL
  refine Units.ext ?_
  ext a b
  simp only [nbUnit_val, nbMat, lowMat, lowCoords, Matrix.add_apply, Matrix.of_apply]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [Matrix.one_apply_ne (ne_of_lt h), dite_eq_right (not_lt.2 h.le), hup a b h, add_zero]
  · simp [hdiag]
  · rw [Matrix.one_apply_ne (ne_of_gt h), dite_eq_left h, zero_add]

variable {i r : Fin n} (hir : i ≠ r) (hlt : i < r)

include hlt in
theorem rootUnit_mem_lowerUnipotent (z : ℂ) : rootUnit hir z ∈ lowerUnipotent n ℂ := by
  refine (mem_lowerUnipotent_iff n ℂ _).2 ⟨fun a b hab => ?_, fun a => ?_⟩
  · simp only [rootUnit_val, rootMatrix, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hab),
      Matrix.single_apply, zero_add]
    rw [ite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hab hlt
  · simp only [rootUnit_val, rootMatrix, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.single_apply]
    rw [ite_eq_right, add_zero]
    rintro ⟨rfl, h⟩
    exact hir h

theorem rootUnit_mul_neg (z : ℂ) : rootUnit hir z * rootUnit hir (-z) = 1 :=
  Units.ext (rootMatrix_mul_neg hir z)

/-- The root position `(r, i)`. -/
def rootPos : Lw n := ⟨(r, i), hlt⟩

/-- The positions other than the root position. -/
abbrev LwRest := {p : Lw n // p ≠ rootPos hlt}

/-- Extension of coordinates by zero at the root position. -/
def extCoords (m : LwRest hlt → ℂ) : Lw n → ℂ :=
  fun p => if h : p = rootPos hlt then 0 else m ⟨p, h⟩

/-- The coordinates of `rootUnit z · nbUnit (extCoords m)`. -/
def slice (z : ℂ) (m : LwRest hlt → ℂ) : Lw n → ℂ :=
  lowCoords (rootMatrix i r z * nbMat (extCoords hlt m))

theorem nbUnit_slice (z : ℂ) (m : LwRest hlt → ℂ) :
    nbUnit (slice hlt z m) = rootUnit hir z * nbUnit (extCoords hlt m) := by
  have h := nbUnit_lowCoords (Subgroup.mul_mem _ (rootUnit_mem_lowerUnipotent hir hlt z)
    (nbUnit_mem_lowerUnipotent (extCoords hlt m)))
  rw [Units.val_mul, rootUnit_val, nbUnit_val] at h
  exact h

/-- **Every lower unipotent element is a root element times one with zero root entry.** -/
theorem exists_rootUnit_mul_eq {L : Langlands.GeneralLinear n ℂ} (hL : L ∈ lowerUnipotent n ℂ) :
    ∃ z m, rootUnit hir z * nbUnit (extCoords hlt m) = L := by
  set z := (L : Matrix (Fin n) (Fin n) ℂ) r i
  set L' := rootUnit hir (-z) * L
  have hL' : L' ∈ lowerUnipotent n ℂ :=
    Subgroup.mul_mem _ (rootUnit_mem_lowerUnipotent hir hlt _) hL
  have hdiag := ((mem_lowerUnipotent_iff n ℂ L).1 hL).2 i
  have hri : (L' : Matrix (Fin n) (Fin n) ℂ) r i = 0 := by
    simp only [L', Units.val_mul, rootUnit_val, rootMatrix, add_mul, one_mul, Matrix.add_apply,
      Matrix.single_mul_apply_same, hdiag, mul_one]
    ring
  refine ⟨z, fun p => lowCoords (L' : Matrix (Fin n) (Fin n) ℂ) p.1, ?_⟩
  have hext : extCoords hlt (fun p => lowCoords (L' : Matrix (Fin n) (Fin n) ℂ) p.1) =
      lowCoords (L' : Matrix (Fin n) (Fin n) ℂ) := by
    funext p
    by_cases hp : p = rootPos hlt
    · subst hp
      simp [extCoords, lowCoords, rootPos, hri]
    · simp [extCoords, hp]
  rw [hext, nbUnit_lowCoords hL', ← mul_assoc, rootUnit_mul_neg, one_mul]

/-! ## Polynomiality of the slices -/

theorem isPolyMat_nbMat_extCoords :
    IsPolyMat (ι := LwRest hlt) 1 (fun m => nbMat (extCoords hlt m)) := by
  intro a b
  by_cases h : b < a
  · by_cases hp : (⟨(a, b), h⟩ : Lw n) = rootPos hlt
    · have : (fun m : LwRest hlt → ℂ => nbMat (extCoords hlt m) a b) = fun _ => 0 := by
        funext m
        simp [nbMat, lowMat, Matrix.one_apply_ne (ne_of_gt h), h, extCoords, hp]
      rw [this]; exact Submodule.zero_mem _
    · have : (fun m : LwRest hlt → ℂ => nbMat (extCoords hlt m) a b) =
          coord (LwRest hlt) (⟨⟨(a, b), h⟩, hp⟩, false) := by
        funext m
        simp [nbMat, lowMat, Matrix.one_apply_ne (ne_of_gt h), h, extCoords, hp, coord]
      rw [this]; exact coord_mem_degLE _
  · have : (fun m : LwRest hlt → ℂ => nbMat (extCoords hlt m) a b) =
        fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
      funext m
      simp [nbMat, lowMat, h]
    rw [this]; exact const_mem_degLE _ 1

theorem coord_slice_mem (z : ℂ) (c : Lw n × Bool) :
    coord (Lw n) c ∘ slice hlt z ∈ degLE (LwRest hlt) 1 := by
  have hM := (isPolyMat_const (ι := LwRest hlt) (rootMatrix i r z) 0).mul
    (isPolyMat_nbMat_extCoords hlt)
  refine coord_comp_mem_degLE (fun p => ?_) c
  simpa [slice, lowCoords] using hM p.1.1 p.1.2

/-! ## Determination by slices -/

/-- A block-polynomial principal-series function vanishing on the slices through a unisolvent
set of root parameters is zero. -/
theorem eq_zero_of_slices {χ : ℕ → ℂˣ → ℂ} {p q : ℕ} {F : Langlands.GeneralLinear n ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ n χ) (hFb : IsBlockPoly hir p q F) (S : Finset ℂ)
    (hS : ∀ f ∈ bidegLT p q, (∀ x ∈ S, f x = 0) → f = 0)
    (h0 : ∀ z ∈ S, ∀ m, F (nbUnit (slice hlt z m)) = 0) : F = 0 := by
  have hall : ∀ z m, F (rootUnit hir z * nbUnit (extCoords hlt m)) = 0 := by
    intro z m
    have := hS _ (hFb (nbUnit (extCoords hlt m))) fun x hx => by
      rw [← nbUnit_slice hir hlt]
      exact h0 x hx m
    exact congrFun this z
  refine eq_zero_of_eqOn_lowerUnipotent hF fun L hL => ?_
  obtain ⟨z, m, rfl⟩ := exists_rootUnit_mul_eq hir hlt hL
  exact hall z m

/-! ## The dimension bound -/

variable {κ : Type*} [Fintype κ] (T : κ → (Lw n → ℂ) → ℂ) (σ : κ → ℂ)

theorem weight_ne_zero (hTpos : ∀ m, IsPosReal (T m)) (v : Lw n → ℂ) :
    (∏ m, T m v ^ σ m) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun m _ => by
    rw [Complex.cpow_def_of_ne_zero ((hTpos m).ne_zero v)]
    exact Complex.exp_ne_zero _

theorem gram_pow_ne_zero (hTpos : ∀ m, IsPosReal (T m)) (v : Lw n → ℂ) (N : ℕ) :
    (∏ m, T m v) ^ N ≠ 0 :=
  pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun m _ => (hTpos m).ne_zero v)

/-- The slice data `z, m ↦ F(slice z m) D^N / ω` of a function. -/
def sliceMap (S : Finset ℂ) (N : ℕ) :
    (Langlands.GeneralLinear n ℂ → ℂ) →ₗ[ℂ] (S → (LwRest hlt → ℂ) → ℂ) where
  toFun F z m := F (nbUnit (slice hlt z m)) * (∏ k, T k (slice hlt z m)) ^ N /
    (∏ k, T k (slice hlt z m) ^ σ k)
  map_add' F G := by
    funext z m
    simp only [Pi.add_apply]
    ring
  map_smul' a F := by
    funext z m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

variable (χ : ℕ → ℂˣ → ℂ) (p q c : ℕ)

include hlt in
/-- **The dimension bound.** For a unisolvent set `S` of the slice polynomials, the level `N`
is finite-dimensional of dimension `≤ |S| (c (N + 1) + 1)^{n(n-1) - 2}`. -/
theorem finrank_filtrationLevel_le (hTpos : ∀ m, IsPosReal (T m)) (S : Finset ℂ)
    (hS : ∀ f ∈ bidegLT p q, (∀ x ∈ S, f x = 0) → f = 0) (N : ℕ) :
    FiniteDimensional ℂ (filtrationLevel χ hir p q T σ c N) ∧
      Module.finrank ℂ (filtrationLevel χ hir p q T σ c N) ≤
        S.card * (c * (N + 1) + 1) ^ (n * (n - 1) - 2) := by
  set W := filtrationLevel χ hir p q T σ c N
  have hmem : ∀ F : W, ∀ z : S,
      sliceMap hlt T σ S N (F : Langlands.GeneralLinear n ℂ → ℂ) z ∈
        degLE (LwRest hlt) (c * (N + 1)) := by
    rintro ⟨F, hF1, hF2, P, hP, hPe⟩ z
    have h : sliceMap hlt T σ S N F z = P ∘ slice hlt z := by
      funext m
      simp only [sliceMap, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
      rw [hPe, mul_div_cancel_left₀ _ (weight_ne_zero T σ hTpos _)]
    rw [h]
    simpa using comp_mem_degLE hP (coord_slice_mem hlt z)
  let Φ : W →ₗ[ℂ] (S → degLE (LwRest hlt) (c * (N + 1))) :=
    LinearMap.pi fun z => LinearMap.codRestrict (degLE (LwRest hlt) (c * (N + 1)))
      ((LinearMap.proj z).comp ((sliceMap hlt T σ S N).comp W.subtype)) fun F => hmem F z
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun F hF => ?_
    obtain ⟨hF1, hF2, -⟩ := F.2
    refine Subtype.ext (eq_zero_of_slices hir hlt hF1 hF2 S hS fun z hz m => ?_)
    have h1 := congrArg (fun G => ((G ⟨z, hz⟩ : degLE (LwRest hlt) (c * (N + 1))) :
      (LwRest hlt → ℂ) → ℂ) m) hF
    simp only [Φ, LinearMap.pi_apply, LinearMap.codRestrict_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.proj_apply, Submodule.coe_subtype, Pi.zero_apply,
      Submodule.coe_zero, sliceMap, LinearMap.coe_mk, AddHom.coe_mk] at h1
    rcases div_eq_zero_iff.1 h1 with h2 | h2
    · exact (mul_eq_zero.1 h2).resolve_right (gram_pow_ne_zero T hTpos _ N)
    · exact absurd h2 (weight_ne_zero T σ hTpos _)
  have hfd : FiniteDimensional ℂ W := Module.Finite.of_injective Φ hinj
  refine ⟨hfd, (LinearMap.finrank_le_finrank_of_injective hinj).trans ?_⟩
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    smul_eq_mul]
  refine Nat.mul_le_mul_left _ ((finrank_degLE_le _).trans (Nat.pow_le_pow_right
    (Nat.succ_pos _) (le_of_eq ?_)))
  rw [Fintype.card_prod, Fintype.card_bool]
  have hcard : Fintype.card (LwRest hlt) = Fintype.card (Lw n) - 1 := by
    simp [LwRest, Fintype.card_subtype_compl]
  rw [hcard]
  have h2 := card_Lw_mul_two (n := n)
  have h1 : 1 ≤ Fintype.card (Lw n) := Fintype.card_pos_iff.2 ⟨rootPos hlt⟩
  rw [← h2, Nat.sub_mul]
end Langlands.Archimedean.NoncompactPicture
