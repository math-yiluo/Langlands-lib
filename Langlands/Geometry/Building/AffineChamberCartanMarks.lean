import Langlands.Geometry.Building.AffineChamberFaceExistence
import Langlands.Geometry.Building.AffineFacetTransport
import Langlands.Geometry.Building.AffineRootSystemTransport

/-!
# The Cartan matrix and the marks of the simple affine roots of a chamber

For an affine root system `Ψ` (rank zero allowed) and a chamber `C`, the Cartan matrix of
the simple affine roots of `C` has entries `ψ̇(η̇∨)`. These are integers by AR 3. The matrix
is a generalized Cartan matrix: its diagonal entries are `2`, its off-diagonal entries are
nonpositive and its zero pattern is symmetric. It also has a left-kernel vector with
strictly positive integer entries, the marks (KP Proposition 1.3.47).
-/

noncomputable section

universe uV uA uW uB

namespace Langlands.Geometry.Building.AffineRootSystem

open Matrix GalleryGeometry

/-! ### Rational linear algebra -/

section LinearAlgebra

variable {ι : Type*} [Fintype ι]

/-- Clearing denominators of a rational vector. -/
theorem exists_nat_mul_eq_intCast (y : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : ι → ℤ, ∀ j, (z j : ℚ) = N * y j := by
  classical
  refine ⟨∏ k, (y k).den, Finset.prod_pos fun k _ => (y k).den_pos,
    fun j => (∏ k ∈ Finset.univ.erase j, ((y k).den : ℤ)) * (y j).num, fun j => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun k => (y k).den) (Finset.mem_univ j)]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

/-- If no rational vector `x` has `M x` equal to the `i`-th standard basis vector, some
rational left-kernel vector of `M` has nonzero `i`-th coordinate. -/
theorem exists_vecMul_eq_zero_apply_ne_zero [DecidableEq ι] (M : Matrix ι ι ℚ) (i : ι)
    (h : ∀ x : ι → ℚ, M *ᵥ x ≠ fun k => if i = k then 1 else 0) :
    ∃ y : ι → ℚ, y ᵥ* M = 0 ∧ y i ≠ 0 := by
  have hnot : (fun k => if i = k then (1 : ℚ) else 0) ∉ LinearMap.range M.mulVecLin := by
    rintro ⟨x, hx⟩
    exact h x hx
  obtain ⟨φ, hφi, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  let y : ι → ℚ := fun j => φ fun k => if j = k then 1 else 0
  have hφapply : ∀ z : ι → ℚ, φ z = y ⬝ᵥ z := by
    intro z
    rw [LinearMap.pi_apply_eq_sum_univ φ z]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul, mul_comm]
  refine ⟨y, ?_, hφi⟩
  have hzero : ∀ x : ι → ℚ, y ⬝ᵥ (M *ᵥ x) = 0 := by
    intro x
    have hmem : φ (M *ᵥ x) ∈ (LinearMap.range M.mulVecLin).map φ :=
      ⟨M *ᵥ x, ⟨x, rfl⟩, rfl⟩
    rw [hφ, Submodule.mem_bot] at hmem
    rw [← hφapply]
    exact hmem
  funext k
  have hk := hzero fun l => if k = l then 1 else 0
  rw [dotProduct_mulVec] at hk
  simpa [dotProduct] using hk

/-- A Stiemke-type alternative for integer matrices whose rational left kernel is closed
under absolute values: if `M x ≥ 0` forces `M x = 0`, then `M` has a left-kernel vector with
strictly positive integer entries. -/
theorem exists_pos_int_vecMul_eq_zero (M : Matrix ι ι ℤ)
    (habs : ∀ y : ι → ℚ, y ᵥ* M.map (Int.cast : ℤ → ℚ) = 0 →
      (fun j => |y j|) ᵥ* M.map (Int.cast : ℤ → ℚ) = 0)
    (hgeom : ∀ x : ι → ℚ, (∀ j, 0 ≤ (M.map (Int.cast : ℤ → ℚ) *ᵥ x) j) →
      M.map (Int.cast : ℤ → ℚ) *ᵥ x = 0) :
    ∃ m : ι → ℤ, (∀ j, 0 < m j) ∧ m ᵥ* M = 0 := by
  classical
  set M' := M.map (Int.cast : ℤ → ℚ) with hM'
  have hy : ∀ i, ∃ y : ι → ℚ, y ᵥ* M' = 0 ∧ y i ≠ 0 := by
    intro i
    refine exists_vecMul_eq_zero_apply_ne_zero M' i fun x hx => ?_
    have h0 := hgeom x (by
      intro j
      rw [hx]
      show 0 ≤ (if i = j then (1 : ℚ) else 0)
      split_ifs <;> norm_num)
    have := congrFun (hx.symm.trans h0) i
    simp at this
  choose y hy0 hyi using hy
  set m' : ι → ℚ := fun j => ∑ i, |y i j| with hm'
  have hm'pos : ∀ j, 0 < m' j := fun j =>
    lt_of_lt_of_le (abs_pos.2 (hyi j))
      (Finset.single_le_sum (f := fun i => |y i j|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ j))
  have hm'ker : m' ᵥ* M' = 0 := by
    funext k
    have h := fun i => congrFun (habs (y i) (hy0 i)) k
    simp only [vecMul, dotProduct, Pi.zero_apply] at h ⊢
    simp only [hm', Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => h i
  obtain ⟨N, hN, z, hz⟩ := exists_nat_mul_eq_intCast m'
  refine ⟨z, fun j => ?_, ?_⟩
  · have : (0 : ℚ) < z j := by
      rw [hz j]
      exact mul_pos (by exact_mod_cast hN) (hm'pos j)
    exact_mod_cast this
  · funext k
    have hk := congrFun hm'ker k
    simp only [vecMul, dotProduct, Pi.zero_apply] at hk ⊢
    have : ((∑ j, z j * M j k : ℤ) : ℚ) = 0 := by
      push_cast
      simp only [hz, hM', Matrix.map_apply] at hk ⊢
      rw [show (∑ j, (N : ℚ) * m' j * (M j k : ℚ)) = N * ∑ j, m' j * (M j k : ℚ) by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring]
      rw [hk, mul_zero]
    exact_mod_cast this

end LinearAlgebra

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-! ### Coroot vectors and the Cartan matrix -/

open Classical in
/-- A coroot vector of `ψ` in the sense of AR 2, chosen when one exists, and `0` otherwise. -/
def corootVector (Ψ : Set (A →ᵃ[ℝ] ℝ)) (ψ : A →ᵃ[ℝ] ℝ) : V :=
  if h : ∃ v, IsCoroot Ψ ψ v then h.choose else 0

theorem isCoroot_corootVector {Ψ : Set (A →ᵃ[ℝ] ℝ)} {ψ : A →ᵃ[ℝ] ℝ}
    (h : ∃ v, IsCoroot Ψ ψ v) : IsCoroot Ψ ψ (corootVector Ψ ψ) := by
  classical
  simp only [corootVector, h, dite_true]
  exact h.choose_spec

/-- The Cartan matrix of the simple affine roots of `C` (KP Construction 1.3.64): its entry
at `(ψ, η)` is the integer part of `ψ̇(η̇∨)`, which is an integer by AR 3. -/
def chamberCartanMatrix (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) :
    Matrix (simpleAffineRoots Ψ C) (simpleAffineRoots Ψ C) ℤ :=
  fun ψ η => ⌊(ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ))⌋

namespace IsAffineRootSystemWithRankZero

variable {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)

include hΨ

theorem isCoroot_corootVector_of_mem {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) :
    IsCoroot Ψ ψ (corootVector Ψ ψ) :=
  isCoroot_corootVector (hΨ.exists_isCoroot ψ hψ)

/-- The chosen coroot vector is the coroot vector. -/
theorem corootVector_eq {ψ : A →ᵃ[ℝ] ℝ} {v : V} (hv : IsCoroot Ψ ψ v) :
    corootVector Ψ ψ = v :=
  (hΨ.coroot_eq_of_linear_eq hv (isCoroot_corootVector ⟨v, hv⟩) rfl).symm

theorem cast_chamberCartanMatrix {C : Set A} (ψ η : simpleAffineRoots Ψ C) :
    (chamberCartanMatrix Ψ C ψ η : ℝ) =
      (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) := by
  obtain ⟨n, hn⟩ := hΨ.coroot_integral _ ψ.2.1.1 _ η.2.1.1 _
    (hΨ.isCoroot_corootVector_of_mem η.2.1.1)
  show ((⌊(ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ))⌋ : ℤ) : ℝ) = _
  rw [hn, Int.floor_intCast]

/-- The diagonal entries are `2`. -/
theorem chamberCartanMatrix_self {C : Set A} (ψ : simpleAffineRoots Ψ C) :
    chamberCartanMatrix Ψ C ψ ψ = 2 := by
  have h := hΨ.cast_chamberCartanMatrix ψ ψ
  rw [(hΨ.isCoroot_corootVector_of_mem ψ.2.1.1).1] at h
  exact_mod_cast h

/-- The reflection identity `2 β(ψ̇, η̇) = ψ̇(η̇∨) β(η̇, η̇)` for the Cartan entries. -/
theorem two_mul_corootForm_eq_chamberCartanMatrix {C : Set A}
    (ψ η : simpleAffineRoots Ψ C) :
    2 * hΨ.corootForm (ψ : A →ᵃ[ℝ] ℝ).linear (η : A →ᵃ[ℝ] ℝ).linear =
      (chamberCartanMatrix Ψ C ψ η : ℝ) *
        hΨ.corootForm (η : A →ᵃ[ℝ] ℝ).linear (η : A →ᵃ[ℝ] ℝ).linear := by
  rw [hΨ.cast_chamberCartanMatrix]
  exact hΨ.two_mul_corootForm (hΨ.isCoroot_corootVector_of_mem η.2.1.1) _

theorem chamberCartanMatrix_eq_zero_iff_corootForm {C : Set A}
    (ψ η : simpleAffineRoots Ψ C) :
    chamberCartanMatrix Ψ C ψ η = 0 ↔
      hΨ.corootForm (ψ : A →ᵃ[ℝ] ℝ).linear (η : A →ᵃ[ℝ] ℝ).linear = 0 := by
  have h := hΨ.two_mul_corootForm_eq_chamberCartanMatrix ψ η
  have hpos := hΨ.corootForm_self_pos η.2.1.1
  constructor
  · intro h0
    rw [h0, Int.cast_zero, zero_mul] at h
    linarith
  · intro h0
    rw [h0, mul_zero, eq_comm, mul_eq_zero] at h
    exact_mod_cast h.resolve_right hpos.ne'

/-- The zero pattern of the Cartan matrix is symmetric. -/
theorem chamberCartanMatrix_eq_zero_iff {C : Set A} (ψ η : simpleAffineRoots Ψ C) :
    chamberCartanMatrix Ψ C ψ η = 0 ↔ chamberCartanMatrix Ψ C η ψ = 0 := by
  rw [hΨ.chamberCartanMatrix_eq_zero_iff_corootForm,
    hΨ.chamberCartanMatrix_eq_zero_iff_corootForm, hΨ.corootForm_comm]

theorem corootForm_smul_smul (r r' : ℝ) (α α' : Module.Dual ℝ V) :
    hΨ.corootForm (r • α) (r' • α') = r * r' * hΨ.corootForm α α' := by
  unfold corootForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Two simple affine roots of the same chamber that are positive multiples of each other
are equal. AR 3 leaves the ratios `1/2`, `1` and `2`, and the first and last are excluded
by indivisibility. -/
theorem eq_of_mem_simpleAffineRoots_of_eq_smul {C : Set A} {ψ η : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ C) (hη : η ∈ simpleAffineRoots Ψ C) {r : ℝ}
    (hr : 0 < r) (h : η = r • ψ) : η = ψ := by
  obtain ⟨u, hu⟩ := hΨ.exists_isCoroot ψ hψ.1.1
  have hu' : IsCoroot Ψ η (r⁻¹ • u) := by
    refine ⟨?_, fun ζ hζ => ?_⟩
    · rw [h, AffineMap.smul_linear, LinearMap.smul_apply, map_smul, hu.1, smul_eq_mul,
        smul_eq_mul]
      field_simp
    · have := hu.2 ζ hζ
      convert this using 2
      rw [h, map_smul, smul_eq_mul, smul_smul]
      congr 1
      field_simp
  obtain ⟨n₁, hn₁⟩ := hΨ.coroot_integral η hη.1.1 ψ hψ.1.1 u hu
  obtain ⟨n₂, hn₂⟩ := hΨ.coroot_integral ψ hψ.1.1 η hη.1.1 _ hu'
  have h1 : (n₁ : ℝ) = 2 * r := by
    rw [← hn₁, h, AffineMap.smul_linear, LinearMap.smul_apply, hu.1, smul_eq_mul]
    ring
  have h2 : (n₂ : ℝ) = 2 * r⁻¹ := by
    rw [← hn₂, map_smul, hu.1, smul_eq_mul]
    ring
  have h12 : n₁ * n₂ = 4 := by
    have : (n₁ : ℝ) * n₂ = 4 := by
      rw [h1, h2]
      field_simp
      ring
    exact_mod_cast this
  have hn₁pos : 0 < n₁ := by
    have : (0 : ℝ) < n₁ := by rw [h1]; positivity
    exact_mod_cast this
  have hn₂pos : 0 < n₂ := by
    have : (0 : ℝ) < n₂ := by rw [h2]; positivity
    exact_mod_cast this
  have hn₁le : n₁ ≤ 4 := by nlinarith
  interval_cases n₁
  · exfalso
    apply hψ.2.1.2
    have hr' : r = 1 / 2 := by push_cast at h1; linarith
    have : (2 : ℝ)⁻¹ • ψ = η := by rw [h, hr']; norm_num
    rw [this]
    exact hη.1.1
  · have hr' : r = 1 := by push_cast at h1; linarith
    rw [h, hr', one_smul]
  · omega
  · exfalso
    apply hη.2.1.2
    have hr' : r = 2 := by push_cast at h1; linarith
    rw [h, hr', smul_smul]
    norm_num
    exact hψ.1.1

variable {c : A}

/-- The off-diagonal entries are nonpositive. -/
theorem chamberCartanMatrix_nonpos (hc : IsRegular Ψ c)
    {ψ η : simpleAffineRoots Ψ (facet Ψ c)} (hne : ψ ≠ η) :
    chamberCartanMatrix Ψ (facet Ψ c) ψ η ≤ 0 := by
  obtain ⟨s, r, hr, hψs⟩ := hΨ.exists_eq_smul_chamberSimpleRoot ψ.2
  obtain ⟨t, r', hr', hηt⟩ := hΨ.exists_eq_smul_chamberSimpleRoot η.2
  have hst : s ≠ t := by
    rintro rfl
    apply hne
    apply Subtype.ext
    have : (ψ : A →ᵃ[ℝ] ℝ) = (r / r') • (η : A →ᵃ[ℝ] ℝ) := by
      rw [hψs, hηt, smul_smul, div_mul_cancel₀ _ hr'.ne']
    exact hΨ.eq_of_mem_simpleAffineRoots_of_eq_smul η.2 ψ.2 (div_pos hr hr') this
  have hG := hΨ.chamberSimpleGram_nonpos hc hst
  have hform : hΨ.corootForm (ψ : A →ᵃ[ℝ] ℝ).linear (η : A →ᵃ[ℝ] ℝ).linear =
      r * r' * hΨ.chamberSimpleGram s t := by
    rw [hψs, hηt, AffineMap.smul_linear, AffineMap.smul_linear, corootForm_smul_smul]
    rfl
  have h := hΨ.two_mul_corootForm_eq_chamberCartanMatrix ψ η
  have hpos := hΨ.corootForm_self_pos η.2.1.1
  have hrr : 0 < r * r' := mul_pos hr hr'
  have hβ : hΨ.corootForm (ψ : A →ᵃ[ℝ] ℝ).linear (η : A →ᵃ[ℝ] ℝ).linear ≤ 0 := by
    rw [hform]
    exact mul_nonpos_of_nonneg_of_nonpos hrr.le hG
  have : (chamberCartanMatrix Ψ (facet Ψ c) ψ η : ℝ) ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  exact_mod_cast this

/-- No nonzero vector is nonnegative on all simple affine roots of a chamber: otherwise the
ray from a point of the chamber in that direction stays in the chamber, which forces all
roots with a given derivative to have values of one sign there and contradicts AR 4. -/
theorem eq_zero_of_forall_simpleAffineRoots_linear_nonneg (hc : IsRegular Ψ c) {v : V}
    (hv : ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), 0 ≤ ψ.linear v) : v = 0 := by
  by_contra hv0
  obtain ⟨ζ, hζ, hζv⟩ : ∃ ζ ∈ Ψ, ζ.linear v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hv0
    rw [← Module.forall_dual_apply_eq_zero_iff ℝ v]
    intro φ
    have hφ : φ ∈ Submodule.span ℝ (derivativeRoots Ψ) := by
      rw [hΨ.span_derivativeRoots_eq_top]
      exact Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ζ, hζ, rfl⟩ := hx
      exact hall ζ hζ
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  obtain ⟨ξ₀, hξ₀, hξ₀v⟩ : ∃ ξ₀ ∈ Ψ, ξ₀.linear v < 0 := by
    rcases lt_or_gt_of_ne hζv with h | h
    · exact ⟨ζ, hζ, h⟩
    · refine ⟨-ζ, hΨ.neg_mem hζ, ?_⟩
      rw [AffineMap.neg_linear, LinearMap.neg_apply]
      linarith
  have hray : ∀ t : ℝ, 0 ≤ t → facetRel Ψ c (t • v +ᵥ c) := by
    intro t ht
    rw [facetRel_iff_simple_pos hΨ hc]
    intro ψ hψ
    rw [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
    have h1 := pos_of_mem_simpleAffineRoots hψ (mem_facet_self Ψ c)
    have h2 := hv ψ hψ
    positivity
  have hneg : ∀ ξ ∈ Ψ, ξ.linear = ξ₀.linear → ξ c < 0 := by
    intro ξ hξ hlin
    have hξc := hc ξ hξ
    by_contra hcon
    push Not at hcon
    have hpos : 0 < ξ c := lt_of_le_of_ne hcon (Ne.symm hξc)
    have ht : 0 ≤ ξ c / (-ξ₀.linear v) + 1 := by
      have : 0 < -ξ₀.linear v := by linarith
      positivity
    have hsign := hray _ ht ξ hξ
    rw [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, hlin] at hsign
    have hlt : (ξ c / (-ξ₀.linear v) + 1) * ξ₀.linear v + ξ c < 0 := by
      have hne : ξ₀.linear v ≠ 0 := hξ₀v.ne
      have : ξ c / (-ξ₀.linear v) * ξ₀.linear v = -ξ c := by
        rw [div_neg, neg_mul, div_mul_cancel₀ _ hne]
      nlinarith
    rw [sign_pos hpos, sign_neg hlt] at hsign
    exact absurd hsign (by decide)
  obtain ⟨u₀, hu₀⟩ := hΨ.exists_isCoroot ξ₀ hξ₀
  have h0 := hneg ξ₀ hξ₀ rfl
  have hsub : {ξ | ξ ∈ Ψ ∧ ξ.linear = ξ₀.linear} ⊆
      {ξ | ξ ∈ Ψ ∧ ξ.linear = ξ₀.linear ∧ ∀ x : A, |ξ x - ξ₀ x| ≤ |ξ₀ c|} := by
    rintro ξ ⟨hξ, hlin⟩
    refine ⟨hξ, hlin, fun x => ?_⟩
    have hξu : ξ.linear u₀ = 2 := by rw [hlin]; exact hu₀.1
    have hrefl : -(ξ - ξ.linear u₀ • ξ₀) ∈ Ψ := hΨ.neg_mem (hu₀.2 ξ hξ)
    have hlin' : (-(ξ - ξ.linear u₀ • ξ₀)).linear = ξ₀.linear := by
      rw [AffineMap.neg_linear, AffineMap.sub_linear, AffineMap.smul_linear, hξu, hlin,
        two_smul]
      abel
    have h1 := hneg ξ hξ hlin
    have h2 := hneg _ hrefl hlin'
    have hξ'c : (-(ξ - ξ.linear u₀ • ξ₀)) c = 2 * ξ₀ c - ξ c := by
      rw [hξu]
      simp only [AffineMap.coe_neg, AffineMap.coe_sub, AffineMap.coe_smul, Pi.neg_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hξ'c] at h2
    have hconst : ξ x - ξ₀ x = ξ c - ξ₀ c := by
      have := apply_eq_apply_of_linear_eq_zero (f := ξ - ξ₀)
        (by rw [AffineMap.sub_linear, hlin, sub_self]) x c
      simpa using this
    rw [hconst, abs_le, abs_of_neg h0]
    constructor <;> linarith
  exact (hΨ.infinite_fiber ξ₀ hξ₀) ((hΨ.finite_bounded ξ₀ hξ₀ |ξ₀ c|).subset hsub)

/-- Real left-kernel vectors of the Cartan matrix stay in the left kernel after taking
absolute values (the Perron–Frobenius step, through the coroot form). -/
theorem abs_mem_leftKernel (hc : IsRegular Ψ c) [Fintype (simpleAffineRoots Ψ (facet Ψ c))]
    (y : simpleAffineRoots Ψ (facet Ψ c) → ℝ)
    (hy : ∀ η : simpleAffineRoots Ψ (facet Ψ c),
      ∑ ψ, y ψ * (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0)
    (η : simpleAffineRoots Ψ (facet Ψ c)) :
    ∑ ψ, |y ψ| * (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0 := by
  let f : simpleAffineRoots Ψ (facet Ψ c) → Module.Dual ℝ V :=
    fun ψ => (ψ : A →ᵃ[ℝ] ℝ).linear
  let g : Module.Dual ℝ V := ∑ ψ, y ψ • f ψ
  have hg : ∀ w, g w = ∑ ψ, y ψ * f ψ w := by
    intro w
    simp [g, LinearMap.sum_apply]
  have hgη : ∀ η : simpleAffineRoots Ψ (facet Ψ c),
      hΨ.corootForm (η : A →ᵃ[ℝ] ℝ).linear g = 0 := by
    intro η
    have h := hΨ.two_mul_corootForm (hΨ.isCoroot_corootVector_of_mem η.2.1.1) g
    rw [hg, hy η, zero_mul, hΨ.corootForm_comm] at h
    linarith
  have hgg : hΨ.corootForm g g = 0 := by
    have : hΨ.corootForm g g = ∑ ψ, y ψ * hΨ.corootForm (f ψ) g := by
      unfold corootForm
      calc ∑ v ∈ hΨ.finite_corootSet.toFinset, g v * g v
          = ∑ v ∈ hΨ.finite_corootSet.toFinset, ∑ ψ, y ψ * (f ψ v * g v) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            calc g v * g v = (∑ ψ, y ψ * f ψ v) * g v := by rw [← hg v]
              _ = ∑ ψ, y ψ * (f ψ v * g v) := by
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun _ _ => by ring
        _ = ∑ ψ, y ψ * ∑ v ∈ hΨ.finite_corootSet.toFinset, f ψ v * g v := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]
    rw [this]
    exact Finset.sum_eq_zero fun ψ _ => by rw [hgη ψ, mul_zero]
  have hiso : IsIsotropicCombination f hΨ.finite_corootSet.toFinset y := by
    intro w hw
    rw [← hg]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => mul_self_nonneg (g v))).1 hgg w hw
    exact mul_self_eq_zero.1 this
  have hG : ∀ ψ η : simpleAffineRoots Ψ (facet Ψ c), ψ ≠ η →
      combinationGram f hΨ.finite_corootSet.toFinset ψ η ≤ 0 := by
    intro ψ η hne
    have h := hΨ.two_mul_corootForm_eq_chamberCartanMatrix ψ η
    have hA : (chamberCartanMatrix Ψ (facet Ψ c) ψ η : ℝ) ≤ 0 := by
      exact_mod_cast hΨ.chamberCartanMatrix_nonpos hc hne
    have hpos := hΨ.corootForm_self_pos η.2.1.1
    show hΨ.corootForm _ _ ≤ 0
    nlinarith
  exact hiso.abs hG _ (hΨ.finite_corootSet.mem_toFinset.2
    ⟨η, η.2.1.1, hΨ.isCoroot_corootVector_of_mem η.2.1.1⟩)

/-- The marks (KP Proposition 1.3.47, as corrected): the Cartan matrix of the simple affine
roots of a chamber has a left-kernel vector with strictly positive integer entries. -/
theorem exists_pos_vecMul_chamberCartanMatrix_eq_zero (hc : IsRegular Ψ c)
    [Fintype (simpleAffineRoots Ψ (facet Ψ c))] :
    ∃ m : simpleAffineRoots Ψ (facet Ψ c) → ℤ, (∀ i, 0 < m i) ∧
      m ᵥ* chamberCartanMatrix Ψ (facet Ψ c) = 0 := by
  classical
  apply exists_pos_int_vecMul_eq_zero
  · intro y hy
    have hyR : ∀ η : simpleAffineRoots Ψ (facet Ψ c),
        ∑ ψ, (y ψ : ℝ) * (ψ : A →ᵃ[ℝ] ℝ).linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ)) = 0 := by
      intro η
      have hη := congrFun hy η
      simp only [vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply] at hη
      have hR : ((∑ ψ, y ψ * (chamberCartanMatrix Ψ (facet Ψ c) ψ η : ℚ) : ℚ) : ℝ) = 0 := by
        rw [hη, Rat.cast_zero]
      push_cast at hR
      simpa only [hΨ.cast_chamberCartanMatrix] using hR
    funext η
    have h := hΨ.abs_mem_leftKernel hc (fun ψ => (y ψ : ℝ)) hyR η
    simp only [vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply]
    have hR : ((∑ ψ, |y ψ| * (chamberCartanMatrix Ψ (facet Ψ c) ψ η : ℚ) : ℚ) : ℝ) = 0 := by
      push_cast
      simpa only [hΨ.cast_chamberCartanMatrix] using h
    exact_mod_cast hR
  · intro x hx
    let v : V := ∑ η, (x η : ℝ) • corootVector Ψ (η : A →ᵃ[ℝ] ℝ)
    have hv : ∀ ψ : simpleAffineRoots Ψ (facet Ψ c), (ψ : A →ᵃ[ℝ] ℝ).linear v =
        (((chamberCartanMatrix Ψ (facet Ψ c)).map (Int.cast : ℤ → ℚ) *ᵥ x) ψ : ℚ) := by
      intro ψ
      simp only [v, map_sum, map_smul, smul_eq_mul, mulVec, dotProduct, Matrix.map_apply]
      push_cast
      exact Finset.sum_congr rfl fun η _ => by rw [hΨ.cast_chamberCartanMatrix, mul_comm]
    have hv0 : v = 0 := hΨ.eq_zero_of_forall_simpleAffineRoots_linear_nonneg hc fun ψ hψ => by
      have := hv ⟨ψ, hψ⟩
      rw [this]
      exact_mod_cast hx ⟨ψ, hψ⟩
    funext ψ
    have := hv ψ
    rw [hv0, map_zero] at this
    exact_mod_cast this.symm

/-- The Cartan matrix of the simple affine roots of a chamber is a generalized Cartan matrix
with a strictly positive integral left-kernel vector. -/
theorem chamberCartanMatrix_spec {C : Set A} (hC : IsChamber Ψ C)
    [Fintype (simpleAffineRoots Ψ C)] :
    (∀ i, chamberCartanMatrix Ψ C i i = 2) ∧
      (∀ i j, i ≠ j → chamberCartanMatrix Ψ C i j ≤ 0) ∧
      (∀ i j, chamberCartanMatrix Ψ C i j = 0 ↔ chamberCartanMatrix Ψ C j i = 0) ∧
      ∃ m : simpleAffineRoots Ψ C → ℤ, (∀ i, 0 < m i) ∧ m ᵥ* chamberCartanMatrix Ψ C = 0 := by
  obtain ⟨c, hc, rfl⟩ := hC
  exact ⟨hΨ.chamberCartanMatrix_self, fun _ _ h => hΨ.chamberCartanMatrix_nonpos hc h,
    hΨ.chamberCartanMatrix_eq_zero_iff, hΨ.exists_pos_vecMul_chamberCartanMatrix_eq_zero hc⟩

end IsAffineRootSystemWithRankZero

/-! ### Transport along affine equivalences -/

section Transport

variable {W : Type uW} {B : Type uB} [AddCommGroup W] [Module ℝ W] [AddTorsor W B]

/-- Root transport preserves and reflects the face relation. -/
theorem isFaceOf_image_iff_transportedRoots (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (Fa Fa' : Set A) :
    IsFaceOf (transportedRoots e Ψ) (e '' Fa) (e '' Fa') ↔ IsFaceOf Ψ Fa Fa' := by
  constructor
  · rintro ⟨hFa, y, hy, hsub⟩
    refine ⟨(isFacet_image_transportedRoots_iff e Ψ Fa).1 hFa, e.symm y, ?_, ?_⟩
    · apply e.injective.image_injective
      rw [image_facet_transportedRoots, e.apply_symm_apply, hy]
    · apply (Set.image_subset_image_iff e.injective).1
      rw [image_facetClosure_transportedRoots, e.apply_symm_apply]
      exact hsub
  · rintro ⟨hFa, x, hx, hsub⟩
    refine ⟨(isFacet_image_transportedRoots_iff e Ψ Fa).2 hFa, e x, ?_, ?_⟩
    · rw [← image_facet_transportedRoots, hx]
    · rw [← image_facetClosure_transportedRoots]
      exact Set.image_mono hsub

theorem image_symm_image_affineEquiv (e : A ≃ᵃ[ℝ] B) (s : Set B) : e '' (e.symm '' s) = s :=
  e.toEquiv.image_symm_image s

/-- Root transport preserves and reflects chamber walls. -/
theorem isChamberWall_transportedRoots_iff (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ))
    (C : Set A) (H : AffineSubspace ℝ A) :
    IsChamberWall (transportedRoots e Ψ) (e '' C) (H.map (e : A →ᵃ[ℝ] B)) ↔
      IsChamberWall Ψ C H := by
  have hmapinj : ∀ H₁ H₂ : AffineSubspace ℝ A,
      H₁.map (e : A →ᵃ[ℝ] B) = H₂.map (e : A →ᵃ[ℝ] B) → H₁ = H₂ := by
    intro H₁ H₂ h
    ext x
    rw [← AffineSubspace.mem_map_iff_mem_of_injective (f := (e : A →ᵃ[ℝ] B)) e.injective, h,
      AffineSubspace.mem_map_iff_mem_of_injective e.injective]
  constructor
  · rintro ⟨hC, ⟨_, ⟨ψ, hψ, rfl⟩, hlin, hH⟩, Fb, hFb, hspan⟩
    refine ⟨(isChamber_image_transportedRoots_iff e Ψ C).1 hC, ⟨ψ, hψ, ?_, ?_⟩,
      e.symm '' Fb, ?_, ?_⟩
    · intro h0
      apply hlin
      rw [linear_affineFunctionalTransport, h0, map_zero]
    · apply hmapinj
      rw [hH, hyperplane_affineFunctionalTransport]
    · rw [← isFaceOf_image_iff_transportedRoots e, image_symm_image_affineEquiv]
      exact hFb
    · apply hmapinj
      rw [AffineSubspace.map_span, AffineEquiv.coe_coe, image_symm_image_affineEquiv]
      exact hspan
  · rintro ⟨hC, ⟨ψ, hψ, hlin, rfl⟩, Fa, hFa, hspan⟩
    refine ⟨(isChamber_image_transportedRoots_iff e Ψ C).2 hC,
      ⟨affineFunctionalTransport e ψ, ⟨ψ, hψ, rfl⟩, ?_,
        (hyperplane_affineFunctionalTransport e ψ).symm⟩,
      e '' Fa, (isFaceOf_image_iff_transportedRoots e Ψ Fa C).2 hFa, ?_⟩
    · intro h0
      apply hlin
      rw [linear_affineFunctionalTransport] at h0
      exact (derivativeTransport e).map_eq_zero_iff.1 h0
    · rw [← AffineEquiv.coe_coe, ← AffineSubspace.map_span, hspan]

theorem affineFunctionalTransport_mem_transportedRoots (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (ψ : A →ᵃ[ℝ] ℝ) :
    affineFunctionalTransport e ψ ∈ transportedRoots e Ψ ↔ ψ ∈ Ψ :=
  (affineFunctionalTransport e).injective.mem_set_image

/-- Root transport preserves and reflects simple affine roots of a chamber. -/
theorem affineFunctionalTransport_mem_simpleAffineRoots_iff (e : A ≃ᵃ[ℝ] B)
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) (ψ : A →ᵃ[ℝ] ℝ) :
    affineFunctionalTransport e ψ ∈ simpleAffineRoots (transportedRoots e Ψ) (e '' C) ↔
      ψ ∈ simpleAffineRoots Ψ C := by
  have hsmul : (2 : ℝ)⁻¹ • affineFunctionalTransport e ψ =
      affineFunctionalTransport e ((2 : ℝ)⁻¹ • ψ) := (map_smul _ _ _).symm
  simp only [simpleAffineRoots, positiveRoots, nonDivisibleRoots, Set.mem_ofPred_eq,
    affineFunctionalTransport_mem_transportedRoots, hsmul, Set.forall_mem_image,
    affineFunctionalTransport_apply, AffineEquiv.symm_apply_apply,
    hyperplane_affineFunctionalTransport, isChamberWall_transportedRoots_iff]

/-- The simple affine roots of a transported chamber are the transported simple roots. -/
theorem simpleAffineRoots_transportedRoots (e : A ≃ᵃ[ℝ] B) (Ψ : Set (A →ᵃ[ℝ] ℝ))
    (C : Set A) :
    simpleAffineRoots (transportedRoots e Ψ) (e '' C) =
      affineFunctionalTransport e '' simpleAffineRoots Ψ C := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨ψ, -, rfl⟩ := hφ.1.1
    exact ⟨ψ, (affineFunctionalTransport_mem_simpleAffineRoots_iff e Ψ C ψ).1 hφ, rfl⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact (affineFunctionalTransport_mem_simpleAffineRoots_iff e Ψ C ψ).2 hψ

/-- An affine identification of root sets and chambers identifies their simple affine
roots, by inverse precomposition. -/
def simpleAffineRootsEquivOfTransport (e : A ≃ᵃ[ℝ] B) {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    {Φ : Set (B →ᵃ[ℝ] ℝ)} {C : Set A} {D : Set B} (h : transportedRoots e Ψ = Φ)
    (hD : e '' C = D) : simpleAffineRoots Ψ C ≃ simpleAffineRoots Φ D :=
  ((affineFunctionalTransport e).toEquiv.image _).trans
    (Set.equivOfEq (show affineFunctionalTransport e '' simpleAffineRoots Ψ C =
      simpleAffineRoots Φ D by rw [← h, ← hD, simpleAffineRoots_transportedRoots]))

@[simp] theorem coe_simpleAffineRootsEquivOfTransport_apply (e : A ≃ᵃ[ℝ] B)
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Φ : Set (B →ᵃ[ℝ] ℝ)} {C : Set A} {D : Set B}
    (h : transportedRoots e Ψ = Φ) (hD : e '' C = D) (ψ : simpleAffineRoots Ψ C) :
    (simpleAffineRootsEquivOfTransport e h hD ψ : B →ᵃ[ℝ] ℝ) =
      affineFunctionalTransport e ψ :=
  rfl

/-- The chamber Cartan matrix is invariant under transport of affine root systems. -/
theorem IsAffineRootSystemWithRankZero.chamberCartanMatrix_transport
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ) (e : A ≃ᵃ[ℝ] B)
    {Φ : Set (B →ᵃ[ℝ] ℝ)} {C : Set A} {D : Set B} (h : transportedRoots e Ψ = Φ)
    (hD : e '' C = D) (ψ η : simpleAffineRoots Ψ C) :
    chamberCartanMatrix Φ D (simpleAffineRootsEquivOfTransport e h hD ψ)
        (simpleAffineRootsEquivOfTransport e h hD η) =
      chamberCartanMatrix Ψ C ψ η := by
  have hΦ : IsAffineRootSystemWithRankZero Φ := h ▸ hΨ.transport e
  have hcor : IsCoroot Φ (affineFunctionalTransport e (η : A →ᵃ[ℝ] ℝ))
      (e.linear (corootVector Ψ (η : A →ᵃ[ℝ] ℝ))) := by
    rw [← h]
    exact (isCoroot_transport_iff e Ψ _ _).2 (hΨ.isCoroot_corootVector_of_mem η.2.1.1)
  simp only [chamberCartanMatrix, coe_simpleAffineRootsEquivOfTransport_apply,
    hΦ.corootVector_eq hcor, affineFunctionalTransport_linear_apply]

/-- A root-preserving automorphism transports the root set to itself. -/
theorem transportedRoots_eq_self_of_mem_rootStabilizer {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    {e : A ≃ᵃ[ℝ] A} (he : e ∈ rootStabilizer Ψ) : transportedRoots e Ψ = Ψ := by
  have he' : e⁻¹ ∈ rootStabilizer Ψ := inv_mem he
  ext ψ
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    exact (he' ζ).2 hζ
  · intro hψ
    refine ⟨ψ.comp (e : A →ᵃ[ℝ] A), (he ψ).2 hψ, ?_⟩
    ext x
    simp [affineFunctionalTransport_apply]

/-- A root-preserving automorphism stabilizing a chamber permutes its simple affine roots by
`ψ ↦ ψ ∘ e⁻¹` and preserves the chamber Cartan matrix. -/
theorem IsAffineRootSystemWithRankZero.exists_perm_chamberCartanMatrix
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ) {C : Set A}
    {e : A ≃ᵃ[ℝ] A} (he : e ∈ rootStabilizer Ψ) (hC : e '' C = C) :
    ∃ σ : Equiv.Perm (simpleAffineRoots Ψ C),
      (∀ ψ, (σ ψ : A →ᵃ[ℝ] ℝ) = (ψ : A →ᵃ[ℝ] ℝ).comp (e.symm : A →ᵃ[ℝ] A)) ∧
        ∀ ψ η, chamberCartanMatrix Ψ C (σ ψ) (σ η) = chamberCartanMatrix Ψ C ψ η :=
  ⟨simpleAffineRootsEquivOfTransport e (transportedRoots_eq_self_of_mem_rootStabilizer he) hC,
    fun _ => rfl,
    hΨ.chamberCartanMatrix_transport e (transportedRoots_eq_self_of_mem_rootStabilizer he) hC⟩

/-- If root-preserving automorphisms stabilizing a chamber act transitively on its simple
affine roots, then for every two simple affine roots some permutation preserving all
entries of the chamber Cartan matrix sends the first to the second. -/
theorem IsAffineRootSystemWithRankZero.exists_perm_chamberCartanMatrix_apply_eq
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ) {C : Set A}
    {Γ : Set (A ≃ᵃ[ℝ] A)} (hΓ : Γ ⊆ rootStabilizer Ψ) (hΓC : ∀ e ∈ Γ, e '' C = C)
    (htrans : ∀ ψ η : simpleAffineRoots Ψ C, ∃ e ∈ Γ,
      (η : A →ᵃ[ℝ] ℝ) = (ψ : A →ᵃ[ℝ] ℝ).comp (e.symm : A →ᵃ[ℝ] A))
    (ψ η : simpleAffineRoots Ψ C) :
    ∃ σ : Equiv.Perm (simpleAffineRoots Ψ C),
      (∀ k l, chamberCartanMatrix Ψ C (σ k) (σ l) = chamberCartanMatrix Ψ C k l) ∧ σ ψ = η := by
  obtain ⟨e, he, hη⟩ := htrans ψ η
  obtain ⟨σ, hσ, hσA⟩ := hΨ.exists_perm_chamberCartanMatrix (hΓ he) (hΓC e he)
  exact ⟨σ, hσA, Subtype.ext (by rw [hσ, hη])⟩

end Transport

end Langlands.Geometry.Building.AffineRootSystem
