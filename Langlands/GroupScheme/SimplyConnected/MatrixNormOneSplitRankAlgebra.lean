import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Linear algebra for the split rank of `SL_m(D)`

Three elementary facts used to bound the split rank of the reduced-norm-one group of
`M_m(D)`:

* a complete family of orthogonal idempotents `e i` of a finite-dimensional algebra `A`
  decomposes `A` into the right ideals `e i A`, and the regular norm of `∑ cᵢ ⊗ eᵢ` is
  `∏ cᵢ ^ dim (e i A)`;
* a nonzero right ideal `e A` of `M_n(D)` has dimension at least `n · dim D`;
* finitely many vectors that generate `ℤ^I` and satisfy a relation with positive
  coefficients number at least `|I| + 1`.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.GroupScheme.MatrixNormOneSplitRank

/-! ### Complete orthogonal idempotents -/

section Idempotents

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → A)

variable (K) in
/-- The right ideal `e i A`, as a `K`-subspace of `A`. -/
def piece (i : ι) : Submodule K A := LinearMap.range (LinearMap.mulLeft K (e i))

omit [Fintype ι] [DecidableEq ι] in
theorem mem_piece_iff {i : ι} {x : A} : x ∈ piece K e i ↔ ∃ y, e i * y = x := Iff.rfl

variable {e} (hmul : ∀ i j, e i * e j = if i = j then e i else 0) (hsum : ∑ i, e i = 1)
include hmul

omit [Fintype ι] in
/-- Left multiplication by `e i` acts on the piece `e j A` as the Kronecker delta. -/
theorem mul_of_mem_piece {i j : ι} {x : A} (hx : x ∈ piece K e j) :
    e i * x = if j = i then x else 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [LinearMap.mulLeft_apply, ← mul_assoc, hmul]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

include hsum

/-- The right ideals `e i A` form an internal direct sum decomposition of `A`. -/
theorem isInternal_piece : DirectSum.IsInternal (piece K e) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hker : (⨆ (j) (_ : j ≠ i), piece K e j) ≤ LinearMap.ker (LinearMap.mulLeft K (e i)) := by
      refine iSup₂_le fun j hj => ?_
      intro z hz
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, mul_of_mem_piece hmul hz, ite_eq_right hj]
    have h0 : e i * x = 0 := hker hx'
    rw [mul_of_mem_piece hmul hx, ite_eq_left rfl] at h0
    exact h0
  · rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, e i * x := by rw [← Finset.sum_mul, hsum, one_mul]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨x, rfl⟩

variable [FiniteDimensional K A]

variable (K) in
/-- A basis of `A` adapted to the decomposition into the right ideals `e i A`. -/
def pieceBasis : Module.Basis (Σ i, Fin (Module.finrank K (piece K e i))) K A :=
  (isInternal_piece hmul hsum).collectedBasis fun i => Module.finBasis K (piece K e i)

theorem pieceBasis_mem (a : Σ i, Fin (Module.finrank K (piece K e i))) :
    pieceBasis K hmul hsum a ∈ piece K e a.1 :=
  (isInternal_piece hmul hsum).collectedBasis_mem _ a

/-- The idempotents act diagonally on the adapted basis. -/
theorem mul_pieceBasis (i : ι) (a : Σ i, Fin (Module.finrank K (piece K e i))) :
    e i * pieceBasis K hmul hsum a = if a.1 = i then pieceBasis K hmul hsum a else 0 :=
  mul_of_mem_piece hmul (pieceBasis_mem hmul hsum a)

/-- The dimensions of the right ideals `e i A` add up to the dimension of `A`. -/
theorem sum_finrank_piece : ∑ i, Module.finrank K (piece K e i) = Module.finrank K A := by
  rw [Module.finrank_eq_card_basis (pieceBasis K hmul hsum), Fintype.card_sigma]
  simp

/-- **Norm of a combination of idempotents.** The regular norm of `∑ cᵢ ⊗ eᵢ` over any
commutative `K`-algebra `R` is `∏ cᵢ ^ dim (e i A)`. -/
theorem norm_sum_tmul (R : Type*) [CommRing R] [Algebra K R] (c : ι → R) :
    Algebra.norm R (∑ i, c i ⊗ₜ[K] e i) = ∏ i, c i ^ Module.finrank K (piece K e i) := by
  classical
  set B := pieceBasis K hmul hsum
  rw [Algebra.norm_eq_matrix_det (B.baseChange R)]
  have hmat : Algebra.leftMulMatrix (B.baseChange R) (∑ i, c i ⊗ₜ[K] e i) =
      Matrix.diagonal fun a => c a.1 := by
    refine Matrix.ext fun a a' => ?_
    rw [Matrix.diagonal_apply, Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.baseChange_apply]
    have hs : (∑ i, c i ⊗ₜ[K] e i) * ((1 : R) ⊗ₜ[K] B a') = c a'.1 ⊗ₜ[K] B a' := by
      rw [Finset.sum_mul]
      have hB : ∀ i a, e i * B a = if a.1 = i then B a else 0 := fun i a =>
        mul_pieceBasis hmul hsum i a
      simp_rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hB]
      rw [Finset.sum_eq_single a'.1]
      · rw [ite_eq_left rfl]
      · intro i _ hi
        rw [ite_eq_right (Ne.symm hi), TensorProduct.tmul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hs, Module.Basis.baseChange_repr_tmul, Module.Basis.repr_self]
    by_cases h : a = a'
    · subst h
      simp
    · rw [Finsupp.single_eq_of_ne h, ite_eq_right h, zero_smul]
  rw [hmat, Matrix.det_diagonal, Fintype.prod_sigma]
  simp

end Idempotents

/-! ### Right ideals of matrix algebras over division rings -/

section MatrixRightIdeal

variable {K D : Type*} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {n : ℕ}

/-- The `K`-linear map placing a row vector in the row `q` of an otherwise zero matrix. -/
def rowInsert (q : Fin n) : (Fin n → D) →ₗ[K] Matrix (Fin n) (Fin n) D where
  toFun c := Matrix.of fun r s => if r = q then c s else 0
  map_add' c c' := by
    ext r s
    simp only [Matrix.of_apply, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' t c := by
    ext r s
    simp only [Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/-- **Right ideals of `M_n(D)` are large.** For a nonzero `e`, the right ideal `e · M_n(D)`
has `K`-dimension at least `n · dim_K D`: multiplying `e` with matrices supported on one
row is injective. -/
theorem le_finrank_range_mulLeft (e : Matrix (Fin n) (Fin n) D) (he : e ≠ 0) :
    n * Module.finrank K D ≤
      Module.finrank K (LinearMap.range (LinearMap.mulLeft K e)) := by
  obtain ⟨p, q, hpq⟩ : ∃ p q, e p q ≠ 0 := by
    by_contra h
    push Not at h
    exact he (Matrix.ext h)
  let L : (Fin n → D) →ₗ[K] LinearMap.range (LinearMap.mulLeft K e) :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft K e).comp (rowInsert q))
      fun c => ⟨rowInsert q c, rfl⟩
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hc' : e * rowInsert q c = 0 := congrArg Subtype.val hc
    funext s
    have hps := congrFun (congrFun hc' p) s
    rw [Matrix.mul_apply, Matrix.zero_apply, Finset.sum_eq_single q] at hps
    · change e p q * (if q = q then c s else 0) = 0 at hps
      rw [ite_eq_left rfl] at hps
      exact (mul_eq_zero.mp hps).resolve_left hpq
    · intro r _ hr
      change e p r * (if r = q then c s else 0) = 0
      rw [ite_eq_right hr, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h := LinearMap.finrank_le_finrank_of_injective hL
  rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at h

end MatrixRightIdeal

/-! ### Generating sets of `ℤ^I` with a positive relation -/

section Lattice

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The rational vector of an integer vector. -/
def ratVec (m : I → ℤ) : I → ℚ := fun i => (m i : ℚ)

/-- If a finite set `S` generates `ℤ^I` and carries a relation `∑ r_m m = 0` with positive
coefficients, then `|I| + 1 ≤ |S|`, unless `S` is empty, in which case `I` is empty. -/
theorem card_add_one_le_of_relation (S : Finset (I → ℤ))
    (hS : AddSubgroup.closure (S : Set (I → ℤ)) = ⊤) (r : (I → ℤ) → ℕ)
    (hr : ∀ m ∈ S, 0 < r m) (hrel : ∑ m ∈ S, r m • m = 0) :
    Fintype.card I ≤ S.card - 1 := by
  classical
  let φ : (S → ℚ) →ₗ[ℚ] (I → ℚ) :=
    Fintype.linearCombination ℚ fun s : S => ratVec s.1
  have hφ : ∀ c, φ c = ∑ s : S, c s • ratVec s.1 := fun c =>
    Fintype.linearCombination_apply ℚ _ c
  -- the image of `φ` contains every integer vector
  have hint : ∀ z : I → ℤ, ratVec z ∈ LinearMap.range φ := by
    intro z
    have hz : z ∈ AddSubgroup.closure (S : Set (I → ℤ)) := hS ▸ AddSubgroup.mem_top z
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      refine ⟨Pi.single ⟨x, hx⟩ 1, ?_⟩
      rw [hφ, Finset.sum_eq_single ⟨x, hx⟩]
      · simp
      · intro s _ hs
        rw [Pi.single_eq_of_ne hs, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    | zero =>
      have : ratVec (0 : I → ℤ) = 0 := by
        funext i
        simp [ratVec]
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : ratVec (x + y) = ratVec x + ratVec y := by
        funext i
        simp [ratVec]
      rw [this]
      exact Submodule.add_mem _ hx hy
    | neg x _ hx =>
      have : ratVec (-x) = -ratVec x := by
        funext i
        simp [ratVec]
      rw [this]
      exact Submodule.neg_mem _ hx
  have htop : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • ratVec (Pi.single i (1 : ℤ)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp [ratVec]
      · intro i _ hi
        simp [ratVec, Ne.symm hi]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hint _)
  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  rw [htop, finrank_top, Module.finrank_pi, Module.finrank_pi, Fintype.card_coe] at hrank
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · -- `ℤ^I` is generated by the empty set, so it is trivial
    have hI : IsEmpty I := by
      rw [hSe, Finset.coe_empty, AddSubgroup.closure_empty] at hS
      refine ⟨fun i => ?_⟩
      have h1 : (Pi.single i (1 : ℤ)) ∈ (⊥ : AddSubgroup (I → ℤ)) := hS ▸ AddSubgroup.mem_top _
      have h2 := congrFun ((AddSubgroup.mem_bot).mp h1) i
      simp at h2
    simp
  · -- the positive relation is a nonzero kernel vector
    obtain ⟨m₀, hm₀⟩ := hSne
    let c : S → ℚ := fun s => (r s.1 : ℚ)
    have hc : c ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, hφ]
      funext i
      have h := congrFun hrel i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at h
      have h' : ((∑ m ∈ S, r m • m i : ℤ) : ℚ) = 0 := by rw [h, Int.cast_zero]
      push_cast [nsmul_eq_mul] at h'
      rw [Finset.sum_apply, Pi.zero_apply]
      simp only [Pi.smul_apply, smul_eq_mul, c, ratVec]
      rw [Finset.sum_coe_sort S (fun m => (r m : ℚ) * (m i : ℚ))]
      exact h'
    have hc0 : c ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨m₀, hm₀⟩
      simp only [c, Pi.zero_apply, Nat.cast_eq_zero] at this
      exact (hr m₀ hm₀).ne' this
    have hker : 0 < Module.finrank ℚ (LinearMap.ker φ) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨c, hc⟩, fun h => hc0 (congrArg Subtype.val h)⟩
    omega

end Lattice

end Langlands.GroupScheme.MatrixNormOneSplitRank
