import Langlands.GroupScheme.OrthogonalMatrix.Hyperbolic

/-! # Hyperbolic bases adapted to a hyperbolic pair and to a rank-one torus

Over an algebraically closed field, a hyperbolic pair `x, f` of a nondegenerate quadratic form
extends to a hyperbolic basis (`exists_adapted_hyperbolicFamily`,
`exists_adapted_hyperbolic_matrix`).

The weight lemma `exists_weight_adapted_matrix` concerns column vectors `α₁, α₂` and row
vectors `β₁, β₂` with `βᵢ ⬝ αⱼ = δᵢⱼ`. Put
`G(s) = 1 + (s - 1) α₁ β₁ + (s⁻¹ - 1) α₂ β₂` (`weightMatrix`). Suppose `G(s)` preserves the
quadratic form `x ↦ x C xᵀ` for one `s` with `s² ≠ 1`. Then there is a hyperbolic coordinate
change `P` that conjugates `α₁ β₁` and `α₂ β₂` to the matrix units at `(inl 0, inl 0)` and
`(inr 0, inr 0)`. Matrices act on row vectors on the right.
-/

noncomputable section

open Matrix Module LinearMap.BilinForm
open LinearMap (BilinForm)
open scoped Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

universe w

variable {L : Type*} [Field L]

/-- **Adapted hyperbolic basis.** Over an algebraically closed field, a hyperbolic pair `x, f`
of a quadratic form with nondegenerate polar form on a space of dimension `2 (k + 1)` extends to
a hyperbolic family with `v (inl 0) = x` and `v (inr 0) = f`. -/
theorem exists_adapted_hyperbolicFamily [IsAlgClosed L] {V : Type w} [AddCommGroup V]
    [Module L V] [FiniteDimensional L V] {k : ℕ} (hV : finrank L V = 2 * (k + 1))
    (Q : QuadraticForm L V) (hN : (QuadraticMap.polarBilin Q).Nondegenerate)
    {x f : V} (hx : Q x = 0) (hf : Q f = 0) (hxf : QuadraticMap.polar Q x f = 1) :
    ∃ v : Fin (k + 1) ⊕ Fin (k + 1) → V, (∀ a, Q (v a) = 0) ∧
      (∀ a b, QuadraticMap.polar Q (v a) (v b) = polarMatrix (Fin (k + 1)) L a b) ∧
      v (Sum.inl 0) = x ∧ v (Sum.inr 0) = f := by
  set B : BilinForm L V := QuadraticMap.polarBilin Q with hBdef
  have hB : ∀ x y, B x y = QuadraticMap.polar Q x y := fun _ _ => rfl
  have hfx : QuadraticMap.polar Q f x = 1 := by rw [QuadraticMap.polar_comm, hxf]
  have hxx : QuadraticMap.polar Q x x = 0 := by rw [QuadraticMap.polar_self, hx, smul_zero]
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hpair : ∀ a c : L, B (a • x + c • f) x = c ∧ B (a • x + c • f) f = a := by
    intro a c
    simp only [hB, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, smul_eq_mul, hxx,
      hfx, hxf, hff]
    constructor <;> ring
  have hli : LinearIndependent L ![x, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := hpair s t
    rw [hst, map_zero, LinearMap.zero_apply, LinearMap.zero_apply] at h
    exact ⟨h.2.symm, h.1.symm⟩
  set W : Submodule L V := Submodule.span L (Set.range ![x, f]) with hWdef
  have hxW : x ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hfW : f ∈ W := Submodule.subset_span ⟨1, rfl⟩
  have hWrank : finrank L W = 2 := by
    rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hRefl : B.IsRefl := fun a b h => by
    rw [hB, QuadraticMap.polar_comm, ← hB, h]
  have hW : (B.restrict W).Nondegenerate := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (B := B.restrict W)
      (fun a b h => hRefl (a : V) (b : V) h)).2 ?_
    rintro ⟨w, hw⟩ h0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hw
    have h1 : B (c 0 • x + c 1 • f) x = 0 := by
      have := h0 ⟨x, hxW⟩
      simpa [Fin.sum_univ_two] using this
    have h2 : B (c 0 • x + c 1 • f) f = 0 := by
      have := h0 ⟨f, hfW⟩
      simpa [Fin.sum_univ_two] using this
    rw [(hpair _ _).1] at h1
    rw [(hpair _ _).2] at h2
    apply Subtype.ext
    simp [Fin.sum_univ_two, h1, h2]
  have hcompl := isCompl_orthogonal_of_restrict_nondegenerate hRefl hW
  set W' : Submodule L V := B.orthogonal W with hW'def
  have hW' : (B.restrict W').Nondegenerate := by
    rw [restrict_nondegenerate_iff_isCompl_orthogonal hRefl, hW'def,
      orthogonal_orthogonal hN hRefl]
    exact hcompl.symm
  have hW'rank : finrank L W' = 2 * k := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  set Q' : QuadraticForm L W' := Q.comp W'.subtype with hQ'def
  have hQ'B : QuadraticMap.polarBilin Q' = B.restrict W' :=
    LinearMap.ext₂ fun a b => rfl
  obtain ⟨v, hv0, hv⟩ := exists_hyperbolicFamily hW'rank Q' (hQ'B ▸ hW')
  have hv0' : ∀ a, Q (v a : V) = 0 := hv0
  have hv' : ∀ a b, QuadraticMap.polar Q (v a : V) (v b : V) = polarMatrix (Fin k) L a b :=
    fun a b => hv a b
  have hort : ∀ a, QuadraticMap.polar Q x (v a : V) = 0 ∧ QuadraticMap.polar Q f (v a : V) = 0 :=
    fun a => ⟨(v a).2 x hxW, (v a).2 f hfW⟩
  have hort' : ∀ a, QuadraticMap.polar Q (v a : V) x = 0 ∧ QuadraticMap.polar Q (v a : V) f = 0 :=
    fun a => ⟨by rw [QuadraticMap.polar_comm]; exact (hort a).1,
      by rw [QuadraticMap.polar_comm]; exact (hort a).2⟩
  refine ⟨Sum.elim (fun i => Fin.cases x (fun j => (v (Sum.inl j) : V)) i)
    (fun i => Fin.cases f (fun j => (v (Sum.inr j) : V)) i), ?_, ?_, by simp, by simp⟩
  · rintro (i | i) <;> cases i using Fin.cases <;> simp [hx, hf, hv0']
  have h0s : ∀ i : Fin k, (0 : Fin (k + 1)) ≠ i.succ := fun i => (Fin.succ_ne_zero i).symm
  have hs0 : ∀ i : Fin k, i.succ ≠ (0 : Fin (k + 1)) := fun i => Fin.succ_ne_zero i
  rintro (i | i) (j | j) <;> cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [polarMatrix, hxx, hxf, hfx, hff, hort, hort', hv', Matrix.one_apply, h0s, hs0]

/-- **Adapted hyperbolic basis, matrix form.** Let `Q : Matrix n n L` with `Q + Qᵀ` invertible
and `card n = 2 (k + 1)` over an algebraically closed field. A hyperbolic pair `x, f` of the
form `y ↦ y Q yᵀ` gives the first rows `P (inl 0) = x` and `P (inr 0) = f` of an invertible
matrix `P` such that `P Q Pᵀ - formMatrix` is alternating. -/
theorem exists_adapted_hyperbolic_matrix [IsAlgClosed L] {n : Type*} [Fintype n]
    [DecidableEq n] {k : ℕ} (hcard : Fintype.card n = 2 * (k + 1)) (Q : Matrix n n L)
    (hQ : IsUnit (Q + Qᵀ)) {x f : n → L} (hx : x ⬝ᵥ Q *ᵥ x = 0) (hf : f ⬝ᵥ Q *ᵥ f = 0)
    (hxf : x ⬝ᵥ (Q + Qᵀ) *ᵥ f = 1) :
    ∃ (P : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) n L) (P' : Matrix n (Fin (k + 1) ⊕ Fin (k + 1)) L),
      P * P' = 1 ∧ P' * P = 1 ∧ IsAlt (P * Q * Pᵀ - formMatrix (Fin (k + 1)) L) ∧
      P (Sum.inl 0) = x ∧ P (Sum.inr 0) = f ∧
      ∀ a b, P a ⬝ᵥ (Q + Qᵀ) *ᵥ P b = polarMatrix (Fin (k + 1)) L a b := by
  set q : QuadraticForm L (n → L) := LinearMap.BilinMap.toQuadraticMap (Matrix.toBilin' Q)
    with hqdef
  have hq : ∀ x, q x = x ⬝ᵥ Q *ᵥ x := fun x => by
    rw [hqdef, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply']
  have hpolar : ∀ x y, QuadraticMap.polar q x y = x ⬝ᵥ (Q + Qᵀ) *ᵥ y := by
    intro x y
    rw [hqdef, LinearMap.BilinMap.polar_toQuadraticMap, Matrix.toBilin'_apply',
      Matrix.toBilin'_apply', Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose,
      dotProduct_comm x (y ᵥ* Q), ← Matrix.dotProduct_mulVec]
  have hB : QuadraticMap.polarBilin q = Matrix.toBilin' (Q + Qᵀ) :=
    LinearMap.ext₂ fun x y => by
      rw [QuadraticMap.polarBilin_apply_apply, hpolar, Matrix.toBilin'_apply']
  have hN : (QuadraticMap.polarBilin q).Nondegenerate := by
    rw [hB]
    exact nondegenerate_toBilin'_iff_det_ne_zero.2
      ((Matrix.isUnit_iff_isUnit_det _).1 hQ).ne_zero
  have hdim : finrank L (n → L) = 2 * (k + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  obtain ⟨v, hv0, hv, hvx, hvf⟩ := exists_adapted_hyperbolicFamily hdim q hN
    (by rw [hq]; exact hx) (by rw [hq]; exact hf) (by rw [hpolar]; exact hxf)
  set P : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) n L := Matrix.of v with hPdef
  have hPJ : P * (Q + Qᵀ) * Pᵀ = polarMatrix (Fin (k + 1)) L := by
    ext a b
    rw [hPdef, of_mul_mul_transpose_apply, ← hpolar, hv]
  have hPP' : P * ((Q + Qᵀ) * Pᵀ * polarMatrix (Fin (k + 1)) L) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPJ, polarMatrix_mul_self]
  let e : (Fin (k + 1) ⊕ Fin (k + 1)) ≃ n := Fintype.equivOfCardEq (by simp; omega)
  refine ⟨P, (Q + Qᵀ) * Pᵀ * polarMatrix (Fin (k + 1)) L, hPP',
    (Matrix.mul_eq_one_comm_of_equiv e).1 hPP', ?_, hvx, hvf, fun a b => ?_⟩
  · rw [isAlt_iff]
    refine ⟨?_, fun a => ?_⟩
    · rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose]
      have h1 : P * Q * Pᵀ - formMatrix (Fin (k + 1)) L +
          (P * (Qᵀ * Pᵀ) - (formMatrix (Fin (k + 1)) L)ᵀ) =
          P * (Q + Qᵀ) * Pᵀ -
            (formMatrix (Fin (k + 1)) L + (formMatrix (Fin (k + 1)) L)ᵀ) := by
        rw [Matrix.mul_add, Matrix.add_mul]
        simp only [Matrix.mul_assoc]
        abel
      rw [h1, hPJ, formMatrix_add_transpose, sub_self]
    · rw [Matrix.sub_apply, hPdef, of_mul_mul_transpose_apply, ← hq, hv0, formMatrix_apply]
      rcases a with a | a <;> simp
  · rw [← hpolar]
    exact hv a b

section Weight

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one torus element `1 + (s - 1) α₁ β₁ + (s' - 1) α₂ β₂`, for column vectors
`α₁, α₂` and row vectors `β₁, β₂`. -/
def weightMatrix {A : Type*} [CommRing A] (α₁ β₁ α₂ β₂ : n → A) (s s' : A) : Matrix n n A :=
  1 + (s - 1) • vecMulVec α₁ β₁ + (s' - 1) • vecMulVec α₂ β₂

omit [Fintype n] in
theorem weightMatrix_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (α₁ β₁ α₂ β₂ : n → A) (s s' : A) :
    (weightMatrix α₁ β₁ α₂ β₂ s s').map φ =
      weightMatrix (φ ∘ α₁) (φ ∘ β₁) (φ ∘ α₂) (φ ∘ β₂) (φ s) (φ s') := by
  ext i j
  simp [weightMatrix, Matrix.one_apply, vecMulVec_apply]

/-- Row vectors under the torus element. -/
theorem vecMul_weightMatrix {A : Type*} [CommRing A] (α₁ β₁ α₂ β₂ : n → A) (s s' : A)
    (x : n → A) :
    x ᵥ* weightMatrix α₁ β₁ α₂ β₂ s s' =
      x + ((s - 1) * (x ⬝ᵥ α₁)) • β₁ + ((s' - 1) * (x ⬝ᵥ α₂)) • β₂ := by
  simp only [weightMatrix, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul,
    vecMul_vecMulVec, smul_smul]

/-- Conjugating the torus element by a coordinate change which conjugates the two rank-one
idempotents to matrix units. -/
theorem conj_weightMatrix {A : Type*} [CommRing A] {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix m n A} {P' : Matrix n m A} (hPP' : P * P' = 1) {α₁ β₁ α₂ β₂ : n → A}
    {i₁ i₂ : m} (h₁ : P * vecMulVec α₁ β₁ * P' = Matrix.single i₁ i₁ 1)
    (h₂ : P * vecMulVec α₂ β₂ * P' = Matrix.single i₂ i₂ 1) (s s' : A) :
    P * weightMatrix α₁ β₁ α₂ β₂ s s' * P' =
      1 + Matrix.single i₁ i₁ (s - 1) + Matrix.single i₂ i₂ (s' - 1) := by
  simp only [weightMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP',
    Matrix.mul_smul, Matrix.smul_mul, h₁, h₂, Matrix.smul_single, smul_eq_mul, mul_one]

omit [DecidableEq n] in
theorem dotProduct_transpose_mulVec_self {A : Type*} [CommRing A] (M : Matrix n n A)
    (x : n → A) : x ⬝ᵥ Mᵀ *ᵥ x = x ⬝ᵥ M *ᵥ x := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]

omit [DecidableEq n] in
theorem dotProduct_mulVec_comm {A : Type*} [CommRing A] (M : Matrix n n A) (x y : n → A) :
    x ⬝ᵥ M *ᵥ y = y ⬝ᵥ Mᵀ *ᵥ x := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]

omit [DecidableEq n] in
/-- The quadratic form of an alternating matrix vanishes. -/
theorem IsAlt.dotProduct_mulVec_self {A : Type*} [CommRing A] {M : Matrix n n A}
    (hM : IsAlt M) (x : n → A) : x ⬝ᵥ M *ᵥ x = 0 := by
  obtain ⟨U, rfl⟩ := hM
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_transpose_mulVec_self, sub_self]

omit [DecidableEq n] in
theorem vecMul_dotProduct_mulVec_vecMul {A : Type*} [CommRing A] (G M : Matrix n n A)
    (x y : n → A) : (x ᵥ* G) ⬝ᵥ M *ᵥ (y ᵥ* G) = x ⬝ᵥ (G * M * Gᵀ) *ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul,
    ← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec ((x ᵥ* G) ᵥ* M),
    Matrix.mulVec_transpose]

/-- `vecMulVec` of two standard basis vectors is a matrix unit. -/
theorem vecMulVec_single_one {A : Type*} [CommRing A] {m : Type*} [DecidableEq m] (i j : m) :
    vecMulVec (Pi.single i (1 : A)) (Pi.single j (1 : A)) = Matrix.single i j 1 := by
  ext a b
  simp only [vecMulVec_apply, Pi.single_apply, Matrix.single_apply]
  split_ifs <;> simp_all

/-- **Weight-adapted hyperbolic coordinates.** Let `C : Matrix n n L` with `C + Cᵀ` invertible
and `card n = 2 (k + 1)` over an algebraically closed field `L`. Let `α₁, α₂` be column vectors
and `β₁, β₂` row vectors with `βᵢ ⬝ αⱼ = δᵢⱼ`. Suppose that for one `s ≠ 0` with `s² ≠ 1` the
torus element `G(s) = 1 + (s - 1) α₁ β₁ + (s⁻¹ - 1) α₂ β₂` preserves the quadratic form
`x ↦ x C xᵀ`, i.e. `G C Gᵀ - C` is alternating. Then some invertible `P` with
`P C Pᵀ - formMatrix` alternating conjugates `α₁ β₁` and `α₂ β₂` to the matrix units at
`(inl 0, inl 0)` and `(inr 0, inr 0)`. -/
theorem exists_weight_adapted_matrix [IsAlgClosed L] {k : ℕ}
    (hcard : Fintype.card n = 2 * (k + 1)) (C : Matrix n n L) (hC : IsUnit (C + Cᵀ))
    {α₁ β₁ α₂ β₂ : n → L} (h11 : β₁ ⬝ᵥ α₁ = 1) (h12 : β₁ ⬝ᵥ α₂ = 0) (h21 : β₂ ⬝ᵥ α₁ = 0)
    (h22 : β₂ ⬝ᵥ α₂ = 1) {s : L} (hs : s ≠ 0) (hs2 : s ^ 2 ≠ 1)
    (hG : IsAlt (weightMatrix α₁ β₁ α₂ β₂ s s⁻¹ * C * (weightMatrix α₁ β₁ α₂ β₂ s s⁻¹)ᵀ - C)) :
    ∃ (P : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) n L) (P' : Matrix n (Fin (k + 1) ⊕ Fin (k + 1)) L),
      P * P' = 1 ∧ P' * P = 1 ∧ IsAlt (P * C * Pᵀ - formMatrix (Fin (k + 1)) L) ∧
      P * vecMulVec α₁ β₁ * P' = Matrix.single (Sum.inl 0) (Sum.inl 0) 1 ∧
      P * vecMulVec α₂ β₂ * P' = Matrix.single (Sum.inr 0) (Sum.inr 0) 1 := by
  set G := weightMatrix α₁ β₁ α₂ β₂ s s⁻¹ with hGdef
  set J := C + Cᵀ with hJdef
  -- invariance of the quadratic and the polar form
  have hJ : G * J * Gᵀ = J := by
    have h1 := ((isAlt_iff _).1 hG).1
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose] at h1
    rw [hJdef, Matrix.mul_add, Matrix.add_mul, ← sub_eq_zero, ← h1]
    simp only [Matrix.mul_assoc]
    abel
  have hq : ∀ x : n → L, (x ᵥ* G) ⬝ᵥ C *ᵥ (x ᵥ* G) = x ⬝ᵥ C *ᵥ x := by
    intro x
    have h0 := hG.dotProduct_mulVec_self x
    rw [Matrix.sub_mulVec, dotProduct_sub, sub_eq_zero] at h0
    rw [vecMul_dotProduct_mulVec_vecMul, h0]
  have hb : ∀ x y : n → L, (x ᵥ* G) ⬝ᵥ J *ᵥ (y ᵥ* G) = x ⬝ᵥ J *ᵥ y := by
    intro x y
    rw [vecMul_dotProduct_mulVec_vecMul, hJ]
  have hpol : ∀ x : n → L, x ⬝ᵥ J *ᵥ x = 2 * (x ⬝ᵥ C *ᵥ x) := by
    intro x
    rw [hJdef, Matrix.add_mulVec, dotProduct_add, dotProduct_transpose_mulVec_self]
    ring
  have hsymm : ∀ x y : n → L, x ⬝ᵥ J *ᵥ y = y ⬝ᵥ J *ᵥ x := by
    intro x y
    rw [dotProduct_mulVec_comm, hJdef, Matrix.transpose_add, Matrix.transpose_transpose,
      add_comm Cᵀ]
  -- the weight vectors
  have hG1 : β₁ ᵥ* G = s • β₁ := by
    rw [hGdef, vecMul_weightMatrix, h11, h12]
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    rw [← one_smul L β₁, smul_smul, ← add_smul, one_smul]
    congr 1
    ring
  have hG2 : β₂ ᵥ* G = s⁻¹ • β₂ := by
    rw [hGdef, vecMul_weightMatrix, h21, h22]
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    rw [← one_smul L β₂, smul_smul, ← add_smul, one_smul]
    congr 1
    ring
  have hGw : ∀ w : n → L, w ⬝ᵥ α₁ = 0 → w ⬝ᵥ α₂ = 0 → w ᵥ* G = w := by
    intro w h1 h2
    rw [hGdef, vecMul_weightMatrix, h1, h2]
    simp
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hs2 (one_pow 2)
  have hsi1 : s⁻¹ ≠ 1 := by
    intro h
    exact hs1 (inv_eq_one.1 h)
  have hsi2 : s⁻¹ ^ 2 ≠ 1 := by
    rw [inv_pow]
    intro h
    exact hs2 (inv_eq_one.1 h)
  -- isotropy of the weight vectors
  have hiso : ∀ (t : L), t ^ 2 ≠ 1 → ∀ β : n → L, β ᵥ* G = t • β → β ⬝ᵥ C *ᵥ β = 0 := by
    intro t ht β hβ
    have e1 := hq β
    rw [hβ] at e1
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at e1
    have e2 : (t ^ 2 - 1) * (β ⬝ᵥ C *ᵥ β) = 0 := by linear_combination e1
    exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 ht)
  have hQ1 : β₁ ⬝ᵥ C *ᵥ β₁ = 0 := hiso s hs2 β₁ hG1
  have hQ2 : β₂ ⬝ᵥ C *ᵥ β₂ = 0 := hiso s⁻¹ hsi2 β₂ hG2
  have hB11 : β₁ ⬝ᵥ J *ᵥ β₁ = 0 := by rw [hpol, hQ1, mul_zero]
  have hB22 : β₂ ⬝ᵥ J *ᵥ β₂ = 0 := by rw [hpol, hQ2, mul_zero]
  -- orthogonality of the fixed vectors to the weight vectors
  have hort : ∀ (t : L), t ≠ 1 → ∀ β : n → L, β ᵥ* G = t • β →
      ∀ w : n → L, w ⬝ᵥ α₁ = 0 → w ⬝ᵥ α₂ = 0 → w ⬝ᵥ J *ᵥ β = 0 := by
    intro t ht β hβ w h1 h2
    have e1 := hb w β
    rw [hβ, hGw w h1 h2] at e1
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at e1
    have e2 : (t - 1) * (w ⬝ᵥ J *ᵥ β) = 0 := by linear_combination e1
    exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 ht)
  -- decomposition of the polar pairings with the weight vectors
  set c := β₁ ⬝ᵥ J *ᵥ β₂ with hcdef
  have hdec : ∀ y : n → L, y ⬝ᵥ J *ᵥ β₂ = (y ⬝ᵥ α₁) * c ∧ y ⬝ᵥ J *ᵥ β₁ = (y ⬝ᵥ α₂) * c := by
    intro y
    set w := y - (y ⬝ᵥ α₁) • β₁ - (y ⬝ᵥ α₂) • β₂ with hwdef
    have hw1 : w ⬝ᵥ α₁ = 0 := by
      simp only [hwdef, sub_dotProduct, smul_dotProduct, smul_eq_mul, h11, h21]
      ring
    have hw2 : w ⬝ᵥ α₂ = 0 := by
      simp only [hwdef, sub_dotProduct, smul_dotProduct, smul_eq_mul, h12, h22]
      ring
    have e2 := hort s⁻¹ hsi1 β₂ hG2 w hw1 hw2
    have e1 := hort s hs1 β₁ hG1 w hw1 hw2
    have hc' : β₂ ⬝ᵥ J *ᵥ β₁ = c := hsymm _ _
    simp only [hwdef, sub_dotProduct, smul_dotProduct, smul_eq_mul, hB22, hB11, hc'] at e1 e2
    constructor
    · linear_combination e2
    · linear_combination e1
  have hc : c ≠ 0 := by
    intro hc0
    have hJβ : J *ᵥ β₁ = 0 := by
      funext i
      have := (hdec (Pi.single i 1)).2
      rw [hc0, mul_zero, single_one_dotProduct] at this
      exact this
    obtain ⟨u, hu⟩ := hC
    have hβ : β₁ = 0 := by
      have h := congrArg (fun v => (↑u⁻¹ : Matrix n n L) *ᵥ v) hJβ
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h
      rw [← hu, Units.inv_mul, Matrix.one_mulVec] at h
      exact h
    rw [hβ, zero_dotProduct] at h11
    exact zero_ne_one h11
  -- the adapted hyperbolic coordinates
  obtain ⟨P, P', hPP', hP'P, hPalt, hP0, hP1, hPpol⟩ :=
    exists_adapted_hyperbolic_matrix hcard C hC (x := β₁) (f := c⁻¹ • β₂) hQ1
      (by simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, hQ2,
        mul_zero])
      (by rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, ← hJdef, ← hcdef,
        inv_mul_cancel₀ hc])
  -- rows of `P` against the columns `α₁, α₂`
  have hrow : ∀ a, P a ⬝ᵥ α₁ = polarMatrix (Fin (k + 1)) L a (Sum.inr 0) ∧
      P a ⬝ᵥ α₂ = c⁻¹ * polarMatrix (Fin (k + 1)) L a (Sum.inl 0) := by
    intro a
    have e1 := hPpol a (Sum.inr 0)
    have e2 := hPpol a (Sum.inl 0)
    rw [hP1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, (hdec (P a)).1] at e1
    rw [hP0, (hdec (P a)).2] at e2
    constructor
    · rw [← e1]
      field_simp
    · rw [← e2]
      field_simp
  have hpm1 : ∀ a, polarMatrix (Fin (k + 1)) L a (Sum.inr 0) =
      (Pi.single (Sum.inl 0) (1 : L) : Fin (k + 1) ⊕ Fin (k + 1) → L) a := by
    rintro (a | a) <;> simp [polarMatrix, Matrix.one_apply, Pi.single_apply, eq_comm]
  have hpm2 : ∀ a, polarMatrix (Fin (k + 1)) L a (Sum.inl 0) =
      (Pi.single (Sum.inr 0) (1 : L) : Fin (k + 1) ⊕ Fin (k + 1) → L) a := by
    rintro (a | a) <;> simp [polarMatrix, Matrix.one_apply, Pi.single_apply]
  have hPα₁ : P *ᵥ α₁ = Pi.single (Sum.inl 0) 1 := by
    funext a
    rw [← hpm1, ← (hrow a).1]
    rfl
  have hPα₂ : P *ᵥ α₂ = c⁻¹ • Pi.single (Sum.inr 0) 1 := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul, ← hpm2, ← (hrow a).2]
    rfl
  have hrowP' : ∀ a, P a ᵥ* P' = Pi.single a 1 := by
    intro a
    funext j
    have h := congrFun (congrFun hPP' a) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.vecMul, dotProduct, Pi.single_apply]
    rw [h]
    exact if_congr eq_comm rfl rfl
  have hβ₁P' : β₁ ᵥ* P' = Pi.single (Sum.inl 0) 1 := by rw [← hP0, hrowP']
  have hβ₂P' : β₂ ᵥ* P' = c • Pi.single (Sum.inr 0) 1 := by
    have h := hrowP' (Sum.inr 0)
    rw [hP1, Matrix.smul_vecMul] at h
    rw [← h, smul_smul, mul_inv_cancel₀ hc, one_smul]
  refine ⟨P, P', hPP', hP'P, hPalt, ?_, ?_⟩
  · rw [mul_vecMulVec, vecMulVec_mul, hPα₁, hβ₁P', vecMulVec_single_one]
  · rw [mul_vecMulVec, vecMulVec_mul, hPα₂, hβ₂P', ← vecMulVec_single_one]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_mul_mul_comm, inv_mul_cancel₀ hc, one_mul]

end Weight

end Langlands.GroupScheme.OrthogonalMatrix
