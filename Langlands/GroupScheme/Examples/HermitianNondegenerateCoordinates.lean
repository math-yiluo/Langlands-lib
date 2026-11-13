import Langlands.GroupScheme.Examples.HermitianHyperbolicMatrixCoordinates
import Langlands.GroupScheme.Examples.HermitianHyperbolicReduction
import Langlands.GroupScheme.Examples.HermitianRootMatrices
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Orthogonal bases and hyperbolic coordinates for nondegenerate Hermitian spaces -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.HermitianRoot

open Module SU3Root

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
  {V : Type v} [AddCommGroup V] [Module L V]
  (h : V →ₗ[L] V →ₛₗ[(fieldInvolution K L).bar.toRingHom] L)
  (hbar : ∀ x y, (fieldInvolution K L).bar (h x y) = h y x)

include hbar in
/-- A nonzero Hermitian space whose pairing separates points on the left contains a
vector with nonzero self-pairing, in every characteristic. -/
theorem exists_pairing_self_ne_zero [Nontrivial V]
    (hn : ∀ x, (∀ y, h x y = 0) → x = 0) : ∃ x : V, h x x ≠ 0 := by
  by_contra! hall
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra! hy
    exact hx (hn x hy)
  let a : L := conjugation K L (traceOne K L / h x y)
  have hexp : h (x + a • y) (x + a • y) =
      h x x + conjugation K L a * h x y + a * h y x +
        a * conjugation K L a * h y y := by
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    have hc : (fieldInvolution K L).bar.toRingHom a = conjugation K L a := rfl
    rw [hc]
    ring
  have hyx : h y x = conjugation K L (h x y) := (hbar x y).symm
  have ha : conjugation K L a = traceOne K L / h x y :=
    conjugation_involutive K L _
  have hsum : conjugation K L a * h x y + a * h y x = 1 := by
    rw [hyx, ha, div_mul_cancel₀ _ hy]
    change traceOne K L + conjugation K L (traceOne K L / h x y) *
      conjugation K L (h x y) = 1
    rw [← map_mul, div_mul_cancel₀ _ hy, traceOne_add_conjugate]
  have h0 := hall (x + a • y)
  rw [hexp, hall x, hall y] at h0
  have : (1 : L) = 0 := by linear_combination h0 - hsum
  exact one_ne_zero this

include hbar in
/-- A Hermitian space separating points on the left has an orthogonal basis with
nonzero self-pairings, in every characteristic. -/
theorem exists_orthogonal_basis_of_separatingLeft [FiniteDimensional L V]
    (hn : ∀ x, (∀ y, h x y = 0) → x = 0) :
    ∃ b : Basis (Fin (finrank L V)) L V, h.IsOrthoᵢ b ∧ ∀ i, h (b i) (b i) ≠ 0 := by
  suffices ∀ d, finrank L V = d →
      ∃ b : Basis (Fin d) L V, h.IsOrthoᵢ b ∧ ∀ i, h (b i) (b i) ≠ 0 by
    exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero =>
    exact ⟨basisOfFinrankZero hd, fun i => i.elim0, fun i => i.elim0⟩
  | succ d ih =>
    have : Nontrivial V := (Module.finrank_pos_iff (R := L) (M := V)).mp (by omega)
    obtain ⟨x, hx⟩ := exists_pairing_self_ne_zero h hbar hn
    have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0, map_zero])
    have hcompl := Sesquilinear.isCompl_span_orthogonal (B := h.flip) (x := x) hx
    rw [← Submodule.finrank_add_eq_of_isCompl hcompl.symm,
      finrank_span_singleton hx0] at hd
    let N := (L ∙ x).orthogonalBilin h.flip
    have hmem : ∀ z : V, z ∈ N ↔ h z x = 0 := by
      intro z
      change z ∈ (L ∙ x).orthogonalBilin h.flip ↔ _
      rw [Submodule.orthogonalBilin_span_singleton]
      rfl
    let h' := h.domRestrict₁₂ N N
    have hbar' : ∀ a b : N, (fieldInvolution K L).bar (h' a b) = h' b a :=
      fun a b => hbar a b
    have hn' : ∀ a : N, (∀ b : N, h' a b = 0) → a = 0 := by
      intro a ha
      apply Subtype.ext
      apply hn
      intro v
      let c : L := h v x / h x x
      have hw : v - c • x ∈ N := by
        rw [hmem]
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
          smul_eq_mul, c, div_mul_cancel₀ _ hx, sub_self]
      have hax : h (a : V) x = 0 := (hmem a).1 a.property
      have h1 : h (a : V) (v - c • x) = 0 := ha ⟨_, hw⟩
      have hv : v = (v - c • x) + c • x := by abel
      rw [hv, map_add, map_smulₛₗ, h1, hax, smul_zero, add_zero]
    obtain ⟨b', hb', hb'0⟩ := ih h' hbar' hn' (Nat.succ.inj hd)
    let b := Basis.mkFinCons x b'
      (by
        rintro c y hy hc
        rw [add_eq_zero_iff_neg_eq] at hc
        rw [← hc, Submodule.neg_mem_iff] at hy
        have hdj := hcompl.disjoint
        rw [Submodule.disjoint_def] at hdj
        have hz := hdj (c • x)
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) hy
        exact (smul_eq_zero.mp hz).resolve_right hx0)
      (by
        intro y
        refine ⟨-h y x / h x x, ?_⟩
        rw [hmem]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, div_mul_cancel₀ _ hx, add_neg_cancel])
    refine ⟨b, ?_, ?_⟩
    · rw [Basis.coe_mkFinCons]
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
        simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
      · exact (hij rfl).elim
      · change h x (b' j : V) = 0
        rw [← hbar, (hmem _).1 (b' j).property, map_zero]
      · exact (hmem _).1 (b' i).property
      · exact hb' (ne_of_apply_ne _ hij)
    · rw [Basis.coe_mkFinCons]
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa only [Fin.cons_zero] using hx
      · simp only [Fin.cons_succ, Function.comp_apply]
        exact hb'0 i

section Chosen

variable [FiniteDimensional L V] (hn : ∀ x, (∀ y, h x y = 0) → x = 0)

/-- A chosen orthogonal basis with nonzero self-pairings for a Hermitian space whose
pairing separates points on the left. -/
def orthogonalBasisOfSeparatingLeft : Basis (Fin (finrank L V)) L V :=
  Classical.choose (exists_orthogonal_basis_of_separatingLeft h hbar hn)

theorem orthogonalBasisOfSeparatingLeft_isOrtho :
    h.IsOrthoᵢ (orthogonalBasisOfSeparatingLeft h hbar hn) :=
  (Classical.choose_spec (exists_orthogonal_basis_of_separatingLeft h hbar hn)).1

theorem orthogonalBasisOfSeparatingLeft_pairing_self_ne_zero (i : Fin (finrank L V)) :
    h (orthogonalBasisOfSeparatingLeft h hbar hn i)
      (orthogonalBasisOfSeparatingLeft h hbar hn i) ≠ 0 :=
  (Classical.choose_spec (exists_orthogonal_basis_of_separatingLeft h hbar hn)).2 i

/-- The diagonal form of self-pairings in the chosen orthogonal basis. -/
def diagonalFormOfSeparatingLeft : DiagonalForm (fieldInvolution K L) (Fin (finrank L V)) where
  weight i := h (orthogonalBasisOfSeparatingLeft h hbar hn i)
    (orthogonalBasisOfSeparatingLeft h hbar hn i)
  bar_weight _i := hbar _ _

/-- The coordinates in the chosen orthogonal basis. -/
def diagonalCoordinatesOfSeparatingLeft : V ≃ₗ[L] (Fin (finrank L V) → L) :=
  (orthogonalBasisOfSeparatingLeft h hbar hn).equivFun

/-- Every weight of the chosen diagonal form is nonzero. -/
theorem diagonalFormOfSeparatingLeft_weight_ne_zero (i : Fin (finrank L V)) :
    (diagonalFormOfSeparatingLeft h hbar hn).weight i ≠ 0 :=
  orthogonalBasisOfSeparatingLeft_pairing_self_ne_zero h hbar hn i

/-- The chosen coordinates carry the Hermitian pairing to the diagonal pairing. -/
theorem diagonalFormOfSeparatingLeft_pairing (x y : V) :
    (diagonalFormOfSeparatingLeft h hbar hn).pairing
      (diagonalCoordinatesOfSeparatingLeft h hbar hn x)
      (diagonalCoordinatesOfSeparatingLeft h hbar hn y) = h x y :=
  (pairing_eq_diagonal_sum h (orthogonalBasisOfSeparatingLeft h hbar hn)
    (orthogonalBasisOfSeparatingLeft_isOrtho h hbar hn) x y).symm

end Chosen

include hbar in
/-- A nondegenerate Hermitian space has diagonal coordinates with nonzero weights. -/
theorem exists_nondegenerate_diagonal_coordinates [FiniteDimensional L V]
    (hn : ∀ x, (∀ y, h x y = 0) → x = 0) :
    ∃ H : DiagonalForm (fieldInvolution K L) (Fin (finrank L V)),
      (∀ i, H.weight i ≠ 0) ∧
      ∃ e : V ≃ₗ[L] (Fin (finrank L V) → L), ∀ x y, H.pairing (e x) (e y) = h x y :=
  ⟨diagonalFormOfSeparatingLeft h hbar hn,
    diagonalFormOfSeparatingLeft_weight_ne_zero h hbar hn,
    diagonalCoordinatesOfSeparatingLeft h hbar hn,
    diagonalFormOfSeparatingLeft_pairing h hbar hn⟩

variable {h}

include hbar in
/-- The middle of a hyperbolic splitting of a left-separating Hermitian space is
again left-separating. -/
theorem hyperbolicMiddle_separatingLeft {x y : V}
    (hxx : h x x = 0) (hxy : h x y = 1) (hyx : h y x = 1) (hyy : h y y = 0)
    (hn : ∀ v, (∀ w, h v w = 0) → v = 0) (z : hyperbolicMiddle h x y)
    (hz : ∀ w : hyperbolicMiddle h x y, h (z : V) (w : V) = 0) : z = 0 := by
  apply Subtype.ext
  apply hn
  intro w
  have hp := hyperbolicCoordinates_pairing hbar hxx hxy hyx hyy (z : V) w
  have hzm := (mem_hyperbolicMiddle h x y (z : V)).1 z.property
  have hz1 : (hyperbolicCoordinates hxx hxy hyx hyy (z : V)).1 = 0 := hzm.2
  have hz3 : (hyperbolicCoordinates hxx hxy hyx hyy (z : V)).2.2 = 0 := hzm.1
  have hzp : ((hyperbolicCoordinates hxx hxy hyx hyy (z : V)).2.1 : V) = z := by
    change (hyperbolicProjection hxx hxy hyx hyy (z : V) : V) = z
    rw [hyperbolicProjection_val, hzm.1, hzm.2, zero_smul, zero_smul, sub_zero, sub_zero]
  rw [hp, hz1, hz3, hzp, hz]
  simp

include hbar in
/-- A nondegenerate Hermitian space containing a nonzero isotropic vector has
explicit linear coordinates with one hyperbolic plane and a negative diagonal middle
with nonzero weights, in every characteristic. -/
theorem exists_isotropic_diagonal_coordinates [FiniteDimensional L V]
    (hn : h.Nondegenerate) {x : V} (hx : x ≠ 0) (hxx : h x x = 0)
    (m : ℕ) (hdim : Module.finrank L V = m + 2) :
    ∃ H : DiagonalForm (fieldInvolution K L) (Fin m), (∀ i, H.weight i ≠ 0) ∧
      ∃ e : V ≃ₗ[L] L × ((Fin m → L) × L), ∀ v w,
        h v w = (e v).1 * (fieldInvolution K L).bar (e w).2.2 -
          H.pairing (e v).2.1 (e w).2.1 +
          (e v).2.2 * (fieldInvolution K L).bar (e w).1 := by
  obtain ⟨y, hxy, hyx, hyy⟩ := exists_hyperbolic_partner h hbar hn hx hxx
  have hm : Module.finrank L (hyperbolicMiddle h x y) = m := by
    have hd := hyperbolicMiddle_finrank hxx hxy hyx hyy
    omega
  have hsep : ∀ p : hyperbolicMiddle h x y,
      (∀ q, negativeMiddlePairing h x y p q = 0) → p = 0 := by
    intro p hp
    apply hyperbolicMiddle_separatingLeft hbar hxx hxy hyx hyy hn.1 p
    intro q
    exact neg_eq_zero.mp (hp q)
  have hdiag := exists_nondegenerate_diagonal_coordinates
    (negativeMiddlePairing h x y) (negativeMiddlePairing_bar hbar) hsep
  rw [hm] at hdiag
  obtain ⟨H, hH, f, hf⟩ := hdiag
  let e₀ := hyperbolicCoordinates hxx hxy hyx hyy
  let e := e₀.trans ((LinearEquiv.refl L L).prodCongr
    (f.prodCongr (LinearEquiv.refl L L)))
  refine ⟨H, hH, e, ?_⟩
  intro v w
  have hp := hyperbolicCoordinates_pairing hbar hxx hxy hyx hyy v w
  have hf' := hf (e₀ v).2.1 (e₀ w).2.1
  change H.pairing (f (e₀ v).2.1) (f (e₀ w).2.1) =
    -h ((e₀ v).2.1 : V) ((e₀ w).2.1 : V) at hf'
  change h v w = (e₀ v).1 * (fieldInvolution K L).bar (e₀ w).2.2 -
    H.pairing (f (e₀ v).2.1) (f (e₀ w).2.1) +
    (e₀ v).2.2 * (fieldInvolution K L).bar (e₀ w).1
  rw [hf', sub_neg_eq_add]
  exact hp

/-- Coordinates on the top, middle and bottom indices of a hyperbolic plane with a
middle space. -/
def indexCoordinates (A : Type*) [CommRing A] (ι : Type*) :
    (Index ι → A) ≃ₗ[A] A × ((ι → A) × A) :=
  indexProductCoordinates (A := A) (ι := ι)

@[simp] theorem indexCoordinates_apply_fst {A : Type*} [CommRing A] {ι : Type*}
    (f : Index ι → A) : (indexCoordinates A ι f).1 = f (Sum.inl ()) := rfl

@[simp] theorem indexCoordinates_apply_snd_fst {A : Type*} [CommRing A] {ι : Type*}
    (f : Index ι → A) (i : ι) :
    (indexCoordinates A ι f).2.1 i = f (Sum.inr (Sum.inl i)) := rfl

@[simp] theorem indexCoordinates_apply_snd_snd {A : Type*} [CommRing A] {ι : Type*}
    (f : Index ι → A) : (indexCoordinates A ι f).2.2 = f (Sum.inr (Sum.inr ())) := rfl

/-- The middle coordinates of the top standard basis vector vanish. -/
@[simp] theorem indexCoordinates_single_top_middle {A : Type*} [CommRing A] {ι : Type*}
    [DecidableEq ι] : (indexCoordinates A ι (Pi.single (Sum.inl ()) 1)).2.1 = 0 := by
  funext k
  simp

/-- The middle coordinates of the bottom standard basis vector vanish. -/
@[simp] theorem indexCoordinates_single_bottom_middle {A : Type*} [CommRing A] {ι : Type*}
    [DecidableEq ι] :
    (indexCoordinates A ι (Pi.single (Sum.inr (Sum.inr ())) 1)).2.1 = 0 := by
  funext k
  simp

/-- The middle coordinates of a standard basis vector at a middle index. -/
theorem indexCoordinates_single_middle {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι]
    (i : ι) :
    (indexCoordinates A ι (Pi.single (Sum.inr (Sum.inl i)) 1)).2.1 = Pi.single i 1 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

/-- The diagonal pairing of two standard basis vectors. -/
theorem DiagonalForm.pairing_single_single {A : Type*} [CommRing A] {c : RingInvolution A}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : DiagonalForm c ι) (i j : ι) :
    H.pairing (Pi.single i 1) (Pi.single j 1) = Matrix.diagonal H.weight i j := by
  rw [DiagonalForm.pairing, Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  · intro k _ hk
    simp [Pi.single_apply, hk]
  · simp

include hbar in
/-- A nondegenerate Hermitian space of dimension `m + 2` containing a nonzero
isotropic vector has a basis indexed by `Index (Fin m)` whose Gram matrix is the
hyperbolic-plus-negative-diagonal matrix `gram H`, with nonzero weights, in every
characteristic. -/
theorem exists_isotropic_gram_basis [FiniteDimensional L V]
    (hn : h.Nondegenerate) {x : V} (hx : x ≠ 0) (hxx : h x x = 0)
    (m : ℕ) (hdim : Module.finrank L V = m + 2) :
    ∃ H : DiagonalForm (fieldInvolution K L) (Fin m), (∀ i, H.weight i ≠ 0) ∧
      ∃ b : Basis (Index (Fin m)) L V, ∀ i j, h (b i) (b j) = gram H i j := by
  obtain ⟨H, hH, e, he⟩ := exists_isotropic_diagonal_coordinates hbar hn hx hxx m hdim
  refine ⟨H, hH, Basis.ofEquivFun (e.trans (indexCoordinates L (Fin m)).symm), ?_⟩
  intro i j
  rw [Basis.coe_ofEquivFun, he]
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rcases i with ⟨⟨⟩⟩ | i | ⟨⟨⟩⟩ <;> rcases j with ⟨⟨⟩⟩ | j | ⟨⟨⟩⟩
  · simp [gram, Matrix.fromBlocks]
  · simp [gram, Matrix.fromBlocks]
  · simp [gram, Matrix.fromBlocks]
  · simp [gram, Matrix.fromBlocks]
  · rw [indexCoordinates_single_middle, indexCoordinates_single_middle,
      DiagonalForm.pairing_single_single]
    by_cases hij : i = j
    · subst hij
      simp [gram, Matrix.fromBlocks]
    · simp [gram, Matrix.fromBlocks, hij]
  · simp [gram, Matrix.fromBlocks]
  · simp [gram, Matrix.fromBlocks]
  · simp [gram, Matrix.fromBlocks]
  · simp [gram, Matrix.fromBlocks]

/-- The Gram matrix `gram H` is symmetric. -/
theorem gram_apply_comm {A : Type*} [CommRing A] {c : RingInvolution A} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (H : DiagonalForm c ι) (i j : Index ι) :
    gram H i j = gram H j i := by
  rcases i with ⟨⟨⟩⟩ | i | ⟨⟨⟩⟩ <;> rcases j with ⟨⟨⟩⟩ | j | ⟨⟨⟩⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · by_cases hij : i = j
    · subst hij
      rfl
    · simp [gram, Matrix.fromBlocks, hij, Ne.symm hij]
  · rfl
  · rfl
  · rfl
  · rfl

section MatrixPairing

open Matrix

variable {ι : Type*} [Fintype ι]

variable (K) in
/-- The pairing `(v, w) ↦ ∑ k, bar (w k) * (M v) k` on column vectors defined by a
square matrix `M`; it is linear in `v` and conjugate-linear in `w`. -/
def matrixHermitianPairing (M : Matrix ι ι L) :
    (ι → L) →ₗ[L] (ι → L) →ₛₗ[(fieldInvolution K L).bar.toRingHom] L :=
  LinearMap.mk₂'ₛₗ (RingHom.id L) (fieldInvolution K L).bar.toRingHom
    (fun v w => ∑ k, (fieldInvolution K L).bar (w k) * (M *ᵥ v) k)
    (fun v₁ v₂ w => by
      simp only [Matrix.mulVec_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a v w => by
      simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun v w₁ w₂ => by
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun a v w => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by
        change _ = (fieldInvolution K L).bar a * _
        ring)

theorem matrixHermitianPairing_apply (M : Matrix ι ι L) (v w : ι → L) :
    matrixHermitianPairing K M v w =
      ∑ k, (fieldInvolution K L).bar (w k) * (M *ᵥ v) k := rfl

/-- A matrix with `bar (M k l) = M l k` defines a Hermitian pairing. -/
theorem matrixHermitianPairing_bar {M : Matrix ι ι L}
    (hM : ∀ k l, (fieldInvolution K L).bar (M k l) = M l k) (v w : ι → L) :
    (fieldInvolution K L).bar (matrixHermitianPairing K M v w) =
      matrixHermitianPairing K M w v := by
  simp only [matrixHermitianPairing_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    RingInvolution.bar_bar, hM, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- A matrix with `bar (M k l) = M l k` and nonzero determinant defines a
nondegenerate Hermitian pairing. -/
theorem matrixHermitianPairing_nondegenerate [DecidableEq ι] {M : Matrix ι ι L}
    (hM : ∀ k l, (fieldInvolution K L).bar (M k l) = M l k) (hdet : M.det ≠ 0) :
    (matrixHermitianPairing K M).Nondegenerate := by
  have hleft : ∀ v, (∀ w, matrixHermitianPairing K M v w = 0) → v = 0 := by
    intro v hv
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext k
    have hk := hv (Pi.single k 1)
    rw [matrixHermitianPairing_apply, Finset.sum_eq_single k] at hk
    · simpa using hk
    · intro l _ hl
      simp [hl]
    · simp
  refine ⟨hleft, fun w hw => hleft w fun v => ?_⟩
  rw [← matrixHermitianPairing_bar hM, hw v, map_zero]

/-- The entries of `Pᴴ M P` are the pairings of the columns of `P`. -/
theorem conjugateTranspose_mul_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M P : Matrix (Index ι) (Index ι) L) (i j : Index ι) :
    (conjugateTranspose (fieldInvolution K L) P * M * P) i j =
      matrixHermitianPairing K M (fun k => P k j) (fun k => P k i) := by
  simp only [matrixHermitianPairing_apply, Matrix.mul_apply, conjugateTranspose,
    Matrix.transpose_apply, Matrix.map_apply, Matrix.mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end MatrixPairing

end Langlands.GroupScheme.HermitianRoot
