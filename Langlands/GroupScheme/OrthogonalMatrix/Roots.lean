import Langlands.GroupScheme.OrthogonalMatrix.Torus
import Langlands.GroupScheme.Torus.SelfCentralizingFromLie
import Langlands.GroupScheme.Lie.SplitTorusCoordinates
import Langlands.GroupScheme.Lie.IdentityComponentWeights

/-! # Maximality of the diagonal torus of the split orthogonal group and its roots

The polar matrix `J` is the permutation matrix of `Sum.swap`, so the Lie condition reads
`Y x (swap y) + Y y (swap x) = 0` and `Y x (swap x) = 0`. The zero weight space of the diagonal
torus consists of the matrices `diag(d, -d)`, so the torus factored through the identity
component is a maximal torus there. The roots are the weight differences `w(x) - w(y)` with
`x` and `y` of different indices, i.e. `±e_a ± e_b` with `a ≠ b`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

open SymplecticMatrix (torusWeights weightCoord weightCoord_inl weightCoord_inr
  weightCoord_injective)

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### Indices and swaps -/

section Index

/-- The index `a` of `inl a` and of `inr a`. -/
def index (x : l ⊕ l) : l :=
  Sum.elim id id x

omit [Fintype l] [DecidableEq l] in
@[simp] theorem index_inl (a : l) : index (Sum.inl a) = a := rfl

omit [Fintype l] [DecidableEq l] in
@[simp] theorem index_inr (a : l) : index (Sum.inr a) = a := rfl

omit [Fintype l] [DecidableEq l] in
@[simp] theorem index_swap (x : l ⊕ l) : index x.swap = index x := by
  rcases x with a | a <;> rfl

omit [Fintype l] [DecidableEq l] in
theorem eq_or_eq_swap_of_index_eq {x y : l ⊕ l} (h : index x = index y) :
    x = y ∨ x = y.swap := by
  rcases x with a | a <;> rcases y with b | b <;> simp_all

omit [Fintype l] [DecidableEq l] in
theorem swap_ne_self (x : l ⊕ l) : x.swap ≠ x := by
  rcases x with a | a <;> simp

omit [Fintype l] [DecidableEq l] in
theorem eq_swap_iff {x y : l ⊕ l} : x = y.swap ↔ y = x.swap := by
  constructor <;> rintro rfl <;> simp

omit [Fintype l] in
theorem weightCoord_swap (x : l ⊕ l) : weightCoord l x.swap = -weightCoord l x := by
  rcases x with a | a
  · rw [Sum.swap_inl, weightCoord_inr, weightCoord_inl, Pi.single_neg]
  · rw [Sum.swap_inr, weightCoord_inr, weightCoord_inl, Pi.single_neg, neg_neg]

end Index

/-! ### The Lie condition in swap form -/

section Entries

variable {A : Type*} [CommRing A]

omit [Fintype l] in
theorem polarMatrix_apply (z y : l ⊕ l) :
    polarMatrix l A z y = if z = y.swap then 1 else 0 := by
  rcases z with a | a <;> rcases y with b | b <;> simp [polarMatrix, Matrix.one_apply]

theorem mul_polarMatrix_apply (Y : Matrix (l ⊕ l) (l ⊕ l) A) (x y : l ⊕ l) :
    (Y * polarMatrix l A) x y = Y x y.swap := by
  simp [Matrix.mul_apply, polarMatrix_apply]

theorem polarMatrix_mul_apply (M : Matrix (l ⊕ l) (l ⊕ l) A) (x y : l ⊕ l) :
    (polarMatrix l A * M) x y = M x.swap y := by
  simp only [Matrix.mul_apply, polarMatrix_apply, ite_mul, one_mul, zero_mul]
  simp_rw [eq_swap_iff (x := x)]
  simp

/-- **The orthogonal Lie condition in swap form.** `Y Q + Q Yᵀ` is alternating exactly when
`Y x (swap y) + Y y (swap x) = 0` and `Y x (swap x) = 0` for all indices. -/
theorem isAlt_lie_iff_swap (Y : Matrix (l ⊕ l) (l ⊕ l) A) :
    IsAlt (Y * formMatrix l A + formMatrix l A * Yᵀ) ↔
      (∀ x y, Y x y.swap + Y y x.swap = 0) ∧ ∀ x, Y x x.swap = 0 := by
  rw [isAlt_lie_iff]
  refine and_congr ⟨fun h x y => ?_, fun h => ?_⟩ ⟨fun h x => ?_, fun h a => ?_⟩
  · have h1 := congrFun (congrFun h x) y
    rwa [Matrix.add_apply, mul_polarMatrix_apply, polarMatrix_mul_apply, Matrix.transpose_apply,
      Matrix.zero_apply] at h1
  · ext x y
    rw [Matrix.add_apply, mul_polarMatrix_apply, polarMatrix_mul_apply, Matrix.transpose_apply,
      Matrix.zero_apply]
    exact h x y
  · rcases x with a | a
    · exact (h a).1
    · exact (h a).2
  · exact ⟨h (Sum.inl a), h (Sum.inr a)⟩

/-- The diagonal matrix `diag(d, -d)` satisfies the Lie condition. -/
theorem isAlt_diagonal_lie (d : l → A) :
    IsAlt (Matrix.diagonal (Sum.elim d (fun a => -d a)) * formMatrix l A +
      formMatrix l A * (Matrix.diagonal (Sum.elim d (fun a => -d a)))ᵀ) := by
  rw [isAlt_lie_iff_swap]
  refine ⟨fun x y => ?_, fun x => Matrix.diagonal_apply_ne _ (swap_ne_self x).symm⟩
  by_cases h : x = y.swap
  · subst h
    rw [Sum.swap_swap, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    rcases y with a | a <;> simp
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (eq_swap_iff.mpr e)),
      add_zero]

/-- The root vector `E_{x y} - E_{swap y, swap x}` satisfies the Lie condition. -/
theorem isAlt_rootVector_lie (x y : l ⊕ l) :
    IsAlt ((Matrix.single x y (1 : A) - Matrix.single y.swap x.swap 1) * formMatrix l A +
      formMatrix l A * (Matrix.single x y (1 : A) - Matrix.single y.swap x.swap 1)ᵀ) := by
  rw [isAlt_lie_iff_swap]
  have hs : ∀ u v : l ⊕ l, u.swap = v.swap ↔ u = v := fun u v =>
    ⟨fun h => by simpa using congrArg Sum.swap h, fun h => h ▸ rfl⟩
  have ht : ∀ u v : l ⊕ l, u = v.swap ↔ u.swap = v := fun u v => by
    rw [eq_swap_iff, eq_comm]
  refine ⟨fun z w => ?_, fun z => ?_⟩
  · simp only [Matrix.sub_apply, Matrix.single_apply, hs x w, hs x z, ht y w, ht y z,
      and_comm (a := x = w), and_comm (a := y.swap = w)]
    ring
  · simp only [Matrix.sub_apply, Matrix.single_apply, hs x z, ht y z, and_comm (a := x = z)]
    ring

end Entries

/-! ### Lie entries -/

section LieEntries

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]

theorem lieMatrix_swap_add (X : Additive (lieKernel (groupScheme l R) A)) (x y : l ⊕ l) :
    lieMatrix X x y.swap + lieMatrix X y x.swap = 0 :=
  ((isAlt_lie_iff_swap _).mp (isAlt_lieMatrix X)).1 x y

theorem lieMatrix_swap_self (X : Additive (lieKernel (groupScheme l R) A)) (x : l ⊕ l) :
    lieMatrix X x x.swap = 0 :=
  ((isAlt_lie_iff_swap _).mp (isAlt_lieMatrix X)).2 x

theorem lieMatrix_inr_inr (X : Additive (lieKernel (groupScheme l R) A)) (a b : l) :
    lieMatrix X (Sum.inr a) (Sum.inr b) = -lieMatrix X (Sum.inl b) (Sum.inl a) := by
  have h := lieMatrix_swap_add X (Sum.inr a) (Sum.inl b)
  rw [Sum.swap_inl, Sum.swap_inr] at h
  linear_combination h

end LieEntries

/-! ### Maximality over a field -/

section Field

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- The zero weight space consists of the Lie algebra elements with diagonal matrix. -/
theorem mem_weightSpace_zero_iff
    (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k)) :
    X ∈ weightSpace (diagonalTorus l (CommRingCat.of k)) 0 ↔
      ∀ x y : l ⊕ l, x ≠ y → lieMatrix X x y = 0 := by
  rw [mem_weightSpace_diagonalTorus_iff_support, map_zero]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  have hw : (0 : l → ℤ) = weightCoord l x - weightCoord l y ↔ x = y := by
    rw [eq_comm, sub_eq_zero]
    exact weightCoord_injective.eq_iff
  rw [hw]
  exact not_imp_comm

variable (l k) in
/-- The upper-left diagonal entries of an element of the zero weight space. -/
def zeroWeightCoord :
    weightSpace (diagonalTorus l (CommRingCat.of k)) 0 →ₗ[k] (l → k) where
  toFun X a := lieMatrix (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k))
    (Sum.inl a) (Sum.inl a)
  map_add' X Y := by
    funext a
    simp only [Submodule.coe_add, map_add, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext a
    simp only [Submodule.coe_smul, map_smul, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
      RingHom.id_apply]

theorem zeroWeightCoord_apply (X : weightSpace (diagonalTorus l (CommRingCat.of k)) 0) (a : l) :
    zeroWeightCoord l k X a =
      lieMatrix (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k))
        (Sum.inl a) (Sum.inl a) :=
  rfl

/-- An element of the zero weight space is determined by its diagonal entries `X_{aa}`. -/
theorem lieMatrix_eq_zero_of_zeroWeightCoord
    (X : weightSpace (diagonalTorus l (CommRingCat.of k)) 0) (hX : zeroWeightCoord l k X = 0) :
    lieMatrix (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k)) = 0 := by
  obtain ⟨Xv, hXv⟩ := X
  have hd : ∀ x y : l ⊕ l, x ≠ y → lieMatrix Xv x y = 0 := (mem_weightSpace_zero_iff Xv).mp hXv
  have h0 : ∀ a, lieMatrix Xv (Sum.inl a) (Sum.inl a) = 0 := fun a => by
    have h := congrFun hX a
    rw [zeroWeightCoord_apply, Pi.zero_apply] at h
    exact h
  change lieMatrix Xv = 0
  ext x y
  rw [Matrix.zero_apply]
  by_cases hxy : x = y
  · subst hxy
    cases x with
    | inl a => exact h0 a
    | inr a => rw [lieMatrix_inr_inr, h0 a, neg_zero]
  · exact hd x y hxy

theorem zeroWeightCoord_bijective : Function.Bijective (zeroWeightCoord l k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
    rw [lieMatrix_eq_zero_of_zeroWeightCoord X hX, Submodule.coe_zero, map_zero]
  · intro d
    obtain ⟨X, hX⟩ := exists_lieMatrix_eq (R := CommRingCat.of k) _ (isAlt_diagonal_lie d)
    have hmem : X ∈ weightSpace (diagonalTorus l (CommRingCat.of k)) 0 := by
      rw [mem_weightSpace_zero_iff, hX]
      intro x y hxy
      exact Matrix.diagonal_apply_ne _ hxy
    refine ⟨⟨X, hmem⟩, ?_⟩
    funext a
    rw [zeroWeightCoord_apply]
    change lieMatrix X (Sum.inl a) (Sum.inl a) = d a
    rw [hX, Matrix.diagonal_apply_eq, Sum.elim_inl]

/-- The zero weight space of the diagonal torus has dimension `|l|`. -/
theorem finrank_weightSpace_zero :
    Module.finrank k (weightSpace (diagonalTorus l (CommRingCat.of k)) 0) = Fintype.card l := by
  rw [(LinearEquiv.ofBijective (zeroWeightCoord l k) zeroWeightCoord_bijective).finrank_eq,
    Module.finrank_fintype_fun_eq_card]

variable (l k)

/-- The diagonal torus, factored through the identity component of `O_{2l}`. -/
def identityTorus : (𝔻).toGrp ⟶ identityComponent (groupScheme l (CommRingCat.of k)) :=
  IdentityComponent.torusHom (diagonalTorus l (CommRingCat.of k))
    (SymplecticMatrix.isSplitTorus_diagonalTorus l k)

@[reassoc (attr := simp)] theorem identityTorus_comp :
    identityTorus l k ≫ identityComponentι (groupScheme l (CommRingCat.of k)) =
      diagonalTorus l (CommRingCat.of k) :=
  IdentityComponent.torusHom_comp _ _

theorem isClosedSubgroup_identityTorus : IsClosedSubgroup (identityTorus l k) :=
  IdentityComponent.isClosedSubgroup_torusHom _ _ (isClosedSubgroup_diagonalTorus l k)

theorem isSplitSubtorus_identityTorus : IsSplitSubtorus (identityTorus l k) :=
  ⟨SymplecticMatrix.isSplitTorus_diagonalTorus l k, isClosedSubgroup_identityTorus l k⟩

/-- **Maximality.** The diagonal torus is a maximal torus of the identity component of the split
orthogonal group over a field. -/
theorem isMaximalTorus_identityTorus : IsMaximalTorus (identityTorus l k) := by
  have : IsAffineHom (𝔻).toGrp.X.hom := isAffineHom_splitTorus _ _
  refine isMaximalTorus_of_finrank_zeroWeight _ (SymplecticMatrix.isSplitTorus_diagonalTorus l k)
    (isClosedSubgroup_identityTorus l k) ?_
  rw [identityTorus, IdentityComponent.finrank_weightSpace, finrank_weightSpace_zero]
  have h := splitTorus.finrank_lieKernel (ULift.{u} l) k
  rw [Nat.card_ulift, Nat.card_eq_fintype_card] at h
  exact h.symm

theorem roots_identityTorus :
    roots (identityTorus l k) = roots (diagonalTorus l (CommRingCat.of k)) :=
  IdentityComponent.roots_torusHom _ _

variable {l k}

/-! ### Roots -/

/-- **Roots of the diagonal torus.** The roots are the weight differences `w(x) - w(y)` with
`x` and `y` of different indices: the characters `±e_a ± e_b` with `a ≠ b`. -/
theorem mem_roots_iff (χ : characterLattice 𝔻) :
    χ ∈ roots (diagonalTorus l (CommRingCat.of k)) ↔
      ∃ x y : l ⊕ l, index x ≠ index y ∧
        GeneralLinear.characterCoordEquiv l k χ = weightCoord l x - weightCoord l y := by
  constructor
  · intro hχ
    obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ.2
    obtain ⟨x, y, hxy⟩ : ∃ x y, lieMatrix X x y ≠ 0 := by
      by_contra h
      apply hX0
      apply lieMatrix_injective (R := CommRingCat.of k) (A := k)
      rw [map_zero]
      refine Matrix.ext fun x y => ?_
      rw [Matrix.zero_apply]
      by_contra hne
      exact h ⟨x, y, hne⟩
    have hc := (mem_weightSpace_diagonalTorus_iff_support X χ).mp hX x y hxy
    refine ⟨x, y, fun hidx => ?_, hc⟩
    rcases eq_or_eq_swap_of_index_eq hidx with rfl | rfl
    · apply hχ.1
      apply (GeneralLinear.characterCoordEquiv l k).injective
      rw [hc, sub_self, map_zero]
    · apply hxy
      have h := lieMatrix_swap_self X y.swap
      rwa [Sum.swap_swap] at h
  · rintro ⟨x, y, hidx, hc⟩
    have hxy : x ≠ y := fun h => hidx (congrArg index h)
    have hxy' : ¬(y.swap = x ∧ x.swap = y) := fun h => hidx (by rw [← h.1, index_swap])
    obtain ⟨X, hX⟩ := exists_lieMatrix_eq (R := CommRingCat.of k) _
      (isAlt_rootVector_lie (A := k) x y)
    refine ⟨fun h0 => ?_, ?_⟩
    · rw [h0, map_zero, eq_comm, sub_eq_zero] at hc
      exact hxy (weightCoord_injective hc)
    · rw [Submodule.ne_bot_iff]
      refine ⟨X, ?_, fun h0 => ?_⟩
      · rw [mem_weightSpace_diagonalTorus_iff_support, hX, hc]
        intro z w hzw
        simp only [Matrix.sub_apply, Matrix.single_apply] at hzw
        by_cases h1 : x = z ∧ y = w
        · rw [← h1.1, ← h1.2]
        · by_cases h2 : y.swap = z ∧ x.swap = w
          · rw [← h2.1, ← h2.2, weightCoord_swap, weightCoord_swap]
            abel
          · rw [ite_eq_right h1, ite_eq_right h2, sub_zero] at hzw
            exact absurd rfl hzw
      · have h1 := congrArg (fun Y => lieMatrix Y x y) h0
        simp only [hX, map_zero, Matrix.sub_apply, Matrix.single_apply_same, Matrix.zero_apply,
          Matrix.single_apply, ite_eq_right hxy'] at h1
        simp at h1

end Field

end Langlands.GroupScheme.OrthogonalMatrix
