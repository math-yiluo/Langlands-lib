import Langlands.Group.GL.OppositeBlocks
import Langlands.BaseChange.LeviNormDescent
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The unipotent radical of a two-block parabolic subgroup

For a block shape `B` of `n` with two blocks, the unipotent radical `U` of the standard
parabolic subgroup consists of the matrices `1 + X` with `X` strictly upper block triangular
(`mem_unipotentSubgroup_iff_isStrictUpper`); such `X` satisfy `X Y = 0`
(`IsStrictUpper.mul_eq_zero`), so `U` is commutative and `(1 + X)⁻¹ = 1 - X`.

For a block diagonal `δ = leviEmbedding m` whose blocks have coprime characteristic
polynomials, the map `u ↦ δ⁻¹ u⁻¹ δ u` is a group automorphism of `U`
(`twistMulEquiv`): in the coordinate `X = u - 1` it is the linear map
`X ↦ X - δ⁻¹ X δ` (`twistLinear`), which is injective because an element of `U` commuting
with `δ` lies in the Levi subgroup, and hence bijective. Over a Hausdorff topological field
whose general linear group is locally compact and σ-compact, the automorphism is a homeomorphism
by the open mapping theorem (`twistContinuousMulEquiv`).
-/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

open Matrix

universe u

variable {n : ℕ} (B : BlockShape n)

section Ring

variable {R : Type u} [CommRing R]

/-- A matrix is strictly upper block triangular for `B` when all its entries in the blocks on
or below the block diagonal vanish. -/
def IsStrictUpper (X : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)), j ≤ i →
    X (B.index i a) (B.index j b) = 0

omit [CommRing R] in
/-- Two matrices with the same entries in all block coordinates are equal. -/
theorem matrix_ext_index {X Y : Matrix (Fin n) (Fin n) R}
    (h : ∀ (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)),
      X (B.index i a) (B.index j b) = Y (B.index i a) (B.index j b)) : X = Y := by
  ext p q
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective p
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective q
  exact h i j a b

/-- Coordinates in distinct blocks are distinct. -/
private theorem index_ne_of_ne {i j : Fin B.length} (a : Fin (B.size i)) (b : Fin (B.size j))
    (hij : i ≠ j) : B.index i a ≠ B.index j b := by
  intro h
  exact hij (Sigma.mk.inj_iff.mp (B.indexEquiv.injective h)).1

/-- The identity matrix vanishes between coordinates of distinct blocks. -/
theorem one_apply_index_ne {i j : Fin B.length} (a : Fin (B.size i)) (b : Fin (B.size j))
    (hij : i ≠ j) : (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index j b) = 0 :=
  Matrix.one_apply_ne (B.index_ne_of_ne a b hij)

/-- The identity matrix restricted to a diagonal block is the identity. -/
theorem one_apply_index_same (i : Fin B.length) (a b : Fin (B.size i)) :
    (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index i b) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h
    simp only [Matrix.one_apply_eq, ite_true]
  · rw [Matrix.one_apply_ne ((B.index i).injective.ne h), ite_eq_right_iff.2 fun h' => (h h').elim]

/-- The zero matrix is strictly upper block triangular. -/
theorem isStrictUpper_zero : B.IsStrictUpper (0 : Matrix (Fin n) (Fin n) R) :=
  fun _ _ _ _ _ => rfl

/-- Strictly upper block triangular matrices are closed under addition. -/
theorem IsStrictUpper.add {X Y : Matrix (Fin n) (Fin n) R} (hX : B.IsStrictUpper X)
    (hY : B.IsStrictUpper Y) : B.IsStrictUpper (X + Y) := fun i j a b h => by
  rw [Matrix.add_apply, hX i j a b h, hY i j a b h, add_zero]

/-- Strictly upper block triangular matrices are closed under negation. -/
theorem IsStrictUpper.neg {X : Matrix (Fin n) (Fin n) R} (hX : B.IsStrictUpper X) :
    B.IsStrictUpper (-X) := fun i j a b h => by
  rw [Matrix.neg_apply, hX i j a b h, neg_zero]

/-- Strictly upper block triangular matrices are closed under subtraction. -/
theorem IsStrictUpper.sub {X Y : Matrix (Fin n) (Fin n) R} (hX : B.IsStrictUpper X)
    (hY : B.IsStrictUpper Y) : B.IsStrictUpper (X - Y) := fun i j a b h => by
  rw [Matrix.sub_apply, hX i j a b h, hY i j a b h, sub_zero]

/-- Strictly upper block triangular matrices are closed under scalar multiplication. -/
theorem IsStrictUpper.smul {X : Matrix (Fin n) (Fin n) R} (hX : B.IsStrictUpper X) (c : R) :
    B.IsStrictUpper (c • X) := fun i j a b h => by
  rw [Matrix.smul_apply, hX i j a b h, smul_zero]

/-- For a two-block shape, the product of two strictly upper block triangular matrices
vanishes. -/
theorem IsStrictUpper.mul_eq_zero (hB : B.length = 2) {X Y : Matrix (Fin n) (Fin n) R}
    (hX : B.IsStrictUpper X) (hY : B.IsStrictUpper Y) : X * Y = 0 := by
  refine B.matrix_ext_index fun i j a b => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply, ← Equiv.sum_comp B.indexEquiv]
  refine Finset.sum_eq_zero fun s _ => ?_
  obtain ⟨l, c⟩ := s
  change X (B.index i a) (B.index l c) * Y (B.index l c) (B.index j b) = 0
  by_cases hli : l ≤ i
  · rw [hX i l a c hli, zero_mul]
  · have hjl : j ≤ l := by
      rw [not_le, Fin.lt_def] at hli
      rw [Fin.le_iff_val_le_val]
      have := j.isLt
      omega
    rw [hY l j c b hjl, mul_zero]

/-- The unipotent radical consists of the invertible matrices `g` with `g - 1` strictly upper
block triangular. -/
theorem mem_unipotentSubgroup_iff_isStrictUpper (g : Langlands.GeneralLinear n R) :
    g ∈ B.unipotentSubgroup R ↔ B.IsStrictUpper ((g : Matrix (Fin n) (Fin n) R) - 1) := by
  rw [B.mem_unipotentSubgroup_iff, B.mem_parabolic_iff]
  constructor
  · rintro ⟨hP, hd⟩ i j a b hji
    rw [Matrix.sub_apply]
    rcases hji.lt_or_eq with hlt | rfl
    · rw [B.one_apply_index_ne a b (ne_of_lt hlt).symm, sub_zero]
      exact hP i j a b hlt
    · rw [B.one_apply_index_same, sub_eq_zero]
      exact hd j a b
  · intro h
    refine ⟨fun i j a b hlt => ?_, fun i a b => ?_⟩
    · have := h i j a b hlt.le
      rwa [Matrix.sub_apply, B.one_apply_index_ne a b (ne_of_lt hlt).symm, sub_zero] at this
    · have := h i i a b le_rfl
      rwa [Matrix.sub_apply, sub_eq_zero, B.one_apply_index_same] at this

variable {B}

/-- For a two-block shape, `1 + X` is invertible with inverse `1 - X` when `X` is strictly
upper block triangular. -/
def unipotentOfStrictUpper (hB : B.length = 2) {X : Matrix (Fin n) (Fin n) R}
    (hX : B.IsStrictUpper X) : Langlands.GeneralLinear n R where
  val := 1 + X
  inv := 1 - X
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, IsStrictUpper.mul_eq_zero B hB hX hX, sub_zero,
      sub_add_cancel]
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, IsStrictUpper.mul_eq_zero B hB hX hX, add_zero,
      add_sub_cancel_right]

@[simp] theorem unipotentOfStrictUpper_val (hB : B.length = 2) {X : Matrix (Fin n) (Fin n) R}
    (hX : B.IsStrictUpper X) :
    ((unipotentOfStrictUpper hB hX : Langlands.GeneralLinear n R) : Matrix (Fin n) (Fin n) R) =
      1 + X := rfl

/-- The matrix `1 + X` lies in the unipotent radical. -/
theorem unipotentOfStrictUpper_mem (hB : B.length = 2) {X : Matrix (Fin n) (Fin n) R}
    (hX : B.IsStrictUpper X) : unipotentOfStrictUpper hB hX ∈ B.unipotentSubgroup R := by
  rw [B.mem_unipotentSubgroup_iff_isStrictUpper, unipotentOfStrictUpper_val, add_sub_cancel_left]
  exact hX

/-- For a two-block shape, the inverse of an element `u` of the unipotent radical is
`2 - u`, that is `1 - (u - 1)`. -/
theorem inv_val_of_mem_unipotentSubgroup (hB : B.length = 2) {u : Langlands.GeneralLinear n R}
    (hu : u ∈ B.unipotentSubgroup R) :
    ((u⁻¹ : Langlands.GeneralLinear n R) : Matrix (Fin n) (Fin n) R) =
      1 - ((u : Matrix (Fin n) (Fin n) R) - 1) := by
  have hX := (B.mem_unipotentSubgroup_iff_isStrictUpper u).1 hu
  have h : u = unipotentOfStrictUpper hB hX := by
    apply Units.ext
    rw [unipotentOfStrictUpper_val, add_sub_cancel]
  conv_lhs => rw [h]
  rfl

/-- For a two-block shape, the unipotent radical is commutative. -/
theorem mul_comm_of_mem_unipotentSubgroup (hB : B.length = 2) {u v : Langlands.GeneralLinear n R}
    (hu : u ∈ B.unipotentSubgroup R) (hv : v ∈ B.unipotentSubgroup R) : u * v = v * u := by
  have hX := (B.mem_unipotentSubgroup_iff_isStrictUpper u).1 hu
  have hY := (B.mem_unipotentSubgroup_iff_isStrictUpper v).1 hv
  have h1 := IsStrictUpper.mul_eq_zero B hB hX hY
  have h2 := IsStrictUpper.mul_eq_zero B hB hY hX
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have e1 : (u : Matrix (Fin n) (Fin n) R) * v =
      ((u : Matrix (Fin n) (Fin n) R) - 1) * ((v : Matrix (Fin n) (Fin n) R) - 1) + u + v - 1 := by
    noncomm_ring
  have e2 : (v : Matrix (Fin n) (Fin n) R) * u =
      ((v : Matrix (Fin n) (Fin n) R) - 1) * ((u : Matrix (Fin n) (Fin n) R) - 1) + v + u - 1 := by
    noncomm_ring
  rw [e1, e2, h1, h2]
  abel

end Ring

section Field

variable {F : Type u} [Field F]

/-- Conjugation by a Levi element preserves strictly upper block triangular matrices (for a
two-block shape). -/
theorem IsStrictUpper.levi_conj {B : BlockShape n} (hB : B.length = 2) (m : B.Levi F)
    {X : Matrix (Fin n) (Fin n) F} (hX : B.IsStrictUpper X) :
    B.IsStrictUpper (((B.leviEmbedding F m : Langlands.GeneralLinear n F) :
      Matrix (Fin n) (Fin n) F) * X *
      (((B.leviEmbedding F m)⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F)) := by
  have hmem := B.levi_conj_mem_unipotentSubgroup F m (unipotentOfStrictUpper_mem hB hX)
  rw [B.mem_unipotentSubgroup_iff_isStrictUpper, Units.val_mul, Units.val_mul,
    unipotentOfStrictUpper_val] at hmem
  have e : ((B.leviEmbedding F m : Langlands.GeneralLinear n F) :
      Matrix (Fin n) (Fin n) F) * (1 + X) *
      (((B.leviEmbedding F m)⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) - 1 =
      ((B.leviEmbedding F m : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * X *
      (((B.leviEmbedding F m)⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) := by
    rw [mul_add, mul_one, add_mul, Units.mul_inv, add_sub_cancel_left]
  rwa [e] at hmem

variable (F) in
/-- The subspace of strictly upper block triangular matrices. -/
def strictUpper : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {X | B.IsStrictUpper X}
  add_mem' hX hY := IsStrictUpper.add B hX hY
  zero_mem' := B.isStrictUpper_zero
  smul_mem' c _ hX := IsStrictUpper.smul B hX c

variable {B}

/-- The linear map `X ↦ X - δ⁻¹ X δ` on strictly upper block triangular matrices, for
`δ = leviEmbedding m` and a two-block shape. -/
def twistLinear (hB : B.length = 2) (m : B.Levi F) :
    B.strictUpper F →ₗ[F] B.strictUpper F where
  toFun X := ⟨X.1 - (((B.leviEmbedding F m)⁻¹ : Langlands.GeneralLinear n F) :
      Matrix (Fin n) (Fin n) F) * X.1 *
      ((B.leviEmbedding F m : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F), by
    have h := IsStrictUpper.levi_conj hB m⁻¹ X.2
    rw [map_inv, inv_inv] at h
    exact IsStrictUpper.sub B X.2 h⟩
  map_add' X Y := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    rw [mul_add, add_mul]
    abel
  map_smul' c X := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

@[simp] theorem twistLinear_apply_coe (hB : B.length = 2) (m : B.Levi F)
    (X : B.strictUpper F) :
    (twistLinear hB m X : Matrix (Fin n) (Fin n) F) =
      X.1 - (((B.leviEmbedding F m)⁻¹ : Langlands.GeneralLinear n F) :
        Matrix (Fin n) (Fin n) F) * X.1 *
        ((B.leviEmbedding F m : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) :=
  rfl

/-- The map `X ↦ X - δ⁻¹ X δ` is injective when the blocks of `δ` have pairwise coprime
characteristic polynomials: a strictly upper block triangular `X` commuting with `δ` vanishes,
since `1 + X` then lies in the Levi subgroup. -/
theorem twistLinear_injective (hB : B.length = 2) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    Function.Injective (twistLinear hB m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  set D : Langlands.GeneralLinear n F := B.leviEmbedding F m with hD
  have h0 : X.1 - ((D⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * X.1 *
      (D : Matrix (Fin n) (Fin n) F) = 0 := by
    have := congrArg Subtype.val hX
    rwa [twistLinear_apply_coe] at this
  have hcomm : (D : Matrix (Fin n) (Fin n) F) * X.1 = X.1 * D := by
    have e1 : X.1 = ((D⁻¹ : Langlands.GeneralLinear n F) :
          Matrix (Fin n) (Fin n) F) * X.1 * (D : Matrix (Fin n) (Fin n) F) := sub_eq_zero.1 h0
    conv_lhs => rw [e1]
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have hu : Commute (B.leviEmbedding F m) (unipotentOfStrictUpper hB X.2) := by
    apply Units.ext
    change (D : Matrix (Fin n) (Fin n) F) * (1 + X.1) = (1 + X.1) * D
    rw [mul_add, add_mul, mul_one, one_mul, hcomm]
  have hlevi := Langlands.BaseChange.mem_leviSubgroup_of_commute B m hm hu
  rw [Langlands.BaseChange.mem_leviSubgroup_iff_offBlock_eq_zero] at hlevi
  apply Subtype.ext
  refine B.matrix_ext_index fun i j a b => ?_
  rw [Submodule.coe_zero, Matrix.zero_apply]
  by_cases hij : i = j
  · subst hij
    exact X.2 i i a b le_rfl
  · have h := hlevi i j a b hij
    change (1 + X.1) (B.index i a) (B.index j b) = 0 at h
    rwa [Matrix.add_apply, B.one_apply_index_ne a b hij, zero_add] at h

/-- The map `X ↦ X - δ⁻¹ X δ` is surjective, being an injective endomorphism of a
finite-dimensional space. -/
theorem twistLinear_surjective (hB : B.length = 2) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    Function.Surjective (twistLinear hB m) :=
  LinearMap.injective_iff_surjective.1 (twistLinear_injective hB m hm)

/-- The map `u ↦ δ⁻¹ u⁻¹ δ u` on the unipotent radical of a two-block shape, for
`δ = leviEmbedding m`, as a group homomorphism. -/
def twistHom (hB : B.length = 2) (m : B.Levi F) :
    B.unipotentSubgroup F →* B.unipotentSubgroup F where
  toFun u := ⟨(B.leviEmbedding F m)⁻¹ * (u : Langlands.GeneralLinear n F)⁻¹ *
      B.leviEmbedding F m * u, by
    refine (B.unipotentSubgroup F).mul_mem ?_ u.2
    have h := B.levi_conj_mem_unipotentSubgroup F m⁻¹ ((B.unipotentSubgroup F).inv_mem u.2)
    rwa [map_inv, inv_inv] at h⟩
  map_one' := by
    apply Subtype.ext
    simp only [OneMemClass.coe_one, inv_one, mul_one, inv_mul_cancel]
  map_mul' u v := by
    apply Subtype.ext
    set D : Langlands.GeneralLinear n F := B.leviEmbedding F m
    simp only [Subgroup.coe_mul]
    have hc : ∀ {a b : Langlands.GeneralLinear n F}, a ∈ B.unipotentSubgroup F →
        b ∈ B.unipotentSubgroup F → a * b = b * a :=
      fun ha hb => mul_comm_of_mem_unipotentSubgroup hB ha hb
    have hconj : ∀ w ∈ B.unipotentSubgroup F, D⁻¹ * w⁻¹ * D ∈ B.unipotentSubgroup F := by
      intro w hw
      have h := B.levi_conj_mem_unipotentSubgroup F m⁻¹ ((B.unipotentSubgroup F).inv_mem hw)
      rwa [map_inv, inv_inv] at h
    have h1 : (u : Langlands.GeneralLinear n F) * v = v * u := hc u.2 v.2
    have h2 : (D⁻¹ * (v : Langlands.GeneralLinear n F)⁻¹ * D) * u =
        u * (D⁻¹ * (v : Langlands.GeneralLinear n F)⁻¹ * D) := hc (hconj v v.2) u.2
    calc D⁻¹ * ((u : Langlands.GeneralLinear n F) * v)⁻¹ * D * (u * v)
        = (D⁻¹ * (u : Langlands.GeneralLinear n F)⁻¹ * D) *
            ((D⁻¹ * (v : Langlands.GeneralLinear n F)⁻¹ * D) * u) * v := by
          rw [show ((u : Langlands.GeneralLinear n F) * v)⁻¹ =
            ((v : Langlands.GeneralLinear n F) * u)⁻¹ by rw [h1]]
          group
      _ = (D⁻¹ * (u : Langlands.GeneralLinear n F)⁻¹ * D) *
            (u * (D⁻¹ * (v : Langlands.GeneralLinear n F)⁻¹ * D)) * v := by rw [h2]
      _ = D⁻¹ * (u : Langlands.GeneralLinear n F)⁻¹ * D * u *
            (D⁻¹ * (v : Langlands.GeneralLinear n F)⁻¹ * D * v) := by group

@[simp] theorem twistHom_apply_coe (hB : B.length = 2) (m : B.Levi F)
    (u : B.unipotentSubgroup F) :
    ((twistHom hB m u : B.unipotentSubgroup F) : Langlands.GeneralLinear n F) =
      (B.leviEmbedding F m)⁻¹ * (u : Langlands.GeneralLinear n F)⁻¹ * B.leviEmbedding F m * u :=
  rfl

/-- In the coordinate `X = u - 1`, the homomorphism `twistHom` is `twistLinear`. -/
theorem twistHom_sub_one (hB : B.length = 2) (m : B.Levi F) (u : B.unipotentSubgroup F) :
    (((twistHom hB m u : B.unipotentSubgroup F) : Langlands.GeneralLinear n F) :
      Matrix (Fin n) (Fin n) F) - 1 =
      (twistLinear hB m ⟨((u : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) - 1,
        (B.mem_unipotentSubgroup_iff_isStrictUpper _).1 u.2⟩ : Matrix (Fin n) (Fin n) F) := by
  set D : Langlands.GeneralLinear n F := B.leviEmbedding F m with hD
  set X : Matrix (Fin n) (Fin n) F := ((u : Langlands.GeneralLinear n F) :
    Matrix (Fin n) (Fin n) F) - 1 with hXdef
  have hX : B.IsStrictUpper X := (B.mem_unipotentSubgroup_iff_isStrictUpper _).1 u.2
  have hY : B.IsStrictUpper (((D⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) *
      X * (D : Matrix (Fin n) (Fin n) F)) := by
    have h := IsStrictUpper.levi_conj hB m⁻¹ hX
    rwa [map_inv, inv_inv] at h
  have hYX := IsStrictUpper.mul_eq_zero B hB hY hX
  have hu : ((u : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) = 1 + X := by
    rw [hXdef, add_sub_cancel]
  have e : ((D⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * (1 - X) *
      (D : Matrix (Fin n) (Fin n) F) =
      1 - ((D⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * X *
        (D : Matrix (Fin n) (Fin n) F) := by
    rw [mul_sub, mul_one, sub_mul, Units.inv_mul]
  have key : ((D⁻¹ * (u : Langlands.GeneralLinear n F)⁻¹ * D * u : Langlands.GeneralLinear n F) :
      Matrix (Fin n) (Fin n) F) - 1 =
      X - ((D⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * X *
        (D : Matrix (Fin n) (Fin n) F) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, inv_val_of_mem_unipotentSubgroup hB u.2,
      ← hXdef, hu, e, sub_mul, one_mul, mul_add, mul_one, hYX, add_zero]
    abel
  exact key

/-- The homomorphism `u ↦ δ⁻¹ u⁻¹ δ u` is injective. -/
theorem twistHom_injective (hB : B.length = 2) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    Function.Injective (twistHom hB m) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h := twistHom_sub_one hB m u
  rw [hu, OneMemClass.coe_one, Units.val_one, sub_self] at h
  have h0 := twistLinear_injective hB m hm
    (show twistLinear hB m ⟨((u : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) - 1,
      (B.mem_unipotentSubgroup_iff_isStrictUpper _).1 u.2⟩ = twistLinear hB m 0 by
      rw [map_zero]
      exact Subtype.ext h.symm)
  apply Subtype.ext
  apply Units.ext
  have := congrArg Subtype.val h0
  simp only [Submodule.coe_zero] at this
  rw [OneMemClass.coe_one, Units.val_one]
  exact sub_eq_zero.1 this

/-- The homomorphism `u ↦ δ⁻¹ u⁻¹ δ u` is surjective. -/
theorem twistHom_surjective (hB : B.length = 2) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    Function.Surjective (twistHom hB m) := by
  intro v
  obtain ⟨Y, hY⟩ := twistLinear_surjective hB m hm
    ⟨((v : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) - 1,
      (B.mem_unipotentSubgroup_iff_isStrictUpper _).1 v.2⟩
  refine ⟨⟨unipotentOfStrictUpper hB Y.2, unipotentOfStrictUpper_mem hB Y.2⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have h := twistHom_sub_one hB m ⟨unipotentOfStrictUpper hB Y.2, unipotentOfStrictUpper_mem hB Y.2⟩
  have hY' : (⟨((unipotentOfStrictUpper hB Y.2 : Langlands.GeneralLinear n F) :
      Matrix (Fin n) (Fin n) F) - 1, (B.mem_unipotentSubgroup_iff_isStrictUpper _).1
        (unipotentOfStrictUpper_mem hB Y.2)⟩ : B.strictUpper F) = Y := by
    apply Subtype.ext
    change 1 + Y.1 - 1 = Y.1
    rw [add_sub_cancel_left]
  rw [hY', hY] at h
  exact sub_left_injective h

/-- The automorphism `u ↦ δ⁻¹ u⁻¹ δ u` of the unipotent radical of a two-block shape. -/
def twistMulEquiv (hB : B.length = 2) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    B.unipotentSubgroup F ≃* B.unipotentSubgroup F :=
  MulEquiv.ofBijective (twistHom hB m) ⟨twistHom_injective hB m hm, twistHom_surjective hB m hm⟩

@[simp] theorem twistMulEquiv_apply (hB : B.length = 2) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly)
    (u : B.unipotentSubgroup F) : twistMulEquiv hB m hm u = twistHom hB m u := rfl

variable [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]

omit [T2Space F] in
/-- The homomorphism `u ↦ δ⁻¹ u⁻¹ δ u` is continuous. -/
theorem continuous_twistHom (hB : B.length = 2) (m : B.Levi F) :
    Continuous (twistHom hB m) := by
  refine Continuous.subtype_mk ?_ _
  exact (((continuous_const.mul continuous_subtype_val.inv).mul continuous_const).mul
    continuous_subtype_val)

/-- Over a Hausdorff topological field whose general linear group is locally compact and
σ-compact, `u ↦ δ⁻¹ u⁻¹ δ u` is a topological group automorphism of the unipotent radical of a
two-block shape (open mapping theorem). -/
def twistContinuousMulEquiv [LocallyCompactSpace (Langlands.GeneralLinear n F)]
    [SigmaCompactSpace (Langlands.GeneralLinear n F)]
    (hB : B.length = 2) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly) :
    B.unipotentSubgroup F ≃ₜ* B.unipotentSubgroup F :=
  haveI : LocallyCompactSpace (B.unipotentSubgroup F) :=
    (B.isClosed_unipotentSubgroup F).locallyCompactSpace
  haveI : SigmaCompactSpace (B.unipotentSubgroup F) :=
    (B.isClosed_unipotentSubgroup F).sigmaCompactSpace
  have hopen : IsOpenMap (twistHom hB m) :=
    MonoidHom.isOpenMap_of_sigmaCompact (twistHom hB m) (twistHom_surjective hB m hm)
      (continuous_twistHom hB m)
  { twistMulEquiv hB m hm with
    continuous_toFun := continuous_twistHom hB m
    continuous_invFun := by
      have h := ((twistMulEquiv hB m hm).toEquiv.toHomeomorphOfContinuousOpen
        (continuous_twistHom hB m) hopen).continuous_symm
      exact h }

@[simp] theorem twistContinuousMulEquiv_apply [LocallyCompactSpace (Langlands.GeneralLinear n F)]
    [SigmaCompactSpace (Langlands.GeneralLinear n F)]
    (hB : B.length = 2) (m : B.Levi F)
    (hm : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly)
    (u : B.unipotentSubgroup F) : twistContinuousMulEquiv hB m hm u = twistHom hB m u := rfl

end Field

end Langlands.GeneralLinear.BlockShape
