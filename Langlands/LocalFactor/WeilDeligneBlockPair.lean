import Langlands.LocalFactor.WeilDeligneEulerSum
import Langlands.WeilDeligne.SpecialBlocks
import Langlands.Weil.Representation.Invariants
import Langlands.Weil.Representation.Twist
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Pair L-factors of two uncentered special blocks

For blocks `B ⊗ S_(a+1)` and `B' ⊗ S_(b+1)` with raising monodromy, the
inertia-fixed monodromy kernel of their tensor product is a direct sum of
`min (a+1) (b+1)` copies of the inertia invariants of `B ⊗ B'`, the copy of
index `j` lying in total weight `a + b - j`. Hence the pair L-factor is the
product of the pair L-factors of `ν^(a+b-j) B` and `B'` with zero monodromy.
The computation is explicit and characteristic free.
-/

noncomputable section

universe uK uG uV uW

open scoped TensorProduct
open Polynomial

namespace Langlands.LocalFactor

section ExtendZero

variable {U : Type uV} [Zero U]

/-- Extension by zero of a finite family to all natural indices. -/
def extendZero {k : ℕ} (y : Fin k → U) (j : ℕ) : U := if h : j < k then y ⟨j, h⟩ else 0

theorem extendZero_of_lt {k : ℕ} (y : Fin k → U) {j : ℕ} (h : j < k) :
    extendZero y j = y ⟨j, h⟩ := dite_eq_left h

theorem extendZero_of_le {k : ℕ} (y : Fin k → U) {j : ℕ} (h : k ≤ j) :
    extendZero y j = 0 := dite_eq_right (by omega)

end ExtendZero

section Grid

variable {K : Type uK} [Field K] {U : Type uV} [AddCommGroup U] [Module K U] (a b : ℕ)

/-- Raising in both indices of `Fin (b+1) → Fin (a+1) → U`: the coordinate
monodromy of a tensor of two special blocks. -/
def gridMonodromy : Module.End K (Fin (b + 1) → Fin (a + 1) → U) where
  toFun x l i := (if h : 0 < i.val then x l ⟨i.val - 1, by omega⟩ else 0) +
    (if h : 0 < l.val then x ⟨l.val - 1, by omega⟩ i else 0)
  map_add' x y := by
    funext l i
    simp only [Pi.add_apply]
    split_ifs <;> abel
  map_smul' c x := by
    funext l i
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [smul_add]

theorem gridMonodromy_apply (x : Fin (b + 1) → Fin (a + 1) → U) (l : Fin (b + 1))
    (i : Fin (a + 1)) :
    gridMonodromy (K := K) a b x l i =
      (if h : 0 < i.val then x l ⟨i.val - 1, by omega⟩ else 0) +
        (if h : 0 < l.val then x ⟨l.val - 1, by omega⟩ i else 0) := rfl

/-- The coordinate action of a group element with weight `c` and action `f`. -/
def gridScale (c : K) (f : Module.End K U) : Module.End K (Fin (b + 1) → Fin (a + 1) → U) where
  toFun x l i := c ^ (i.val + l.val) • f (x l i)
  map_add' x y := by
    funext l i
    simp [smul_add]
  map_smul' d x := by
    funext l i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    exact smul_comm _ _ _

theorem gridScale_apply (c : K) (f : Module.End K U) (x : Fin (b + 1) → Fin (a + 1) → U)
    (l : Fin (b + 1)) (i : Fin (a + 1)) :
    gridScale a b c f x l i = c ^ (i.val + l.val) • f (x l i) := rfl

/-- The alternating antidiagonal vectors: the component of index `j` sits on the
antidiagonal of total degree `a + b - j` with sign `(-1)^i`. -/
def gridEmbedding :
    (Fin (min (a + 1) (b + 1)) → U) →ₗ[K] (Fin (b + 1) → Fin (a + 1) → U) where
  toFun y l i := (-1 : K) ^ i.val • extendZero y (a + b - (i.val + l.val))
  map_add' y y' := by
    funext l i
    simp only [extendZero, Pi.add_apply]
    split_ifs <;> simp [smul_add]
  map_smul' c y := by
    funext l i
    simp only [extendZero, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [smul_comm c]

theorem gridEmbedding_apply (y : Fin (min (a + 1) (b + 1)) → U) (l : Fin (b + 1))
    (i : Fin (a + 1)) :
    gridEmbedding (K := K) a b y l i =
      (-1 : K) ^ i.val • extendZero y (a + b - (i.val + l.val)) := rfl

/-- The antidiagonal vectors are killed by the coordinate monodromy. -/
theorem gridMonodromy_gridEmbedding (y : Fin (min (a + 1) (b + 1)) → U) :
    gridMonodromy (K := K) a b (gridEmbedding (K := K) a b y) = 0 := by
  funext l i
  rw [gridMonodromy_apply]
  simp only [gridEmbedding_apply, Pi.zero_apply]
  have hi' := i.isLt
  have hl' := l.isLt
  by_cases hi : 0 < i.val <;> by_cases hl : 0 < l.val
  · rw [dite_eq_left hi, dite_eq_left hl]
    have e : a + b - (i.val - 1 + l.val) = a + b - (i.val + (l.val - 1)) := by omega
    have hs : (-1 : K) ^ i.val = -(-1 : K) ^ (i.val - 1) := by
      conv_lhs => rw [show i.val = i.val - 1 + 1 by omega]
      rw [pow_succ]
      ring
    simp only [e, hs, neg_smul, add_neg_cancel]
  · rw [dite_eq_left hi, dite_eq_right hl, extendZero_of_le]
    · simp
    · omega
  · rw [dite_eq_right hi, dite_eq_left hl, extendZero_of_le]
    · simp
    · omega
  · rw [dite_eq_right hi, dite_eq_right hl, add_zero]

/-- The component of index `j` is read off at the top weight of the first block. -/
theorem gridEmbedding_last (y : Fin (min (a + 1) (b + 1)) → U) (j : Fin (min (a + 1) (b + 1))) :
    gridEmbedding (K := K) a b y ⟨b - j.val, by omega⟩ (Fin.last a) =
      (-1 : K) ^ a • y j := by
  have hj := j.isLt
  rw [gridEmbedding_apply, Fin.val_last]
  have e : a + b - (a + (b - j.val)) = j.val := by omega
  simp only [e, extendZero_of_lt y j.isLt]

theorem gridEmbedding_injective : Function.Injective (gridEmbedding (K := K) (U := U) a b) := by
  intro y y' h
  funext j
  have hj := gridEmbedding_last (K := K) a b y j
  rw [h, gridEmbedding_last] at hj
  exact smul_right_injective U (pow_ne_zero a (neg_ne_zero.mpr one_ne_zero)) hj.symm

/-- The coordinate action on antidiagonal vectors: the component of index `j`
acquires the weight `c^(a+b-j)`. -/
theorem gridScale_gridEmbedding (c : K) (f : Module.End K U)
    (y : Fin (min (a + 1) (b + 1)) → U) :
    gridScale a b c f (gridEmbedding (K := K) a b y) =
      gridEmbedding (K := K) a b (fun j => c ^ (a + b - j.val) • f (y j)) := by
  funext l i
  have hi' := i.isLt
  have hl' := l.isLt
  rw [gridScale_apply, gridEmbedding_apply, gridEmbedding_apply]
  by_cases h : a + b - (i.val + l.val) < min (a + 1) (b + 1)
  · rw [extendZero_of_lt y h, extendZero_of_lt _ h, map_smul, smul_comm]
    have e : a + b - (a + b - (i.val + l.val)) = i.val + l.val := by omega
    simp only [e]
  · rw [extendZero_of_le y (by omega), extendZero_of_le _ (by omega)]
    simp

section Chain

variable {a b} {x : Fin (b + 1) → Fin (a + 1) → U}

/-- The interior relation of the coordinate monodromy kernel. -/
theorem grid_step (H : gridMonodromy (K := K) a b x = 0) (l l' : Fin (b + 1))
    (i i' : Fin (a + 1)) (hl : l.val = l'.val + 1) (hi : i'.val = i.val + 1) :
    x l i = -x l' i' := by
  have h := congrFun (congrFun H l) i'
  rw [gridMonodromy_apply, dite_eq_left (by omega), dite_eq_left (by omega)] at h
  have e1 : (⟨i'.val - 1, by omega⟩ : Fin (a + 1)) = i := Fin.ext (by simp; omega)
  have e2 : (⟨l.val - 1, by omega⟩ : Fin (b + 1)) = l' := Fin.ext (by simp; omega)
  rw [e1, e2] at h
  exact eq_neg_of_add_eq_zero_left h

theorem grid_bottom_left (H : gridMonodromy (K := K) a b x = 0) (l : Fin (b + 1))
    (hl : l.val < b) : x l 0 = 0 := by
  have h := congrFun (congrFun H ⟨l.val + 1, by omega⟩) 0
  rw [gridMonodromy_apply, dite_eq_right (by simp), dite_eq_left (by simp)] at h
  simpa using h

theorem grid_bottom_right (H : gridMonodromy (K := K) a b x = 0) (i : Fin (a + 1))
    (hi : i.val < a) : x 0 i = 0 := by
  have h := congrFun (congrFun H 0) ⟨i.val + 1, by omega⟩
  rw [gridMonodromy_apply, dite_eq_left (by simp), dite_eq_right (by simp)] at h
  simpa using h

/-- Along an antidiagonal, a kernel vector is determined by its value at the top
weight of the first block. -/
theorem grid_chain (H : gridMonodromy (K := K) a b x = 0) :
    ∀ (t : ℕ) (l : Fin (b + 1)) (i : Fin (a + 1)) (hi : i.val + t = a) (hl : t ≤ l.val),
      x l i = (-1 : K) ^ t • x ⟨l.val - t, by omega⟩ (Fin.last a) := by
  intro t
  induction t with
  | zero =>
    intro l i hi hl
    have e : i = Fin.last a := Fin.ext (by simp; omega)
    subst e
    simp
  | succ t ih =>
    intro l i hi hl
    rw [grid_step H l ⟨l.val - 1, by omega⟩ i ⟨i.val + 1, by omega⟩ (by simp; omega) rfl,
      ih ⟨l.val - 1, by omega⟩ ⟨i.val + 1, by omega⟩ (by simp; omega) (by simp; omega)]
    have e : (⟨(⟨l.val - 1, by omega⟩ : Fin (b + 1)).val - t, by simp; omega⟩ : Fin (b + 1)) =
        ⟨l.val - (t + 1), by omega⟩ := Fin.ext (by simp; omega)
    rw [e, pow_succ, mul_comm, ← smul_smul, neg_one_smul]

/-- Kernel vectors vanish on antidiagonals of total degree below `a`. -/
theorem grid_zero_left (H : gridMonodromy (K := K) a b x = 0) :
    ∀ (n : ℕ) (l : Fin (b + 1)) (i : Fin (a + 1)), l.val = n → i.val + n < a → x l i = 0 := by
  intro n
  induction n with
  | zero =>
    intro l i hl hi
    have e : l = 0 := Fin.ext hl
    subst e
    exact grid_bottom_right H i (by omega)
  | succ n ih =>
    intro l i hl hi
    rw [grid_step H l ⟨l.val - 1, by omega⟩ i ⟨i.val + 1, by omega⟩ (by simp; omega) rfl,
      ih _ _ (by simp; omega) (by simp; omega), neg_zero]

/-- Kernel vectors vanish on antidiagonals of total degree below `b`. -/
theorem grid_zero_right (H : gridMonodromy (K := K) a b x = 0) :
    ∀ (n : ℕ) (l : Fin (b + 1)) (i : Fin (a + 1)), i.val = n → n + l.val < b → x l i = 0 := by
  intro n
  induction n with
  | zero =>
    intro l i hi hl
    have e : i = 0 := Fin.ext hi
    subst e
    exact grid_bottom_left H l (by omega)
  | succ n ih =>
    intro l i hi hl
    have h := grid_step H ⟨l.val + 1, by omega⟩ l ⟨i.val - 1, by omega⟩ i rfl (by simp; omega)
    rw [ih _ _ (by simp; omega) (by simp; omega)] at h
    exact (neg_eq_zero.mp h.symm)

/-- Every vector killed by the coordinate monodromy is a sum of alternating
antidiagonal vectors. -/
theorem eq_gridEmbedding (H : gridMonodromy (K := K) a b x = 0) :
    x = gridEmbedding (K := K) a b
      (fun j => (-1 : K) ^ a • x ⟨b - j.val, by omega⟩ (Fin.last a)) := by
  funext l i
  have hi' := i.isLt
  have hl' := l.isLt
  rw [gridEmbedding_apply]
  by_cases h : a + b - (i.val + l.val) < min (a + 1) (b + 1)
  · rw [extendZero_of_lt _ h, grid_chain H (a - i.val) l i (by omega) (by omega), smul_smul]
    have key : ∀ m n : ℕ, m ≤ n → (-1 : K) ^ m * (-1 : K) ^ n = (-1 : K) ^ (n - m) := by
      intro m n hmn
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [← pow_add, show m + (m + d) = 2 * m + d by ring, pow_add, pow_mul, neg_one_sq,
        one_pow, one_mul, Nat.add_sub_cancel_left]
    have hs : (-1 : K) ^ i.val * (-1 : K) ^ a = (-1 : K) ^ (a - i.val) := key _ _ (by omega)
    have e : (⟨b - (a + b - (i.val + l.val)), by omega⟩ : Fin (b + 1)) =
        ⟨l.val - (a - i.val), by omega⟩ := Fin.ext (by simp; omega)
    simp only [hs, e]
  · rw [extendZero_of_le _ (by omega), smul_zero]
    by_cases ha : i.val + l.val < a
    · exact grid_zero_left H l.val l i rfl ha
    · exact grid_zero_right H i.val l i rfl (by omega)

end Chain

end Grid

namespace WeilDeligne

section Block

variable {K : Type uK} {G : Type uG} [Field K] [Group G] (ν : G →* Kˣ)
  (B : FiniteRepresentation.{uK, uG, uV} K G) (B' : FiniteRepresentation.{uK, uG, uW} K G)
  (a b : ℕ)

/-- Grid coordinates on the tensor product of two blocks: the coordinate of
index `(l, i)` pairs weight `i` of the first block with weight `l` of the second. -/
def blockPairCoord :
    ((B ⊗[K] (Fin (a + 1) → K)) ⊗[K] (B' ⊗[K] (Fin (b + 1) → K))) ≃ₗ[K]
      (Fin (b + 1) → Fin (a + 1) → B ⊗[K] B') :=
  TensorProduct.tensorTensorTensorComm K B (Fin (a + 1) → K) B' (Fin (b + 1) → K) ≪≫ₗ
    (TensorProduct.assoc K (B ⊗[K] B') (Fin (a + 1) → K) (Fin (b + 1) → K)).symm ≪≫ₗ
    TensorProduct.piScalarRight K K ((B ⊗[K] B') ⊗[K] (Fin (a + 1) → K)) (Fin (b + 1)) ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => TensorProduct.piScalarRight K K (B ⊗[K] B') (Fin (a + 1))

theorem blockPairCoord_tmul (u : B) (f : Fin (a + 1) → K) (u' : B') (f' : Fin (b + 1) → K) :
    blockPairCoord B B' a b ((u ⊗ₜ[K] f) ⊗ₜ[K] (u' ⊗ₜ[K] f')) =
      fun l i => (f i * f' l) • (u ⊗ₜ[K] u') := by
  funext l i
  simp only [blockPairCoord, LinearEquiv.trans_apply, TensorProduct.tensorTensorTensorComm_tmul,
    TensorProduct.assoc_symm_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, LinearEquiv.piCongrRight_apply, map_smul, Pi.smul_apply,
    smul_smul]
  rw [mul_comm]

/-- The monodromy of the tensor of two blocks on a pure tensor, in grid coordinates. -/
theorem blockPairCoord_monodromy_tmul (u : B) (f : Fin (a + 1) → K) (u' : B')
    (f' : Fin (b + 1) → K) :
    blockPairCoord B B' a b
        ((WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
          (WeilDeligneRepresentation.block ν B' (b + 1))).monodromy
          ((u ⊗ₜ[K] f) ⊗ₜ[K] (u' ⊗ₜ[K] f'))) =
      fun l i => (WeilDeligneRepresentation.Special.raising K (a + 1) f i * f' l +
        f i * WeilDeligneRepresentation.Special.raising K (b + 1) f' l) • (u ⊗ₜ[K] u') := by
  change blockPairCoord B B' a b
      (((0 : B) ⊗ₜ[K] f + u ⊗ₜ[K] WeilDeligneRepresentation.Special.raising K (a + 1) f) ⊗ₜ[K]
          (u' ⊗ₜ[K] f') +
        (u ⊗ₜ[K] f) ⊗ₜ[K]
          ((0 : B') ⊗ₜ[K] f' + u' ⊗ₜ[K] WeilDeligneRepresentation.Special.raising K (b + 1) f')) = _
  rw [TensorProduct.zero_tmul, TensorProduct.zero_tmul, zero_add, zero_add, map_add,
    blockPairCoord_tmul, blockPairCoord_tmul]
  funext l i
  rw [Pi.add_apply, Pi.add_apply, add_smul]

/-- The action of a group element on a pure tensor of two blocks, in grid coordinates. -/
theorem blockPairCoord_representation_tmul (g : G) (u : B) (f : Fin (a + 1) → K) (u' : B')
    (f' : Fin (b + 1) → K) :
    blockPairCoord B B' a b
        ((WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
          (WeilDeligneRepresentation.block ν B' (b + 1))).representation g
          ((u ⊗ₜ[K] f) ⊗ₜ[K] (u' ⊗ₜ[K] f'))) =
      fun l i => (WeilDeligneRepresentation.Special.action ν (a + 1) g f i *
        WeilDeligneRepresentation.Special.action ν (b + 1) g f' l) •
          (B.representation g u ⊗ₜ[K] B'.representation g u') := by
  change blockPairCoord B B' a b
      ((B.representation g u ⊗ₜ[K] WeilDeligneRepresentation.Special.action ν (a + 1) g f) ⊗ₜ[K]
        (B'.representation g u' ⊗ₜ[K] WeilDeligneRepresentation.Special.action ν (b + 1) g f')) = _
  rw [blockPairCoord_tmul]

/-- In grid coordinates the monodromy raises both weights. -/
theorem blockPairCoord_monodromy
    (x : WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
      (WeilDeligneRepresentation.block ν B' (b + 1))) :
    blockPairCoord B B' a b
        ((WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
          (WeilDeligneRepresentation.block ν B' (b + 1))).monodromy x) =
      gridMonodromy (K := K) a b (blockPairCoord B B' a b x) := by
  have h : (blockPairCoord B B' a b).toLinearMap ∘ₗ
      (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
        (WeilDeligneRepresentation.block ν B' (b + 1))).monodromy =
      gridMonodromy (K := K) a b ∘ₗ (blockPairCoord B B' a b).toLinearMap := by
    apply TensorProduct.ext_fourfold'
    intro (u : B) (f : Fin (a + 1) → K) (u' : B') (f' : Fin (b + 1) → K)
    change blockPairCoord B B' a b
        ((WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
          (WeilDeligneRepresentation.block ν B' (b + 1))).monodromy
          ((u ⊗ₜ[K] f) ⊗ₜ[K] (u' ⊗ₜ[K] f'))) =
      gridMonodromy (K := K) a b (blockPairCoord B B' a b ((u ⊗ₜ[K] f) ⊗ₜ[K] (u' ⊗ₜ[K] f')))
    rw [blockPairCoord_monodromy_tmul, blockPairCoord_tmul]
    funext l i
    rw [gridMonodromy_apply, WeilDeligneRepresentation.Special.raising_apply,
      WeilDeligneRepresentation.Special.raising_apply]
    by_cases hi : 0 < i.val <;> by_cases hl : 0 < l.val <;> simp [hi, hl, add_smul]
  exact LinearMap.congr_fun h x

/-- In grid coordinates a group element acts through `B ⊗ B'` with the weight
`ν(g)^(i+l)` at index `(l, i)`. -/
theorem blockPairCoord_representation (g : G)
    (x : WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
      (WeilDeligneRepresentation.block ν B' (b + 1))) :
    blockPairCoord B B' a b
        ((WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
          (WeilDeligneRepresentation.block ν B' (b + 1))).representation g x) =
      gridScale a b (ν g : K) (TensorProduct.map (B.representation g) (B'.representation g))
        (blockPairCoord B B' a b x) := by
  have h : (blockPairCoord B B' a b).toLinearMap ∘ₗ
      (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
        (WeilDeligneRepresentation.block ν B' (b + 1))).representation g =
      gridScale a b (ν g : K) (TensorProduct.map (B.representation g) (B'.representation g)) ∘ₗ
        (blockPairCoord B B' a b).toLinearMap := by
    apply TensorProduct.ext_fourfold'
    intro (u : B) (f : Fin (a + 1) → K) (u' : B') (f' : Fin (b + 1) → K)
    change blockPairCoord B B' a b
        ((WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
          (WeilDeligneRepresentation.block ν B' (b + 1))).representation g
          ((u ⊗ₜ[K] f) ⊗ₜ[K] (u' ⊗ₜ[K] f'))) =
      gridScale a b (ν g : K) (TensorProduct.map (B.representation g) (B'.representation g))
        (blockPairCoord B B' a b ((u ⊗ₜ[K] f) ⊗ₜ[K] (u' ⊗ₜ[K] f')))
    rw [blockPairCoord_representation_tmul, blockPairCoord_tmul]
    funext l i
    rw [gridScale_apply, map_smul, TensorProduct.map_tmul, smul_smul,
      WeilDeligneRepresentation.Special.action_apply,
      WeilDeligneRepresentation.Special.action_apply]
    congr 1
    ring
  exact LinearMap.congr_fun h x

variable (I : Subgroup G) [I.Normal]

/-- The operator on `min (a+1) (b+1)` copies of the inertia invariants of
`B ⊗ B'` whose copy of index `j` carries the weight `ν(g)^(a+b-j)`. -/
def blockPairKernelOperator (g : G) :
    Module.End K (Fin (min (a + 1) (b + 1)) →
      ↥(Representation.invariants ((B.representation.tprod B'.representation).comp I.subtype))) :=
  LinearMap.pi fun j => ((ν g : K) ^ (a + b - j.val) •
    (B.representation.tprod B'.representation).toInvariants I g) ∘ₗ LinearMap.proj j

/-- The alternating antidiagonal vectors with inertia-invariant entries, as vectors
of the tensor product of two blocks. -/
def blockPairKernelEmbedding :
    (Fin (min (a + 1) (b + 1)) →
      ↥(Representation.invariants ((B.representation.tprod B'.representation).comp I.subtype)))
      →ₗ[K] WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
        (WeilDeligneRepresentation.block ν B' (b + 1)) :=
  (blockPairCoord B B' a b).symm.toLinearMap ∘ₗ gridEmbedding a b ∘ₗ
    LinearMap.compLeft
      (Representation.invariants ((B.representation.tprod B'.representation).comp I.subtype)).subtype
      (Fin (min (a + 1) (b + 1)))

omit [I.Normal] in
theorem blockPairCoord_kernelEmbedding
    (w : Fin (min (a + 1) (b + 1)) →
      ↥(Representation.invariants ((B.representation.tprod B'.representation).comp I.subtype))) :
    blockPairCoord B B' a b (blockPairKernelEmbedding ν B B' a b I w) =
      gridEmbedding (K := K) a b (fun j => (w j : B ⊗[K] B')) :=
  LinearEquiv.apply_symm_apply _ _

/-- The inertia-fixed monodromy kernel of the tensor of two blocks is identified
with `min (a+1) (b+1)` copies of the inertia invariants of `B ⊗ B'`, the copy of
index `j` lying in total weight `a + b - j`. -/
theorem eulerPolynomial_block_block (hν : ∀ i : I, ν i = 1) (g : G) :
    eulerPolynomial (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
        (WeilDeligneRepresentation.block ν B' (b + 1))) I g =
      LocalFactor.eulerPolynomial (blockPairKernelOperator ν B B' a b I g) := by
  have hνK : ∀ i : I, (ν i : K) = 1 := fun i => by rw [hν i, Units.val_one]
  apply eulerPolynomial_eq_of_embedding g _ (blockPairKernelEmbedding ν B B' a b I)
  · intro w w' h
    have h' := congrArg (blockPairCoord B B' a b) h
    rw [blockPairCoord_kernelEmbedding, blockPairCoord_kernelEmbedding] at h'
    funext j
    exact Subtype.ext (congrFun (gridEmbedding_injective a b h') j)
  · intro w
    constructor
    · apply (blockPairCoord B B' a b).injective
      rw [blockPairCoord_monodromy, blockPairCoord_kernelEmbedding, gridMonodromy_gridEmbedding]
      exact (map_zero (blockPairCoord B B' a b)).symm
    · intro i
      apply (blockPairCoord B B' a b).injective
      rw [blockPairCoord_representation, blockPairCoord_kernelEmbedding, gridScale_gridEmbedding,
        hνK i]
      congr 1
      funext j
      rw [one_pow, one_smul]
      exact (w j).property i
  · intro v hN hI
    have hx : gridMonodromy (K := K) a b (blockPairCoord B B' a b v) = 0 := by
      rw [← blockPairCoord_monodromy, hN]
      exact map_zero (blockPairCoord B B' a b)
    have hfix : ∀ (i : I) (l : Fin (b + 1)) (i' : Fin (a + 1)),
        TensorProduct.map (B.representation i) (B'.representation i)
          (blockPairCoord B B' a b v l i') = blockPairCoord B B' a b v l i' := by
      intro i l i'
      have h := congrFun (congrFun (congrArg (blockPairCoord B B' a b) (hI i)) l) i'
      rw [blockPairCoord_representation, gridScale_apply, hνK i, one_pow, one_smul] at h
      exact h
    refine ⟨fun j => ⟨(-1 : K) ^ a • blockPairCoord B B' a b v ⟨b - j.val, by omega⟩
      (Fin.last a), (Representation.mem_invariants _ _).mpr fun i => ?_⟩, ?_⟩
    · change TensorProduct.map (B.representation i) (B'.representation i) _ = _
      rw [map_smul, hfix]
    · apply (blockPairCoord B B' a b).injective
      rw [blockPairCoord_kernelEmbedding]
      exact (eq_gridEmbedding hx).symm
  · intro w
    apply (blockPairCoord B B' a b).injective
    rw [blockPairCoord_representation, blockPairCoord_kernelEmbedding,
      blockPairCoord_kernelEmbedding, gridScale_gridEmbedding]
    rfl

/-- The rational version of `eulerPolynomial_block_block`. -/
theorem rationalLFactor_block_block (hν : ∀ i : I, ν i = 1) (g : G) :
    rationalLFactor (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.block ν B (a + 1))
        (WeilDeligneRepresentation.block ν B' (b + 1))) I g =
      LocalFactor.rationalFactor (blockPairKernelOperator ν B B' a b I g) := by
  change (algebraMap K[X] (RatFunc K) (eulerPolynomial _ I g))⁻¹ = _
  rw [eulerPolynomial_block_block ν B B' a b I hν g]
  rfl

/-- The tensor of a twisted representation with zero monodromy acts by the twisted
tensor action. -/
theorem tensor_zeroMonodromy_twist_representation (χ : G →* Kˣ) (g : G) :
    (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist χ B))
        (WeilDeligneRepresentation.zeroMonodromy ν B')).representation g =
      (χ g : K) • TensorProduct.map (B.representation g) (B'.representation g) := by
  change TensorProduct.map ((χ g : K) • B.representation g) (B'.representation g) = _
  rw [TensorProduct.map_smul_left]

/-- For a character trivial on `I`, the pair factor of the twist of `B` by `χ` and
`B'` with zero monodromy is the factor of `χ(g)` times the action of `g` on the
inertia invariants of `B ⊗ B'`. -/
theorem pairLFactor_zeroMonodromy_twist (χ : G →* Kˣ) (hχ : ∀ i : I, χ i = 1) (g : G) :
    pairLFactor (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist χ B))
        (WeilDeligneRepresentation.zeroMonodromy ν B') I g =
      LocalFactor.rationalFactor
        ((χ g : K) • (B.representation.tprod B'.representation).toInvariants I g) := by
  have hχK : ∀ i : I, (χ i : K) = 1 := fun i => by rw [hχ i, Units.val_one]
  have hN : (WeilDeligneRepresentation.tensor
      (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist χ B))
      (WeilDeligneRepresentation.zeroMonodromy ν B')).monodromy = 0 := by
    apply LinearMap.ext
    intro v
    change (TensorProduct.map (0 : Module.End K B) (1 : Module.End K B') +
      TensorProduct.map (1 : Module.End K B) (0 : Module.End K B') :
      Module.End K (B ⊗[K] B')) v = 0
    simp only [TensorProduct.map_zero_left, TensorProduct.map_zero_right, add_zero]
    rfl
  apply rationalLFactor_eq_of_embedding g _
    (Representation.invariants ((B.representation.tprod B'.representation).comp I.subtype)).subtype
    (Submodule.injective_subtype _)
  · intro w
    refine ⟨by rw [hN, LinearMap.zero_apply], fun i => ?_⟩
    rw [tensor_zeroMonodromy_twist_representation, hχK i, one_smul]
    exact w.property i
  · intro v _ hI
    refine ⟨⟨v, (Representation.mem_invariants _ _).mpr fun i => ?_⟩, rfl⟩
    have h := hI i
    rw [tensor_zeroMonodromy_twist_representation, hχK i, one_smul] at h
    exact h
  · intro w
    rw [tensor_zeroMonodromy_twist_representation]
    rfl

/-- **Pair L-factors of two uncentered blocks** (Henniart 2002, §2.4): if `ν` is
trivial on `I`, the pair factor of `B ⊗ S_(a+1)` and `B' ⊗ S_(b+1)` is the product
over `j < min (a+1) (b+1)` of the pair factors of `ν^(a+b-j) B` and `B'` with zero
monodromy. -/
theorem pairLFactor_block_block (hν : ∀ i : I, ν i = 1) (g : G) :
    pairLFactor (WeilDeligneRepresentation.block ν B (a + 1))
        (WeilDeligneRepresentation.block ν B' (b + 1)) I g =
      ∏ j : Fin (min (a + 1) (b + 1)),
        pairLFactor
          (WeilDeligneRepresentation.zeroMonodromy ν
            (FiniteRepresentation.twist (ν ^ (a + b - j.val)) B))
          (WeilDeligneRepresentation.zeroMonodromy ν B') I g := by
  rw [pairLFactor, rationalLFactor_block_block ν B B' a b I hν g, blockPairKernelOperator,
    rationalFactor_pi]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [pairLFactor_zeroMonodromy_twist ν B B' I _
    (fun i => by rw [MonoidHom.pow_apply, hν i, one_pow]) g, MonoidHom.pow_apply,
    Units.val_pow_eq_pow_val]

end Block

end WeilDeligne

end Langlands.LocalFactor
