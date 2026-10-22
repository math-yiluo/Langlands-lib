import Langlands.Group.GL.BlockModulus
import Langlands.Group.GL.UpperUnipotent

/-!
# The singleton block shape and the upper unipotent group

With `n` blocks of size one, the standard block parabolic is the upper triangular
group and its unipotent radical is the actual upper unipotent group, with the same
matrices. Levi elements are diagonal matrices, and the block modulus is the
product of the root quotients `|t_i| / |t_j|` over `i < j`.
-/

open scoped BigOperators NNReal

namespace Langlands.GeneralLinear

universe u

namespace BlockShape

/-- The shape with `n` blocks, each of size one. It is reducible, so that `Fin` instances
and lemmas stated for `Fin n` and `Fin 1` apply to its block and coordinate types. -/
abbrev singletons (n : ℕ) : BlockShape n where
  length := n
  size _ := 1
  positive _ := Nat.one_pos
  sum_eq := by simp

variable {n : ℕ}

theorem singletons_length : (singletons n).length = n := rfl

theorem singletons_size (i : Fin (singletons n).length) :
    (singletons n).size i = 1 := rfl

instance singletons_size_neZero (i : Fin (singletons n).length) :
    NeZero ((singletons n).size i) :=
  ⟨one_ne_zero⟩

/-- Each block of the singleton shape has exactly one coordinate. -/
instance (i : Fin (singletons n).length) : Unique (Fin ((singletons n).size i)) :=
  inferInstanceAs (Unique (Fin 1))

/-- The consecutive-block numbering of the singleton shape is the identity. -/
@[simp] theorem singletons_indexEquiv_apply (i : Fin n) (j : Fin 1) :
    (singletons n).indexEquiv ⟨i, j⟩ = i := by
  apply Fin.ext
  rw [indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  simp [singletons_size]

/-- The only coordinate of block `i` is the standard coordinate `i`. -/
@[simp] theorem singletons_index (i : Fin n) (j : Fin 1) :
    (singletons n).index i j = i :=
  singletons_indexEquiv_apply i j

variable (R : Type u) [CommRing R]

/-- The singleton parabolic is the upper triangular group. -/
theorem singletons_mem_parabolic_iff (g : Langlands.GeneralLinear n R) :
    g ∈ (singletons n).parabolic R ↔ g.val.IsUpperTriangular := by
  rw [mem_parabolic_iff]
  constructor
  · intro h i j hij
    have hg := h i j 0 0 hij
    rwa [singletons_index, singletons_index] at hg
  · intro h i j a b hij
    rw [singletons_index, singletons_index]
    exact h hij

/-- The singleton radical, as a matrix subgroup, is the upper unipotent group. -/
theorem singletons_unipotentSubgroup :
    (singletons n).unipotentSubgroup R = upperUnipotent n R := by
  ext g
  rw [mem_unipotentSubgroup_iff, singletons_mem_parabolic_iff]
  change _ ↔ g.val.IsUpperTriangular ∧ ∀ i, g i i = 1
  constructor
  · rintro ⟨h, hd⟩
    refine ⟨h, fun i => ?_⟩
    have hg := hd i 0 0
    rwa [singletons_index, ite_eq_left rfl] at hg
  · rintro ⟨h, hd⟩
    refine ⟨h, fun i a b => ?_⟩
    obtain rfl : a = b := Subsingleton.elim a b
    rw [singletons_index, ite_eq_left rfl]
    exact hd i

/-- A singleton parabolic element lies in the radical exactly when it is upper
unipotent. -/
theorem singletons_mem_unipotentRadical_iff (g : (singletons n).parabolic R) :
    g ∈ (singletons n).unipotentRadical R ↔ g.val ∈ upperUnipotent n R := by
  rw [← singletons_unipotentSubgroup, unipotentSubgroup]
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).symm

/-- The upper unipotent group is the singleton radical; matrices are unchanged. -/
def upperUnipotentEquivRadical :
    upperUnipotent n R ≃* (singletons n).unipotentRadical R where
  toFun u := ⟨⟨u.val, (singletons_mem_parabolic_iff R u.val).mpr u.property.1⟩,
    (singletons_mem_unipotentRadical_iff R _).mpr u.property⟩
  invFun v := ⟨v.val.val, (singletons_mem_unipotentRadical_iff R v.val).mp v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem upperUnipotentEquivRadical_apply_val (u : upperUnipotent n R) :
    (((upperUnipotentEquivRadical R u : (singletons n).unipotentRadical R) :
      (singletons n).parabolic R) : Langlands.GeneralLinear n R) = u := rfl

@[simp] theorem upperUnipotentEquivRadical_symm_apply_val
    (v : (singletons n).unipotentRadical R) :
    (((upperUnipotentEquivRadical R).symm v : upperUnipotent n R) :
      Langlands.GeneralLinear n R) = ((v : (singletons n).parabolic R) :
        Langlands.GeneralLinear n R) := rfl

section Topology

variable [TopologicalSpace R]

/-- The same identification is a homeomorphism for the existing subgroup topologies. -/
def upperUnipotentContinuousEquivRadical :
    upperUnipotent n R ≃ₜ* (singletons n).unipotentRadical R where
  toMulEquiv := upperUnipotentEquivRadical R
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

@[simp] theorem upperUnipotentContinuousEquivRadical_toMulEquiv :
    (upperUnipotentContinuousEquivRadical R).toMulEquiv =
      upperUnipotentEquivRadical (n := n) R := rfl

@[simp] theorem upperUnipotentContinuousEquivRadical_apply (u : upperUnipotent n R) :
    upperUnipotentContinuousEquivRadical R u = upperUnipotentEquivRadical R u := rfl

end Topology

/-- Diagonal invertible matrices as Levi elements of the singleton shape: the
family of `1 × 1` scalar matrices of the given units. -/
def singletonLevi : (Fin n → Rˣ) →* (singletons n).Levi R where
  toFun t i := GeneralLinear.scalar (t i)
  map_one' := by
    funext i
    exact map_one _
  map_mul' t t' := by
    funext i
    exact map_mul _ _ _

@[simp] theorem singletonLevi_apply (t : Fin n → Rˣ) (i : Fin n) :
    singletonLevi R t i = GeneralLinear.scalar (t i) := rfl

/-- The block diagonal matrix of `singletonLevi t` is the diagonal matrix of `t`. -/
theorem leviEmbedding_singletonLevi_val (t : Fin n → Rˣ) :
    ((singletons n).leviEmbedding R (singletonLevi R t)).val =
      Matrix.diagonal fun i => (t i : R) := by
  have key : ∀ i j : Fin n,
      (singletons n).leviEmbedding R (singletonLevi R t)
        ((singletons n).index i 0) ((singletons n).index j 0) =
      Matrix.diagonal (fun i => (t i : R)) i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [leviEmbedding_apply_same, Matrix.diagonal_apply_eq]
      simp [Matrix.scalar_apply]
    · rw [(singletons n).leviEmbedding_apply_ne R _ _ _ hij, Matrix.diagonal_apply_ne _ hij]
  ext i j
  have hk := key i j
  rwa [singletons_index, singletons_index] at hk

/-- For every block shape, the Levi action is conjugation of the underlying matrices. -/
@[simp] theorem leviAction_apply_val (B : BlockShape n) (m : B.Levi R)
    (v : B.unipotentRadical R) :
    (((B.leviAction R m v : B.unipotentRadical R) : B.parabolic R) :
      Langlands.GeneralLinear n R) =
      B.leviEmbedding R m * ((v : B.parabolic R) : Langlands.GeneralLinear n R) *
        (B.leviEmbedding R m)⁻¹ := rfl

/-- Diagonal Levi elements act on the upper unipotent group by matrix conjugation. -/
theorem leviAction_singletonLevi_upperUnipotentEquivRadical (t : Fin n → Rˣ)
    (u : upperUnipotent n R) :
    ((((singletons n).leviAction R (singletonLevi R t) (upperUnipotentEquivRadical R u) :
      (singletons n).unipotentRadical R) : (singletons n).parabolic R) :
        Langlands.GeneralLinear n R) =
      (singletons n).leviEmbedding R (singletonLevi R t) * u *
        ((singletons n).leviEmbedding R (singletonLevi R t))⁻¹ := rfl

end BlockShape
end Langlands.GeneralLinear

namespace Langlands.PadicField.TopologicalData

open Langlands.GeneralLinear Langlands.GeneralLinear.BlockShape

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The singleton block modulus of a diagonal element is the product of the root
quotients `|t_i| / |t_j|` over `i < j`. -/
theorem leviModulus_singletonLevi {n : ℕ} (t : Fin n → F.Carrierˣ) :
    T.leviModulus (singletons n) (singletonLevi F.Carrier t) =
      ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        T.normalizedAbsUnits (t i) / T.normalizedAbsUnits (t j) := by
  rw [T.leviModulus_apply]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [singletonLevi_apply, singletonLevi_apply, T.determinantNorm_scalar,
    T.determinantNorm_scalar]
  simp only [pow_one]

end Langlands.PadicField.TopologicalData
