import Langlands.GroupScheme.Examples.HermitianMatrixBasic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Nat.Find

/-! # The actual Gram pairing and its attained Witt index -/

noncomputable section

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

universe u v w

variable {A : Type u} {B : Type w} {ι : Type v}
  [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
  {c : RingInvolution A} {d : RingInvolution B}

namespace Form

/-- The column-vector convention: conjugate-linear first, linear second. -/
def pairing (H : Form c ι) (x y : ι → A) : A :=
  ∑ i, ∑ j, c.bar (x i) * H.gram i j * y j

@[simp] theorem pairing_zero_left (H : Form c ι) (y : ι → A) : H.pairing 0 y = 0 := by
  simp [pairing]

@[simp] theorem pairing_zero_right (H : Form c ι) (x : ι → A) : H.pairing x 0 = 0 := by
  simp [pairing]

theorem pairing_add_left (H : Form c ι) (x y z : ι → A) :
    H.pairing (x + y) z = H.pairing x z + H.pairing y z := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right (H : Form c ι) (x y z : ι → A) :
    H.pairing x (y + z) = H.pairing x y + H.pairing x z := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_smul_left (H : Form c ι) (a : A) (x y : ι → A) :
    H.pairing (a • x) y = c.bar a * H.pairing x y := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pairing_smul_right (H : Form c ι) (a : A) (x y : ι → A) :
    H.pairing x (a • y) = a * H.pairing x y := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual pairing as a bundled sesquilinear map. -/
def sesquilinear (H : Form c ι) : (ι → A) →ₛₗ[c.bar.toRingHom] (ι → A) →ₗ[A] A where
  toFun x :=
    { toFun := H.pairing x
      map_add' := H.pairing_add_right x
      map_smul' := fun a y => H.pairing_smul_right a x y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact H.pairing_add_left x y z
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    exact H.pairing_smul_left a x y

@[simp] theorem sesquilinear_apply (H : Form c ι) (x y : ι → A) :
    H.sesquilinear x y = H.pairing x y := rfl

theorem bar_gram (H : Form c ι) (i j : ι) : c.bar (H.gram i j) = H.gram j i :=
  congrArg (fun M : Matrix ι ι A => M j i) H.hermitian

/-- Hermitian symmetry holds in every characteristic. -/
theorem bar_pairing (H : Form c ι) (x y : ι → A) :
    c.bar (H.pairing x y) = H.pairing y x := by
  simp only [pairing, map_sum, map_mul, RingInvolution.bar_bar, H.bar_gram]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The flipped convention is linear first and conjugate-linear second. -/
def linearFirst (H : Form c ι) : (ι → A) →ₗ[A] (ι → A) →ₛₗ[c.bar.toRingHom] A :=
  H.sesquilinear.flip

@[simp] theorem linearFirst_apply (H : Form c ι) (x y : ι → A) :
    H.linearFirst x y = H.pairing y x := rfl

theorem bar_linearFirst (H : Form c ι) (x y : ι → A) :
    c.bar (H.linearFirst x y) = H.linearFirst y x := H.bar_pairing y x

/-- Entrywise coefficient change respects the full Gram pairing. -/
theorem pairing_map (H : Form c ι) (J : Form d ι) (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hJ : (H.gram : Matrix ι ι A).map f = J.gram) (x y : ι → A) :
    J.pairing (fun i => f (x i)) (fun i => f (y i)) = f (H.pairing x y) := by
  simp only [pairing, map_sum, map_mul, hf]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← congrArg (fun M : Matrix ι ι B => M i j) hJ]
  rfl

/-- Total isotropy requires vanishing on every pair of vectors of the submodule. -/
def IsTotallyIsotropic (H : Form c ι) (W : Submodule A (ι → A)) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, H.pairing x y = 0

@[simp] theorem totallyIsotropic_bot (H : Form c ι) : H.IsTotallyIsotropic ⊥ := by
  intro x hx y _
  have hx0 : x = 0 := hx
  subst x
  exact H.pairing_zero_left y

theorem totallyIsotropic_iff_linearFirst (H : Form c ι) (W : Submodule A (ι → A)) :
    H.IsTotallyIsotropic W ↔ ∀ x ∈ W, ∀ y ∈ W, H.linearFirst x y = 0 := by
  constructor <;> intro h x hx y hy <;> exact h y hy x hx

end Form

section Field

variable {L : Type u} [Field L] {c : RingInvolution L} (H : Form c ι)

namespace Form

/-- The largest dimension of an actual totally isotropic subspace. -/
def wittIndex : ℕ := by
  classical
  exact Nat.findGreatest (fun n => ∃ W : Submodule L (ι → L),
    H.IsTotallyIsotropic W ∧ Module.finrank L W = n) (Fintype.card ι)

theorem wittIndex_le_card : H.wittIndex ≤ Fintype.card ι := by
  classical
  exact Nat.findGreatest_le _

/-- This is also the bound by the ambient vector-space dimension. -/
theorem wittIndex_le_finrank : H.wittIndex ≤ Module.finrank L (ι → L) := by
  simpa only [Module.finrank_fintype_fun_eq_card] using H.wittIndex_le_card

/-- Some actual totally isotropic submodule attains the index. -/
theorem exists_totallyIsotropic_finrank_eq_wittIndex :
    ∃ W : Submodule L (ι → L), H.IsTotallyIsotropic W ∧ Module.finrank L W = H.wittIndex := by
  classical
  apply Nat.findGreatest_spec (P := fun n => ∃ W : Submodule L (ι → L),
    H.IsTotallyIsotropic W ∧ Module.finrank L W = n) (Nat.zero_le _)
  exact ⟨⊥, H.totallyIsotropic_bot, by simp⟩

/-- Every actual totally isotropic submodule has dimension at most the index. -/
theorem finrank_le_wittIndex (W : Submodule L (ι → L)) (hW : H.IsTotallyIsotropic W) :
    Module.finrank L W ≤ H.wittIndex := by
  classical
  apply Nat.le_findGreatest
  · simpa only [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W
  · exact ⟨W, hW, rfl⟩

/-- A useful characterization independent of the bounded-search implementation. -/
theorem wittIndex_eq_iff (n : ℕ) : H.wittIndex = n ↔
    (∃ W : Submodule L (ι → L), H.IsTotallyIsotropic W ∧ Module.finrank L W = n) ∧
    ∀ W : Submodule L (ι → L), H.IsTotallyIsotropic W → Module.finrank L W ≤ n := by
  constructor
  · intro h
    exact ⟨h ▸ H.exists_totallyIsotropic_finrank_eq_wittIndex,
      fun W hW => h ▸ H.finrank_le_wittIndex W hW⟩
  · rintro ⟨⟨W, hW, hdim⟩, hmax⟩
    obtain ⟨U, hU, hdU⟩ := H.exists_totallyIsotropic_finrank_eq_wittIndex
    exact le_antisymm (hdU ▸ hmax U hU) (hdim ▸ H.finrank_le_wittIndex W hW)

end Form
end Field
end Langlands.GroupScheme.HermitianMatrix
