import Langlands.ClassFieldTheory.Global.RelativeWeilTransfer
import Langlands.Global.HeckeCharacter
import Mathlib.Data.Matrix.Block
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

/-! # Cyclic character-twisted block sum on the relative Weil group -/

noncomputable section

set_option autoImplicit false

universe u v w

namespace Langlands.TraceFormula.CyclicBlockSum

open NumberField Langlands.ClassFieldTheory.Global Langlands.Global
open scoped NumberField

variable {I : Type v} [AddCommGroup I] {W : Type u} [Group W]

private theorem toAdd_one : (1 : Multiplicative I).toAdd = (0 : I) := rfl

private theorem toAdd_mul (x y : Multiplicative I) : (x * y).toAdd = x.toAdd + y.toAdd := rfl

/-- Translation of the dual factor labels by the additive Weil degree. -/
def shiftAction (k : W →* Multiplicative I) (G : Type w) [Group G] :
    W →* MulAut (I → G) where
  toFun t :=
    { toFun := fun f i => f (i + (k t).toAdd)
      invFun := fun f i => f (i - (k t).toAdd)
      left_inv := fun f => funext fun i => congrArg f (sub_add_cancel i _)
      right_inv := fun f => funext fun i => congrArg f (add_sub_cancel_right i _)
      map_mul' := fun _ _ => rfl }
  map_one' := by
    ext f i
    change f (i + (k 1).toAdd) = f i
    rw [map_one, toAdd_one, add_zero]
  map_mul' t s := by
    ext f i
    change f (i + (k (t * s)).toAdd) = f ((i + (k t).toAdd) + (k s).toAdd)
    rw [map_mul, toAdd_mul, add_assoc]

@[simp] theorem shiftAction_apply (k : W →* Multiplicative I) (G : Type w) [Group G]
    (t : W) (f : I → G) (i : I) :
    shiftAction k G t f i = f (i + (k t).toAdd) := rfl

abbrev DualGL (r : ℕ) := Matrix.GeneralLinearGroup (Fin r) ℂ
abbrev BlockGL (I : Type v) [Fintype I] [DecidableEq I] (b : ℕ) :=
  Matrix.GeneralLinearGroup (Fin b × I) ℂ

section Matrices

variable [Fintype I] [DecidableEq I]

/-- The genuine block diagonal matrices, as a group homomorphism on units. -/
def blockDiag (b : ℕ) : (I → DualGL b) →* BlockGL I b where
  toFun f :=
    ⟨Matrix.blockDiagonal (fun i => (f i).val), Matrix.blockDiagonal (fun i => (f i)⁻¹.val),
      by rw [← Matrix.blockDiagonal_mul]; simp only [← Units.val_mul, mul_inv_cancel,
           Units.val_one]; exact Matrix.blockDiagonal_one,
      by rw [← Matrix.blockDiagonal_mul]; simp only [← Units.val_mul, inv_mul_cancel,
           Units.val_one]; exact Matrix.blockDiagonal_one⟩
  map_one' := by
    apply Units.ext
    exact Matrix.blockDiagonal_one
  map_mul' f g := Units.ext (Matrix.blockDiagonal_mul (fun i => (f i).val) (fun i => (g i).val))

omit [AddCommGroup I] in
theorem blockDiag_injective (b : ℕ) : Function.Injective (blockDiag (I := I) b) := by
  intro f g h
  have hv : Matrix.blockDiagonal (fun i => (f i).val) =
      Matrix.blockDiagonal (fun i => (g i).val) := congrArg Units.val h
  exact funext fun i => Units.ext (congrFun (Matrix.blockDiagonal_injective hv) i)

end Matrices

private theorem scalar_commute (b : ℕ) (z : ℂˣ) (g : DualGL b) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin b) z) g := by
  apply Units.ext
  exact Matrix.scalar_comm (z : ℂ) (Commute.all _) g.val

section Relative

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

set_option hygiene false in
local notation "WR" => RelativeWeilGroup c F E

variable (κ : (E ≃ₐ[F] E) ≃* Multiplicative I)

/-- The degree of the actual relative Weil group, in the chosen cyclic labels. -/
def degree : WR →* Multiplicative I := κ.toMonoidHom.comp (RelativeWeilGroup.projection c F E)

variable (r : I → WR) (hr : ∀ i, degree c F E κ (r i) = Multiplicative.ofAdd i)

set_option hygiene false in
local notation "k" => degree c F E κ

/-- Right-transversal defect in the actual idele-class subgroup. -/
private def subgroupDefect (i : I) (t : WR) : RelativeWeilGroup.ideleClassSubgroup c F E :=
  ⟨r i * t * (r (i + (k t).toAdd))⁻¹, by
    change _ ∈ (RelativeWeilGroup.inclusion c F E).range
    rw [RelativeWeilGroup.exact, MonoidHom.mem_ker]
    apply κ.injective
    change k (r i * t * (r (i + (k t).toAdd))⁻¹) = κ 1
    rw [map_mul, map_mul, map_inv, hr, hr, map_one]
    exact mul_inv_cancel (Multiplicative.ofAdd i * k t)⟩

/-- The idele class `δ_i(t)` defined by `r_i t = δ_i(t) r_(i+k(t))`. -/
def ideleDefect (i : I) (t : WR) : IdeleClassGroup (𝓞 E) E :=
  RelativeWeilGroup.ideleClassSubgroupEquiv c F E (subgroupDefect c F E κ r hr i t)

@[simp] theorem inclusion_ideleDefect (i : I) (t : WR) :
    RelativeWeilGroup.inclusion c F E (ideleDefect c F E κ r hr i t) =
      r i * t * (r (i + (k t).toAdd))⁻¹ :=
  RelativeWeilGroup.inclusion_ideleClassSubgroupEquiv c F E _

@[simp] theorem ideleDefect_one (i : I) : ideleDefect c F E κ r hr i 1 = 1 := by
  apply RelativeWeilGroup.inclusion_injective c F E
  simp only [inclusion_ideleDefect, map_one, toAdd_one, add_zero,
    mul_one, mul_inv_cancel]

theorem ideleDefect_mul (i : I) (t s : WR) :
    ideleDefect c F E κ r hr i (t * s) =
      ideleDefect c F E κ r hr i t * ideleDefect c F E κ r hr (i + (k t).toAdd) s := by
  apply RelativeWeilGroup.inclusion_injective c F E
  simp only [map_mul, inclusion_ideleDefect, toAdd_mul, add_assoc]
  group

theorem ideleDefect_inclusion (i : I) (a : IdeleClassGroup (𝓞 E) E) :
    ideleDefect c F E κ r hr i (RelativeWeilGroup.inclusion c F E a) =
      AdelicFunctoriality.ideleClassEquiv
        (RelativeWeilGroup.projection c F E (r i)).toRingEquiv a := by
  have hp : RelativeWeilGroup.projection c F E (RelativeWeilGroup.inclusion c F E a) = 1 := by
    have hmem : RelativeWeilGroup.inclusion c F E a ∈
        (RelativeWeilGroup.inclusion c F E).range := ⟨a, rfl⟩
    rw [RelativeWeilGroup.exact] at hmem
    exact MonoidHom.mem_ker.mp hmem
  have hk : k (RelativeWeilGroup.inclusion c F E a) = 1 := by simp [degree, hp]
  apply RelativeWeilGroup.inclusion_injective c F E
  rw [inclusion_ideleDefect, hk, toAdd_one, add_zero, RelativeWeilGroup.conjugation]

variable [Fintype I] [DecidableEq I] (b : ℕ) (η : I → HeckeCharacter E)

set_option hygiene false in
local notation "D" => ((I → DualGL b) ⋊[shiftAction k (DualGL b)] WR)
set_option hygiene false in
local notation "U" => ((I → BlockGL I b) ⋊[shiftAction k (BlockGL I b)] WR)
set_option hygiene false in
local notation "dcl" => ideleDefect c F E κ r hr
set_option hygiene false in
local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin b)

/-- The shifted block homomorphism `ξ₀` of Clozel–Rajan §7.2, using the actual
relative Weil group and the actual idele-class characters. All dual factors
use the usual outer shift, so the block at index `α` in row `i` uses `h_(i−α)`.
At this stage the family `η` is supplied; the endoscopic datum requires additional
recurrence and regularity conditions. -/
def shiftedBlockEmbedding : D →* U where
  toFun x := ⟨fun i => blockDiag b (fun α => sc (η α (dcl i x.right)) * x.left (i - α)), x.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext i
      change blockDiag b (fun α => sc (η α (dcl i 1)) * 1) = 1
      simp only [ideleDefect_one, map_one, one_mul]
      exact map_one (blockDiag b)
    · rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · funext i
      change blockDiag b (fun α => sc (η α (dcl i (x.right * y.right))) *
        (x.left * shiftAction k (DualGL b) x.right y.left) (i - α)) =
        blockDiag b (fun α => sc (η α (dcl i x.right)) * x.left (i - α)) *
        blockDiag b (fun α => sc (η α (dcl (i + (k x.right).toAdd) y.right)) *
          y.left (i + (k x.right).toAdd - α))
      rw [← map_mul]
      congr 1
      funext α
      simp only [Pi.mul_apply, shiftAction_apply, ideleDefect_mul, map_mul]
      rw [show (i - α) + (k x.right).toAdd = (i + (k x.right).toAdd) - α by abel]
      let s := sc (η α (dcl i x.right))
      let t := sc (η α (dcl (i + (k x.right).toAdd) y.right))
      let g := x.left (i-α)
      let h := y.left (i + (k x.right).toAdd - α)
      change (s * t) * (g * h) = (s * g) * (t * h)
      calc
        _ = s * (t * g) * h := by simp only [mul_assoc]
        _ = _ := by
          rw [show t * g = g * t from (scalar_commute b _ g).eq]
          simp only [mul_assoc]
    · rfl

/-- Injectivity across both the dual factors and the relative Weil quotient. -/
theorem shiftedBlockEmbedding_injective :
    Function.Injective (shiftedBlockEmbedding c F E κ r hr b η) := by
  intro x y e
  have er : x.right = y.right := congrArg (fun z : U => z.right) e
  apply SemidirectProduct.ext
  · funext i
    have eb : blockDiag b (fun α => sc (η α (dcl i x.right)) * x.left (i - α)) =
        blockDiag b (fun α => sc (η α (dcl i y.right)) * y.left (i - α)) :=
      congrArg (fun z : U => z.left i) e
    have el := blockDiag_injective b eb
    have e0 := congrFun el 0
    change sc (η 0 (dcl i x.right)) * x.left (i - 0) =
      sc (η 0 (dcl i y.right)) * y.left (i - 0) at e0
    rw [er, sub_zero] at e0
    exact mul_left_cancel e0
  · exact er

/-- The zero row on the upper idele-class subgroup, with a transversal normalized at zero.
This is the block formula used to read a Satake system over `E`. -/
theorem shiftedBlockEmbedding_zero_inclusion (hr0 : r 0 = 1) (h : I → DualGL b)
    (a : IdeleClassGroup (𝓞 E) E) :
    (shiftedBlockEmbedding c F E κ r hr b η ⟨h, RelativeWeilGroup.inclusion c F E a⟩).left 0 =
      blockDiag b (fun α => sc (η α a) * h (-α)) := by
  change blockDiag b (fun α => sc (η α (dcl 0 (RelativeWeilGroup.inclusion c F E a))) * h (0-α)) = _
  rw [ideleDefect_inclusion, hr0, map_one,
    show (1 : E ≃ₐ[F] E).toRingEquiv = RingEquiv.refl E from rfl]
  simp only [AdelicFunctoriality.ideleClassEquiv_refl, ContinuousMulEquiv.refl_apply, zero_sub]

end Relative

end Langlands.TraceFormula.CyclicBlockSum
