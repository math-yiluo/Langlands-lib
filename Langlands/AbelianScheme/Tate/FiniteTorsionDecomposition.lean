import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Group.Equiv.Basic

/-! # Decomposition of actual integer-torsion subgroups -/

noncomputable section

namespace Langlands.AbelianScheme.Tate

/-- The actual kernel of integer multiplication on an abelian group. -/
abbrev TorsionKernel (M : Type*) [AddCommGroup M] (n : ℕ) :=
  (nsmulAddMonoidHom (α := M) n).ker

variable (M : Type*) [AddCommGroup M]

/-- Taking `d`-torsion inside `n`-torsion gives exactly `d`-torsion if `d ∣ n`. -/
def torsionKernelIteratedEquiv {d n : ℕ} (h : d ∣ n) :
    TorsionKernel (TorsionKernel M n) d ≃+ TorsionKernel M d where
  toFun x := ⟨x.val.val, by
    have hx := congrArg Subtype.val x.property
    exact hx⟩
  invFun x := ⟨⟨x.val, by
    obtain ⟨k, rfl⟩ := h
    change (d * k) • x.val = 0
    rw [mul_comm d k, mul_smul, show d • x.val = 0 from x.property, nsmul_zero]⟩,
    by apply Subtype.ext; exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Coprime torsion splits using the two multiplication maps. -/
def torsionKernelCoprimeEquiv {a b : ℕ} (hab : a.Coprime b) :
    TorsionKernel M (a * b) ≃+ TorsionKernel M a × TorsionKernel M b := by
  let f : TorsionKernel M (a * b) →+
      TorsionKernel M a × TorsionKernel M b :=
    { toFun := fun x =>
        (⟨b • x.val, by
          change a • (b • x.val) = 0
          rw [← mul_smul]
          exact x.property⟩,
        ⟨a • x.val, by
          change b • (a • x.val) = 0
          rw [← mul_smul, mul_comm b a]
          exact x.property⟩)
      map_zero' := by ext <;> simp
      map_add' := by intro x y; ext <;> simp }
  apply AddEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply (nsmul_eq_zero_iff_of_coprime hab).mp
    have h₁ := congrArg (fun z => (z.1 : M)) h
    have h₂ := congrArg (fun z => (z.2 : M)) h
    exact ⟨by simpa [f, nsmul_sub] using sub_eq_zero.mpr h₂,
      by simpa [f, nsmul_sub] using sub_eq_zero.mpr h₁⟩
  · rintro ⟨x, y⟩
    have hbez : (a : ℤ) * a.gcdA b + (b : ℤ) * a.gcdB b = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, hab.gcd_eq_one]
      rfl
    have hx : ((b : ℤ) * a.gcdB b) • x.val = x.val := by
      have he := congrArg (fun z : ℤ => z • x.val) hbez
      simpa only [add_zsmul, mul_zsmul, natCast_zsmul, smul_comm a (a.gcdA b),
        show a • x.val = 0 from x.property, smul_zero, zero_add, one_zsmul] using he
    have hy : ((a : ℤ) * a.gcdA b) • y.val = y.val := by
      have he := congrArg (fun z : ℤ => z • y.val) hbez
      simpa only [add_zsmul, mul_zsmul, natCast_zsmul, smul_comm b (a.gcdB b),
        show b • y.val = 0 from y.property, smul_zero, add_zero, one_zsmul] using he
    let z : M := a.gcdB b • x.val + a.gcdA b • y.val
    have hzx : b • z = x.val := by
      dsimp [z]
      rw [nsmul_add, smul_comm b (a.gcdA b), show b • y.val = 0 from y.property,
        smul_zero, add_zero]
      simpa only [mul_zsmul, natCast_zsmul] using hx
    have hzy : a • z = y.val := by
      dsimp [z]
      rw [nsmul_add, smul_comm a (a.gcdB b), show a • x.val = 0 from x.property,
        smul_zero, zero_add]
      simpa only [mul_zsmul, natCast_zsmul] using hy
    refine ⟨⟨z, ?_⟩, ?_⟩
    · change (a * b) • z = 0
      rw [mul_smul, hzx]
      exact x.property
    · apply Prod.ext <;> apply Subtype.ext
      · exact hzx
      · exact hzy

/-- Chinese remainder theorem on a fixed finite family of residue coordinates. -/
def piZmodCoprimeEquiv (r : ℕ) {a b : ℕ} (hab : a.Coprime b) :
    (Fin r → ZMod (a * b)) ≃+ (Fin r → ZMod a) × (Fin r → ZMod b) where
  toFun x := (fun i => (ZMod.chineseRemainder hab (x i)).1,
    fun i => (ZMod.chineseRemainder hab (x i)).2)
  invFun x i := (ZMod.chineseRemainder hab).symm (x.1 i, x.2 i)
  left_inv x := by funext i; exact (ZMod.chineseRemainder hab).symm_apply_apply _
  right_inv x := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst ((ZMod.chineseRemainder hab).apply_symm_apply _)
    · exact congrArg Prod.snd ((ZMod.chineseRemainder hab).apply_symm_apply _)
  map_add' x y := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst ((ZMod.chineseRemainder hab).map_add _ _)
    · exact congrArg Prod.snd ((ZMod.chineseRemainder hab).map_add _ _)

end Langlands.AbelianScheme.Tate
