import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-! # Equivariant factor-set averaging for prime-to-exponent extensions -/

noncomputable section

universe u v w

open scoped BigOperators

namespace Langlands.GroupScheme.EtaleExtensionSplit

variable {E : Type u} [Group E] {Q : Type v} [Group Q] [Fintype Q]

/-- Average the factor set of a supplied set section over the quotient. The
correction respects every supplied pair of automorphisms compatible with the
extension and the original section. The kernel need not carry a linear action. -/
theorem exists_equivariant_averaged_section (f : E →* Q) [IsMulCommutative f.ker]
    (s : Q → E) (hs : ∀ a, f (s a) = a)
    (p : ℕ) (hp : 1 < p) (hcard : (Fintype.card Q).Coprime p) (hK : ∀ x : f.ker, x ^ p = 1)
    {I : Type w} (α : I → E ≃* E) (β : I → Q ≃* Q)
    (hα : ∀ i x, f (α i x) = β i (f x)) (hβ : ∀ i a, s (β i a) = α i (s a)) :
    ∃ t : Q →* E, (∀ a, f (t a) = a) ∧ (∀ i a, t (β i a) = α i (t a)) := by
  classical
  let : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := mul_comm' }
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcard hp
  have hr' : Fintype.card Q * r ≡ 1 [MOD p] := by
    change Fintype.card Q * r % p = 1 % p
    rwa [Nat.mod_eq_of_lt hp]
  have hroot (x : f.ker) : (x ^ Fintype.card Q) ^ r = x := by
    rw [← pow_mul]
    simpa only [pow_one] using pow_eq_pow_of_modEq hr' (hK x)
  let c (a b : Q) : f.ker := ⟨s a * s b * (s (a * b))⁻¹, by
    simp [MonoidHom.mem_ker, hs]⟩
  let J (a : Q) : f.ker ≃* f.ker := MulAut.conjNormal (s a)
  have hc (a b z : Q) : c a b * c (a * b) z = J a (c b z) * c a (b * z) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, c, J, MulAut.conjNormal_apply, mul_assoc]
    group
  let B (a : Q) : f.ker := (∏ z : Q, c a z) ^ r
  have hprod (a b : Q) : c a b * B (a * b) = J a (B b) * B a := by
    have h1 : (c a b) ^ Fintype.card Q * (∏ z : Q, c (a * b) z) =
        J a (∏ z : Q, c b z) * (∏ z : Q, c a z) := by
      calc
        _ = ∏ z : Q, c a b * c (a * b) z := by simp [Finset.prod_mul_distrib]
        _ = ∏ z : Q, J a (c b z) * c a (b * z) := Finset.prod_congr rfl (fun z _ => hc a b z)
        _ = _ := by
          rw [Finset.prod_mul_distrib, ← map_prod]
          congr 1
          exact Fintype.prod_equiv (Equiv.mulLeft b) _ _ (fun _ => rfl)
    simpa only [mul_pow, hroot, map_pow, B] using congrArg (fun x : f.ker => x ^ r) h1
  let t (a : Q) : E := (B a : E)⁻¹ * s a
  have hmul (a b : Q) : t a * t b = t (a * b) := by
    have hb : (B a)⁻¹ * (J a (B b))⁻¹ * c a b = (B (a * b))⁻¹ := by
      apply mul_right_cancel (b := B (a * b))
      rw [mul_assoc, hprod]
      group
    have hb' := congrArg (fun x : f.ker => (x : E)) hb
    change (B a : E)⁻¹ * (J a (B b) : E)⁻¹ * (c a b : E) = (B (a * b) : E)⁻¹ at hb'
    calc
      t a * t b = ((B a : E)⁻¹ * (J a (B b) : E)⁻¹ * (c a b : E)) * s (a * b) := by
        simp only [t, J, c, MulAut.conjNormal_apply]
        group
      _ = t (a * b) := by rw [hb']
  refine ⟨MonoidHom.mk' t (fun a b => (hmul a b).symm), ?_, ?_⟩
  · intro a
    change f ((B a : E)⁻¹ * s a) = a
    simp [hs, MonoidHom.mem_ker.mp (B a).property]
  · intro i a
    let j : f.ker →* f.ker := {
      toFun x := ⟨α i x, MonoidHom.mem_ker.mpr (by
        rw [hα, MonoidHom.mem_ker.mp x.property, map_one])⟩
      map_one' := Subtype.ext (map_one (α i))
      map_mul' := fun x y => Subtype.ext (map_mul (α i) (x : E) y) }
    have hB : B (β i a) = j (B a) := by
      simp only [B, map_pow, map_prod]
      congr 1
      apply Fintype.prod_equiv (β i).symm
      intro z
      apply Subtype.ext
      change s (β i a) * s z * (s (β i a * z))⁻¹ =
        α i (s a * s ((β i).symm z) * (s (a * (β i).symm z))⁻¹)
      conv_lhs =>
        rw [← (β i).apply_symm_apply z, ← map_mul (β i), hβ i a, hβ i ((β i).symm z),
          hβ i (a * (β i).symm z)]
      simp only [map_mul, map_inv]
    change (B (β i a) : E)⁻¹ * s (β i a) = α i ((B a : E)⁻¹ * s a)
    rw [hB, hβ, map_mul, map_inv]
    rfl

end Langlands.GroupScheme.EtaleExtensionSplit
