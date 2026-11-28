import Langlands.LinearAlgebra.RootDatumNegation
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneReduction
import Mathlib.Tactic.Abel

/-! # Inversion in the D4 Weyl group -/

noncomputable section

namespace Langlands.RootDatumNegation

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (e : b.support ≃ Fin 4)
    (hD : ∀ i j : b.support, P.pairing i.val j.val = CartanMatrix.D 4 (e i) (e j))

include hD hspan in
/-- For a simply connected D4 root datum, the cube of the Coxeter word on
vertices `0, 1, 2, 3` negates the whole root datum. -/
theorem negAut_mem_weylGroup_of_D4 : negAut P ∈ P.weylGroup := by
  let v (i : Fin 4) : J := (e.symm i).val
  let α (i : Fin 4) := P.root (v i)
  let s (i : Fin 4) : P.Aut := RootPairing.Equiv.reflection P (v i)
  have hs (i j : Fin 4) : (s i).weightMap (α j) = α j - (CartanMatrix.D 4 j i) • α i := by
    change P.reflection (v i) (P.root (v j)) = _
    rw [RootPairing.reflection_apply]
    change α j - (P.pairing (v j) (v i)) • α i = _
    simp only [v, hD, Equiv.apply_symm_apply]
  have hsmem (i : Fin 4) : s i ∈ P.weylGroup := P.reflection_mem_weylGroup (v i)
  let c := s 0 * (s 1 * (s 2 * s 3))
  have hc : c ∈ P.weylGroup := mul_mem (hsmem 0) (mul_mem (hsmem 1) (mul_mem (hsmem 2) (hsmem 3)))
  have hmap (x : X) : c.weightMap x = (s 0).weightMap
      ((s 1).weightMap ((s 2).weightMap ((s 3).weightMap x))) := rfl
  have h0 : c.weightMap (α 0) = α 1 := by
    rw [hmap]
    norm_num [hs, CartanMatrix.D, map_sub, map_zsmul]
    abel
  have h1 : c.weightMap (α 1) = α 0 + α 1 + α 2 + α 3 := by
    rw [hmap]
    norm_num [hs, CartanMatrix.D, map_sub, map_zsmul]
    abel
  have h2 : c.weightMap (α 2) = -(α 0 + α 1 + α 2) := by
    rw [hmap]
    norm_num [hs, CartanMatrix.D, map_sub, map_zsmul]
    abel
  have h3 : c.weightMap (α 3) = -(α 0 + α 1 + α 3) := by
    rw [hmap]
    norm_num [hs, CartanMatrix.D, map_sub, map_zsmul]
    abel
  have hcube (i : Fin 4) : (c ^ 3).weightMap (α i) = -α i := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
    change c.weightMap (c.weightMap (c.weightMap (α i))) = _
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [h0, h1, h2, h3, map_add, map_neg] <;> abel
  have hfix (a : b.support) : ((c ^ 3) * negAut P).indexEquiv a = a := by
    apply P.root.injective
    rw [← RootPairing.Hom.root_weightMap_apply]
    let i := e a
    have hi : v i = a := congrArg Subtype.val (e.symm_apply_apply a)
    change (c ^ 3).weightMap ((negAut P).weightMap (P.root a.val)) = P.root a.val
    rw [← hi, negAut_weightMap, map_neg]
    change -(c ^ 3).weightMap (α i) = α i
    rw [hcube, neg_neg]
  have he := Langlands.GroupScheme.InnerTypeANormOneReduction.aut_eq_one_of_simple b hspan
    ((c ^ 3) * negAut P) hfix
  have hn : c ^ 3 = negAut P := (eq_inv_of_mul_eq_one_left he).trans (negAut_inv P)
  exact hn ▸ pow_mem hc 3

end Langlands.RootDatumNegation
