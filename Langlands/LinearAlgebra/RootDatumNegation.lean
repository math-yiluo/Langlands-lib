import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Negation and negative bases of integral root data -/

noncomputable section

namespace Langlands.RootDatumNegation

variable {J M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootDatum J M N)

/-- Simultaneous negation on the full character and cocharacter lattices. -/
def negAut : P.Aut := by
  letI := P.indexNeg
  exact {
    weightMap := -LinearMap.id
    coweightMap := -LinearMap.id
    indexEquiv := Equiv.neg J
    weight_coweight_transpose := by ext y x; simp
    root_weightMap := by ext i; simp
    coroot_coweightMap := by ext i; simp
    bijective_weightMap := neg_bijective
    bijective_coweightMap := neg_bijective }

@[simp] theorem negAut_weightMap (x : M) : (negAut P).weightMap x = -x := rfl

@[simp] theorem negAut_coweightMap (x : N) : (negAut P).coweightMap x = -x := rfl

@[simp] theorem negAut_indexEquiv (i : J) :
    (negAut P).indexEquiv i = P.reflectionPerm i i := rfl

@[simp] theorem negAut_indexEquiv_symm (i : J) :
    (negAut P).indexEquiv.symm i = P.reflectionPerm i i := rfl

@[simp] theorem negAut_mul_self : negAut P * negAut P = 1 := by
  apply RootPairing.Equiv.weightHom_injective P
  ext x
  change -(-x) = x
  exact neg_neg x

@[simp] theorem negAut_inv : (negAut P)⁻¹ = negAut P :=
  inv_eq_of_mul_eq_one_left (negAut_mul_self P)

/-- Negation is central in the full root-datum automorphism group. -/
theorem negAut_comm (e : P.Aut) : negAut P * e = e * negAut P := by
  apply RootPairing.Equiv.weightHom_injective P
  ext x
  change -(e.weightMap x) = e.weightMap (-x)
  exact (map_neg _ _).symm

variable {J' M' N' : Type*} [AddCommGroup M'] [AddCommGroup N']
    {Q : RootDatum J' M' N'}

/-- Transport of a base preserves all integral root heights. -/
theorem height_map (b : P.Base) (e : RootPairing.Equiv P Q) (a : J) :
    (b.map e).height (e.indexEquiv a) = b.height a := by
  classical
  obtain ⟨c, -, -, hc⟩ := b.exists_root_eq_sum_int a
  have hb (j : J) : j ∈ b.support ↔ e.indexEquiv j ∈ (b.map e).support := by
    simp
  have hroot : Q.root (e.indexEquiv a) =
      ∑ j ∈ (b.map e).support, c (e.indexEquiv.symm j) • Q.root j := by
    calc
      Q.root (e.indexEquiv a) = e.weightMap (P.root a) :=
        (e.root_weightMap_apply P Q a).symm
      _ = ∑ j ∈ b.support, c j • Q.root (e.indexEquiv j) := by
        rw [hc, map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, e.root_weightMap_apply]
      _ = ∑ j ∈ (b.map e).support, c (e.indexEquiv.symm j) • Q.root j :=
        Finset.sum_equiv e.indexEquiv hb (fun j _ => by rw [Equiv.symm_apply_apply])
  rw [RootPairing.Base.height_eq_sum hroot, RootPairing.Base.height_eq_sum hc]
  exact (Finset.sum_equiv e.indexEquiv hb
    (fun j _ => by rw [Equiv.symm_apply_apply])).symm

/-- The negative base has precisely the negative roots as its positive roots. -/
theorem isPos_map_negAut (b : P.Base) (a : J) :
    (b.map (negAut P)).IsPos a ↔ ¬ b.IsPos a := by
  let := P.indexNeg
  have h := height_map P b (negAut P) (-a)
  change (b.map (negAut P)).height (-(-a)) = b.height (-a) at h
  rw [neg_neg, b.height_reflectionPerm_self] at h
  rw [RootPairing.Base.isPos_iff, h, RootPairing.Base.isPos_iff]
  have := b.height_ne_zero a
  omega

/-- Membership in the negative simple base is membership of the negative index
in the original base. -/
theorem mem_support_map_negAut (b : P.Base) (a : J) :
    a ∈ (b.map (negAut P)).support ↔ (negAut P).indexEquiv a ∈ b.support := by
  classical
  let := P.indexNeg
  change a ∈ (b.map (negAut P)).support ↔ -a ∈ b.support
  simp only [RootPairing.Base.support_map_eq, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, he⟩
    change -j = a at he
    have hn : -a = j := by rw [← he]; exact neg_neg j
    rw [hn]
    exact hj
  · intro ha
    exact ⟨-a, ha, by change -(-a) = a; exact neg_neg a⟩

end Langlands.RootDatumNegation
