import Langlands.LinearAlgebra.CartanDNumbering
import Langlands.LinearAlgebra.LeviCorootSpan

/-! # A star-fixed A2 face in type D4 -/

noncomputable section

open scoped BigOperators

namespace Langlands.LinearAlgebra

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y)

/-- A reflection of a numbered D4 base makes its vertices zero and one
into roots fixed by every automorphism of the original based datum. -/
theorem exists_reflection_fixed_pair_of_typeD4
    (B : P.Base) (e : B.support ≃ Fin 4)
    (hD : ∀ i j, P.pairing (e.symm i).val (e.symm j).val = CartanMatrix.D 4 i j) :
    ∃ w : P.Aut,
      (∀ i j : Fin 2,
        P.pairing (w.indexEquiv (e.symm (Fin.castLE (by decide) i)).val)
          (w.indexEquiv (e.symm (Fin.castLE (by decide) j)).val) = CartanMatrix.A 2 i j) ∧
      ∀ (s : P.Aut) (_ : ∀ j, j ∈ B.support ↔ s.indexEquiv j ∈ B.support) (i : Fin 4),
        i.val < 2 → s.indexEquiv (w.indexEquiv (e.symm i).val) = w.indexEquiv (e.symm i).val := by
  classical
  let a (i : Fin 4) : J := (e.symm i).val
  let z := P.reflectionPerm (a 3) (a 1)
  let r := P.reflectionPerm (a 2) z
  have hp (i j : Fin 4) : P.pairing (a i) (a j) = CartanMatrix.D 4 i j := hD i j
  have hroot :
      P.root z = P.root (a 1) + P.root (a 3) ∧
      P.coroot z = P.coroot (a 1) + P.coroot (a 3) := by
    constructor
    · rw [show z = P.reflectionPerm (a 3) (a 1) from rfl, P.root_reflectionPerm,
        P.reflection_apply_root, hp, show CartanMatrix.D 4 1 3 = -1 by decide]
      simp
    · rw [show z = P.reflectionPerm (a 3) (a 1) from rfl, P.coroot_reflectionPerm,
        P.coreflection_apply_coroot, hp, show CartanMatrix.D 4 3 1 = -1 by decide]
      simp
  have hr : P.root r = P.root (a 1) + P.root (a 3) + P.root (a 2) := by
    rw [show r = P.reflectionPerm (a 2) z from rfl, P.root_reflectionPerm,
      P.reflection_apply_root, P.pairing_eq_add_of_root_eq_add hroot.1,
      hp, hp, show CartanMatrix.D 4 1 2 = -1 by decide, show CartanMatrix.D 4 3 2 = 0 by decide,
      hroot.1]
    simp
  have hc : P.coroot r = P.coroot (a 1) + P.coroot (a 3) + P.coroot (a 2) := by
    have hz : P.pairing (a 2) z = -1 := by
      have h := P.flip.pairing_eq_add_of_root_eq_add hroot.2 (l := a 2)
      simpa only [RootPairing.pairing_flip, hp, show CartanMatrix.D 4 2 1 = -1 by decide,
        show CartanMatrix.D 4 2 3 = 0 by decide, add_zero] using h
    rw [show r = P.reflectionPerm (a 2) z from rfl, P.coroot_reflectionPerm,
      P.coreflection_apply_coroot, hz, hroot.2]
    simp
  have hpr (j : Fin 4) : P.pairing (a j) r =
      CartanMatrix.D 4 j 1 + CartanMatrix.D 4 j 3 + CartanMatrix.D 4 j 2 := by
    change P.root' (a j) (P.coroot r) = _
    rw [hc, map_add, map_add]
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (hp j 1) (hp j 3)) (hp j 2)
  let w := RootPairing.Equiv.reflection P r
  have h0 : P.root (w.indexEquiv (a 0)) = ∑ j : Fin 4, P.root (a j) := by
    rw [show w.indexEquiv (a 0) = P.reflectionPerm r (a 0) from rfl,
      P.root_reflectionPerm, P.reflection_apply_root, hpr, hr, Fin.sum_univ_four]
    norm_num [CartanMatrix.D]
    abel
  have h1 : w.indexEquiv (a 1) = a 1 := by
    apply P.root.injective
    rw [show w.indexEquiv (a 1) = P.reflectionPerm r (a 1) from rfl,
      P.root_reflectionPerm, P.reflection_apply_root, hpr]
    norm_num [CartanMatrix.D]
  refine ⟨w, ?_, fun s hs i hi => ?_⟩
  · intro i j
    rw [w.toHom.pairing, hD]
    fin_cases i <;> fin_cases j <;> decide
  let q : Equiv.Perm (Fin 4) :=
    (e.symm.trans (s.indexEquiv.subtypeEquiv hs)).trans e
  have hq (j : Fin 4) : a (q j) = s.indexEquiv (a j) := by
    dsimp [a, q]
    rw [e.symm_apply_apply]
    rfl
  have hfix : q 1 = 1 := by
    apply Langlands.CartanDNumbering.fixes_center (by decide : 4 ≤ 4) q
    intro j k
    rw [← hp, ← hp, hq, hq]
    exact s.toHom.pairing
  have hi' : i = 0 ∨ i = 1 := by
    fin_cases i <;> simp_all
  rcases hi' with rfl | rfl
  · apply P.root.injective
    rw [← s.root_weightMap_apply P P, h0]
    change s.weightEquiv (∑ j : Fin 4, P.root (a j)) = ∑ j : Fin 4, P.root (a j)
    rw [map_sum, ← Equiv.sum_comp q (fun j => P.root (a j))]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hq]
      exact s.root_weightMap_apply P P _
  · change s.indexEquiv (w.indexEquiv (a 1)) = _
    rw [h1, ← hq, hfix]

/-- If a based automorphism fixes a dominant cocharacter's simple zero
roots, it fixes every zero root, even for a different choice of base. -/
theorem indexEquiv_eq_of_root'_eq_zero
    (B : P.Base) (ν : Y) (hdom : ∀ j ∈ B.support, 0 ≤ P.root' j ν)
    (s : P.Aut) (hs : ∀ j ∈ B.support, P.root' j ν = 0 → s.indexEquiv j = j)
    {j : J} (hj : P.root' j ν = 0) : s.indexEquiv j = j := by
  let ℓ : Module.Dual ℤ X := P.toLinearMap.flip ν
  have hz := coroot_span_zero_eq_span_simple P.flip B.flip ℓ hdom
  have hr : P.root j ∈ Submodule.span ℤ (P.root '' {i | i ∈ B.support ∧ P.root' i ν = 0}) := by
    change P.root j ∈ Submodule.span ℤ (P.flip.coroot '' {i | i ∈ B.flip.support ∧ ℓ (P.flip.coroot i) = 0})
    rw [← hz]
    exact Submodule.subset_span ⟨j, hj, rfl⟩
  have hle : Submodule.span ℤ (P.root '' {i | i ∈ B.support ∧ P.root' i ν = 0}) ≤
      LinearMap.ker (s.weightMap - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change s.weightMap (P.root i) - P.root i = 0
    rw [s.root_weightMap_apply P P, hs i hi.1 hi.2, sub_self]
  apply P.root.injective
  rw [← s.root_weightMap_apply P P]
  exact sub_eq_zero.mp (hle hr)

/-- A reflected base of D4 makes its first two vertices fixed under every
automorphism preserving the original support. -/
def CartanD4StarFixedTypeA2Statement : Prop :=
  ∀ (J X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (B : P.Base) (e : B.support ≃ Fin 4),
    (∀ i j, P.pairing (e.symm i).val (e.symm j).val = CartanMatrix.D 4 i j) →
    ∃ w : P.Aut,
      (∀ i j : Fin 2,
        P.pairing (w.indexEquiv (e.symm (Fin.castLE (by decide) i)).val)
          (w.indexEquiv (e.symm (Fin.castLE (by decide) j)).val) = CartanMatrix.A 2 i j) ∧
      ∀ (s : P.Aut) (_ : ∀ j, j ∈ B.support ↔ s.indexEquiv j ∈ B.support) (i : Fin 4),
        i.val < 2 → s.indexEquiv (w.indexEquiv (e.symm i).val) = w.indexEquiv (e.symm i).val

theorem cartanD4StarFixedTypeA2 : CartanD4StarFixedTypeA2Statement := by
  intro J X Y _ _ P B e hD
  exact exists_reflection_fixed_pair_of_typeD4 P B e hD

end Langlands.LinearAlgebra
