import Langlands.LinearAlgebra.LeviCorootSpan
import Langlands.LinearAlgebra.RootDatumSimpleCorootEquiv

/-! # Fixed coweights of an involution of an integral root datum -/

noncomputable section

open Module
open Langlands.GroupScheme.SplitExistence (exists_dual_forall_ne_zero)
open Langlands.RootDatumSimpleCorootEquiv (simpleCorootBasis simpleCorootBasis_apply)

namespace Langlands.LinearAlgebra

variable {J X Y : Type*} [Fintype J] [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (σ : P.Aut)

private theorem exists_coroot_difference_functional :
    ∃ f : Dual ℤ Y, ∀ i, σ.indexEquiv i ≠ i →
      f (P.coroot i - σ.coweightEquiv (P.coroot i)) ≠ 0 := by
  classical
  let v : J → Y := fun i => P.coroot i - σ.coweightEquiv (P.coroot i)
  let s : Finset J := Finset.univ.filter (fun i => σ.indexEquiv i ≠ i)
  obtain ⟨f, hf⟩ := exists_dual_forall_ne_zero s v (fun i hi => by
    have hne : σ.indexEquiv i ≠ i := (Finset.mem_filter.mp hi).2
    have hv : v i ≠ 0 := by
      intro hz
      have hc := (sub_eq_zero.mp hz).symm
      rw [RootPairing.Equiv.coweightEquiv_apply,
        RootPairing.Hom.coroot_coweightMap_apply] at hc
      exact hne ((Equiv.symm_apply_eq σ.indexEquiv).mp (P.coroot.injective hc)).symm
    by_contra! h
    apply hv
    apply P.flip.toPerfPair.injective
    apply LinearMap.ext
    intro z
    simpa using h (P.toLinearMap z))
  exact ⟨f, fun i hi => hf i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)⟩

set_option linter.defProp false in
/-- For a suitable simple base, every fixed coweight is the sum of a norm and an
integral combination of simple coroots with fixed indices. -/
def exists_base_involution_norm [P.IsReduced] (hP : P.corootSpan ℤ = ⊤)
    (hσ : Function.Involutive σ.coweightEquiv) :
    ∃ B : P.Base, ∀ x : Y, σ.coweightEquiv x = x →
      ∃ y : Y, x - (y + σ.coweightEquiv y) ∈
        Submodule.span ℤ (P.coroot '' {i | i ∈ B.support ∧ σ.indexEquiv i = i}) := by
  classical
  obtain ⟨f, hf⟩ := exists_coroot_difference_functional P σ
  let ℓ : Dual ℤ Y := f - f.comp σ.coweightEquiv.toLinearMap
  have hzero (i : J) : ℓ (P.coroot i) = 0 ↔ σ.indexEquiv i = i := by
    constructor
    · intro hi
      by_contra h
      exact hf i h (by simpa [ℓ, map_sub] using hi)
    · intro hi
      have hi' : σ.indexEquiv.symm i = i :=
        (Equiv.symm_apply_eq σ.indexEquiv).mpr hi.symm
      simp [ℓ, RootPairing.Hom.coroot_coweightMap_apply, hi']
  let d : Y →ₗ[ℤ] Y := -σ.coweightEquiv.toLinearMap
  have hdℓ (v : Y) : ℓ (d v) = ℓ v := by
    change f (-σ.coweightEquiv v) - f (σ.coweightEquiv (-σ.coweightEquiv v)) =
      f v - f (σ.coweightEquiv v)
    simp only [map_neg, hσ v]
    omega
  obtain ⟨B, hB⟩ := exists_base_coroot_nonneg P ℓ
  let b := simpleCorootBasis B hP
  have hb (i : B.support) : b i = P.coroot i := simpleCorootBasis_apply B hP i
  have hpositive {v : Y}
      (hv : v ∈ AddSubmonoid.closure (P.coroot '' (B.support : Set J))) :
      0 ≤ ℓ v ∧ ∀ j : B.support, 0 ≤ b.coord j v := by
    induction hv using AddSubmonoid.closure_induction with
    | mem v hv =>
      obtain ⟨i, hi, rfl⟩ := hv
      refine ⟨hB i hi, fun j => ?_⟩
      rw [← hb ⟨i, hi⟩, Basis.coord_apply, Basis.repr_self_apply]
      split <;> norm_num
    | zero => simp
    | add v w _ _ hv hw =>
      exact ⟨by simpa only [map_add] using add_nonneg hv.1 hw.1,
        fun j => by simpa only [map_add] using add_nonneg (hv.2 j) (hw.2 j)⟩
  have himage (i : B.support) (hi : ℓ (b i) ≠ 0) (j : B.support) :
      0 ≤ b.coord j (d (b i)) := by
    let k := σ.indexEquiv.symm i
    have hroot : d (b i) = P.coroot (P.reflectionPerm k k) := by
      rw [P.coroot_reflectionPerm, P.coreflection_apply_self, hb]
      simp [d, k, RootPairing.Hom.coroot_coweightMap_apply]
    have hpos : 0 < ℓ (b i) := lt_of_le_of_ne (hb i ▸ hB i i.property) hi.symm
    have heval : 0 < ℓ (P.coroot (P.reflectionPerm k k)) := by rwa [← hroot, hdℓ]
    rw [hroot]
    rcases B.coroot_mem_or_neg_mem (P.reflectionPerm k k) with hv | hv
    · exact (hpositive hv).2 j
    · have hn := (hpositive hv).1
      rw [map_neg] at hn
      omega
  have hd_nonneg (v : Y)
      (hv : ∀ i : B.support, ℓ (b i) ≠ 0 → 0 ≤ b.coord i v)
      (j : B.support) (hj : ℓ (b j) ≠ 0) : 0 ≤ b.coord j (d v) := by
    conv in d v => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : ℓ (b i) = 0
    · have hfix := (hzero i).mp (by simpa [hb] using hi)
      have hsymm : σ.indexEquiv.symm i = i :=
        (Equiv.symm_apply_eq σ.indexEquiv).mpr hfix.symm
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      have hc : b.coord j (d (b i)) = 0 := by
        have hd : d (b i) = -b i := by
          simp [d, hb, RootPairing.Hom.coroot_coweightMap_apply, hsymm]
        simp [hd, Basis.coord_apply, hij]
      simp [hc]
    · exact mul_nonneg (hv i hi) (himage i hi j)
  refine ⟨B, fun x hx => ?_⟩
  let y := b.equivFun.symm (fun i => max (b.coord i x) 0)
  have hy (i : B.support) : b.coord i y = max (b.coord i x) 0 := by
    rw [Basis.coord_apply, ← Basis.equivFun_apply]
    exact congrFun (b.equivFun.apply_symm_apply _) i
  let r := x - (y + σ.coweightEquiv y)
  have hr_nonneg (j : B.support) (hj : ℓ (b j) ≠ 0) : 0 ≤ b.coord j r := by
    have hdy := hd_nonneg y (fun i _ => by rw [hy]; exact le_max_right _ _) j hj
    have hdiff := hd_nonneg (y - x) (fun i _ => by
      rw [map_sub, hy]
      exact sub_nonneg.mpr (le_max_left _ _)) j hj
    have hdx : d x = -x := by simp [d, hx]
    rw [map_sub, hdx, map_sub, map_neg] at hdiff
    have hdy' : b.coord j (d y) = -b.coord j (σ.coweightEquiv y) := by simp [d]
    rw [hdy'] at hdy hdiff
    simp only [r, map_sub, map_add, hy]
    omega
  have hdr : d r = -r := by
    change -σ.coweightEquiv (x - (y + σ.coweightEquiv y)) = _
    rw [map_sub, map_add, hx, hσ y, add_comm (σ.coweightEquiv y) y]
  refine ⟨y, ?_⟩
  change r ∈ _
  rw [← b.sum_repr r]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : ℓ (b i) = 0
  · apply Submodule.smul_mem
    rw [hb]
    exact Submodule.subset_span ⟨i, ⟨i.property, (hzero i).mp (by simpa [hb] using hi)⟩, rfl⟩
  · have hn := hr_nonneg i hi
    have hp := hd_nonneg r hr_nonneg i hi
    rw [hdr, map_neg] at hp
    have h : b.coord i r = 0 := by omega
    rw [← Basis.coord_apply, h, zero_smul]
    exact Submodule.zero_mem _

end Langlands.LinearAlgebra
