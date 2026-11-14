import Langlands.LinearAlgebra.RootDatumIsogeny
import Langlands.LinearAlgebra.RootDatumCoweightFace
import Langlands.LinearAlgebra.RootDatumZeroFace

/-! # Chamber simple roots under root-datum isogenies -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v u' v'

namespace Langlands.LinearAlgebra.RootDatumIsogeny

open Set

section ChamberCriterion

variable {J : Type v} {M N : Type u} [Finite J] [AddCommGroup M] [AddCommGroup N]
    {P : RootDatum J M N} [P.IsReduced]

omit [Finite J] [P.IsReduced] in
/-- A regular functional positive on a base has precisely that base's
positive system. -/
theorem isPos_iff_functional_pos
    (b : P.Base) (l : M →ₗ[ℤ] ℤ) (hl : ∀ i, l (P.root i) ≠ 0)
    (hb : ∀ i ∈ b.support, 0 < l (P.root i)) (i : J) :
    b.IsPos i ↔ 0 < l (P.root i) := by
  have hnonneg (x : M)
      (hx : x ∈ AddSubmonoid.closure (P.root '' (b.support : Set J))) :
      0 ≤ l x := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact (hb j hj).le
    | zero => simp
    | add x y _ _ hx hy =>
      simpa only [map_add] using add_nonneg hx hy
  constructor
  · intro hi
    exact lt_of_le_of_ne
      (hnonneg _ ((RootDatumZeroFace.isPos_iff_mem_closure b i).mp hi)) (hl i).symm
  · intro hi
    by_contra h
    have hn := hnonneg _ ((RootDatumZeroFace.neg_mem_closure_iff_not_isPos b i).mpr h)
    simp only [map_neg] at hn
    omega

/-- A positive root is simple exactly when reflection in it preserves
positivity of every other positive root. -/
theorem mem_support_iff_reflection_pos
    (b : P.Base) (l : M →ₗ[ℤ] ℤ)
    (hsign : ∀ i, b.IsPos i ↔ 0 < l (P.root i)) (i : J) :
    i ∈ b.support ↔ 0 < l (P.root i) ∧
      ∀ j, 0 < l (P.root j) → j ≠ i →
        0 < l (P.reflection i (P.root j)) := by
  constructor
  · intro hi
    refine ⟨(hsign i).mp (b.isPos_of_mem_support hi), ?_⟩
    intro j hj hji
    rw [← P.root_reflectionPerm]
    exact (hsign _).mp (((hsign j).mpr hj).reflectionPerm hi hji)
  · rintro ⟨hi, hreflect⟩
    rw [b.mem_support_iff_positive_indecomposable P i]
    refine ⟨(hsign i).mpr hi, ?_⟩
    intro a c ha hc heq
    have ha' := (hsign a).mp ha
    have hc' := (hsign c).mp hc
    have hsum : l (P.root i) = l (P.root a) + l (P.root c) := by
      rw [heq, map_add]
    have hai : a ≠ i := by
      intro h
      subst a
      omega
    have hci : c ≠ i := by
      intro h
      subst c
      omega
    have hra := hreflect a ha' hai
    have hrc := hreflect c hc' hci
    have hr :
        l (P.reflection i (P.root a)) + l (P.reflection i (P.root c)) =
          -l (P.root i) := by
      rw [← map_add, ← map_add, ← heq, P.reflection_apply_self, map_neg]
    omega

end ChamberCriterion

variable {p : ℕ} {J : Type v} {X Y : Type u} {J' : Type v'} {X' Y' : Type u'}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    [Finite J] [Finite J']
    [Module.Finite ℤ X] [Module.Finite ℤ Y]
    [Module.Finite ℤ X'] [Module.Finite ℤ Y']
    {P : RootDatum J X Y} {Q : RootDatum J' X' Y'}
    [P.IsReduced] [Q.IsReduced]

/-- The actual weight map commutes with reflection in corresponding roots,
including nonconstant root factors. -/
theorem weightMap_reflection (f : RootDatumIsogeny p P Q) (i : J) (x : X) :
    f.weightMap (P.reflection i x) =
      Q.reflection (f.indexEquiv i) (f.weightMap x) := by
  have hpair :
      (Q.coroot' (f.indexEquiv i)) (f.weightMap x) =
        (f.rootFactor i : ℤ) * (P.coroot' i) x := by
    change Q.toLinearMap (f.weightMap x) (Q.coroot (f.indexEquiv i)) =
      (f.rootFactor i : ℤ) * P.toLinearMap x (P.coroot i)
    rw [f.pairing_apply, f.coroot_coweightMap, map_smul, smul_eq_mul]
  simp only [RootPairing.reflection_apply, map_sub, map_smul,
    f.root_weightMap, hpair, smul_smul]
  rw [mul_comm]

/-- A root has the same sign on a coweight as its positive multiple under
the actual weight map. -/
theorem root_pos_coweightMap_iff (f : RootDatumIsogeny p P Q) (v : Y') (i : J) :
    0 < P.toLinearMap (P.root i) (f.coweightMap v) ↔
      0 < Q.toLinearMap (Q.root (f.indexEquiv i)) v := by
  rw [← f.pairing_apply, f.root_weightMap]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact mul_pos_iff_of_pos_left (by exact_mod_cast f.rootFactor_pos i)

/-- Positivity after a corresponding reflection is preserved even when
the reflected root has a different characteristic-power factor. -/
theorem reflection_root_pos_coweightMap_iff
    (f : RootDatumIsogeny p P Q) (v : Y') (i j : J) :
    0 < P.toLinearMap (P.reflection i (P.root j)) (f.coweightMap v) ↔
      0 < Q.toLinearMap
        (Q.reflection (f.indexEquiv i) (Q.root (f.indexEquiv j))) v := by
  rw [← f.pairing_apply, f.weightMap_reflection, f.root_weightMap]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact mul_pos_iff_of_pos_left (by exact_mod_cast f.rootFactor_pos j)

/-- Bases adapted to a coweight and its pullback have exactly corresponding
simple roots. -/
theorem mem_support_iff_of_coweight_signs
    (f : RootDatumIsogeny p P Q) (v : Y') (b : P.Base) (b' : Q.Base)
    (hb : ∀ i, b.IsPos i ↔
      0 < P.toLinearMap (P.root i) (f.coweightMap v))
    (hb' : ∀ j, b'.IsPos j ↔ 0 < Q.toLinearMap (Q.root j) v) (i : J) :
    i ∈ b.support ↔ f.indexEquiv i ∈ b'.support := by
  rw [mem_support_iff_reflection_pos b (P.toLinearMap.flip (f.coweightMap v)) hb,
    mem_support_iff_reflection_pos b' (Q.toLinearMap.flip v) hb']
  constructor
  · rintro ⟨hi, hr⟩
    refine ⟨(f.root_pos_coweightMap_iff v i).mp hi, ?_⟩
    intro j hj hji
    change 0 < Q.toLinearMap (Q.root j) v at hj
    let a := f.indexEquiv.symm j
    have hea : f.indexEquiv a = j := f.indexEquiv.apply_symm_apply j
    have ha : 0 < P.toLinearMap (P.root a) (f.coweightMap v) :=
      (f.root_pos_coweightMap_iff v a).mpr (by simpa only [hea] using hj)
    have hai : a ≠ i := by
      intro h
      apply hji
      rw [← hea, h]
    have h := (f.reflection_root_pos_coweightMap_iff v i a).mp (hr a ha hai)
    change 0 < Q.toLinearMap (Q.reflection (f.indexEquiv i) (Q.root j)) v
    simpa only [hea] using h
  · rintro ⟨hi, hr⟩
    refine ⟨(f.root_pos_coweightMap_iff v i).mpr hi, ?_⟩
    intro j hj hji
    exact (f.reflection_root_pos_coweightMap_iff v i j).mpr
      (hr (f.indexEquiv j) ((f.root_pos_coweightMap_iff v j).mp hj)
        (fun h => hji (f.indexEquiv.injective h)))

end Langlands.LinearAlgebra.RootDatumIsogeny
