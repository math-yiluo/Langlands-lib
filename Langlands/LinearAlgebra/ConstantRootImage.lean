import Mathlib.LinearAlgebra.RootSystem.Irreducible
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic

/-! # Linear images of irreducible roots with constant squared length -/

noncomputable section

namespace Langlands.LinearAlgebra.ConstantRootImage

open Set

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N]
  (P : RootPairing ι ℚ M N) [P.IsIrreducible]

/-- Some root pairs nontrivially with each of two prescribed roots in an
irreducible root system. -/
theorem exists_pairing_ne_zero_pair (a b : ι) :
    ∃ c : ι, P.pairing c a ≠ 0 ∧ P.pairing c b ≠ 0 := by
  by_contra! hno
  let s : Set ι := {i | P.pairing i a ≠ 0}
  let q : Submodule ℚ M := Submodule.span ℚ (P.root '' s)
  have hs : s.Nonempty := ⟨a, by simp [s]⟩
  have hmem {i : ι} (hi : i ∈ s) : P.root i ∈ q :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  have htop : q = ⊤ := by
    apply P.span_root_image_eq_top_of_forall_orthogonal s hs
    intro j hj i hi
    have hja : P.pairing j a = 0 := by
      by_contra h
      exact hj (hmem h)
    have hji : P.pairing j i = 0 := by
      by_contra h
      let z := P.reflectionPerm i j
      have hz : P.pairing z a ≠ 0 := by
        change P.toLinearMap (P.root z) (P.coroot a) ≠ 0
        rw [P.root_reflectionPerm, P.reflection_apply_root]
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
          RootPairing.root_coroot_eq_pairing, smul_eq_mul, hja, zero_sub, ne_eq,
          neg_eq_zero, mul_eq_zero]
        exact not_or.mpr ⟨h, hi⟩
      have hzq := hmem hz
      have heq : P.root j = P.root z + P.pairing j i • P.root i := by
        rw [P.root_reflectionPerm, P.reflection_apply_root]
        module
      exact hj (heq ▸ q.add_mem hzq (q.smul_mem _ (hmem hi)))
    exact ⟨hji, P.pairing_eq_zero_iff'.mp hji⟩
  have hle : q ≤ LinearMap.ker (P.coroot' b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hno i hi
  have hb := hle (htop ▸ Submodule.mem_top (x := P.root b))
  have : (2 : ℚ) = 0 := by
    simpa only [LinearMap.mem_ker, RootPairing.root_coroot'_eq_pairing,
      RootPairing.pairing_same] using hb
  norm_num at this

variable (B : LinearMap.BilinForm ℚ M) (hB : B.IsSymm)
  {c : ℚ} (hlen : ∀ i, B (P.root i) (P.root i) = c)

include hB hlen in
omit [P.IsIrreducible] in
private theorem two_mul_apply_root_root_of_pairing_ne_zero (i j : ι)
    (hji : P.pairing j i ≠ 0) :
    2 * B (P.root j) (P.root i) = P.pairing j i * c := by
  have h := hlen (P.reflectionPerm i j)
  rw [P.root_reflectionPerm, P.reflection_apply_root] at h
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hlen, hB.eq (P.root i) (P.root j)] at h
  have hprod : P.pairing j i *
      (2 * B (P.root j) (P.root i) - P.pairing j i * c) = 0 := by
    nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hji)

include hB hlen in
private theorem apply_root_root_eq_zero_of_pairing_eq_zero (i j : ι)
    (hij : P.pairing i j = 0) :
    B (P.root i) (P.root j) = 0 := by
  obtain ⟨k, hki, hkj⟩ := exists_pairing_ne_zero_pair P i j
  have hpair : P.pairing (P.reflectionPerm i k) j = P.pairing k j := by
    change P.toLinearMap (P.root (P.reflectionPerm i k)) (P.coroot j) = _
    rw [P.root_reflectionPerm, P.reflection_apply_root]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      RootPairing.root_coroot_eq_pairing, smul_eq_mul, hij, mul_zero, sub_zero]
  have h₁ := two_mul_apply_root_root_of_pairing_ne_zero P B hB hlen j k hkj
  have h₂ := two_mul_apply_root_root_of_pairing_ne_zero P B hB hlen j
    (P.reflectionPerm i k) (hpair ▸ hkj)
  rw [hpair, P.root_reflectionPerm, P.reflection_apply_root] at h₂
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul] at h₂
  have hprod : P.pairing k i * B (P.root i) (P.root j) = 0 := by
    nlinarith [h₁, h₂]
  exact (mul_eq_zero.mp hprod).resolve_left hki

include hB hlen in
/-- A symmetric bilinear form constant on every root is determined on pairs
of roots by the root-coroot pairing. -/
theorem two_mul_apply_root_root (i j : ι) :
    2 * B (P.root j) (P.root i) = P.pairing j i * c := by
  by_cases hji : P.pairing j i = 0
  · rw [hji, zero_mul,
      apply_root_root_eq_zero_of_pairing_eq_zero P B hB hlen j i hji, mul_zero]
  · exact two_mul_apply_root_root_of_pairing_ne_zero P B hB hlen i j hji

variable [P.IsRootSystem]

include hB hlen in
/-- The root evaluations of the bilinear form determine every coroot on the
entire root space. -/
theorem two_smul_apply_root_eq_smul_coroot (i : ι) :
    (2 : ℚ) • B (P.root i) = c • P.coroot' i := by
  apply LinearMap.ext_on_range (RootPairing.IsRootSystem.span_root_eq_top (P := P))
  intro j
  change 2 * B (P.root i) (P.root j) = c * P.pairing j i
  rw [hB.eq (P.root i) (P.root j),
    two_mul_apply_root_root P B hB hlen i j, mul_comm]

section Image

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- All roots have one common nonzero squared length after applying a given
linear map and evaluating a supplied bilinear form. -/
def HasConstantRootImageLength (f : M →ₗ[ℚ] E) (C : LinearMap.BilinForm ℚ E) : Prop :=
  ∃ d : ℚ, d ≠ 0 ∧ ∀ i, C (f (P.root i)) (f (P.root i)) = d

variable {P}

/-- A linear map giving every root of an irreducible rational root system
one nonzero squared length has trivial kernel. -/
theorem injective_of_hasConstantRootImageLength
    (f : M →ₗ[ℚ] E) (C : LinearMap.BilinForm ℚ E) (hC : C.IsSymm)
    (h : HasConstantRootImageLength P f C) : Function.Injective f := by
  obtain ⟨d, hd, hlen⟩ := h
  let B' : LinearMap.BilinForm ℚ M := C.compl₁₂ f f
  have hB' : B'.IsSymm := ⟨fun x y => hC.eq (f x) (f y)⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply P.eq_zero_iff_forall_coroot'_eq_zero.mpr
  intro i
  have hcor := congrArg (fun φ : M →ₗ[ℚ] ℚ => φ (x - y))
    (two_smul_apply_root_eq_smul_coroot P B' hB' hlen i)
  change 2 * C (f (P.root i)) (f (x - y)) = d * P.coroot' i (x - y) at hcor
  rw [map_sub, hxy, sub_self, map_zero, mul_zero] at hcor
  exact (mul_eq_zero.mp hcor.symm).resolve_left hd

omit [P.IsRootSystem] in
/-- Under the same hypothesis the original full root-coroot pairing is
symmetric. -/
theorem pairing_symmetric_of_hasConstantRootImageLength
    (f : M →ₗ[ℚ] E) (C : LinearMap.BilinForm ℚ E) (hC : C.IsSymm)
    (h : HasConstantRootImageLength P f C) (i j : ι) :
    P.pairing i j = P.pairing j i := by
  obtain ⟨d, hd, hlen⟩ := h
  let B' : LinearMap.BilinForm ℚ M := C.compl₁₂ f f
  have hB' : B'.IsSymm := ⟨fun x y => hC.eq (f x) (f y)⟩
  have h₁ := two_mul_apply_root_root P B' hB' hlen i j
  have h₂ := two_mul_apply_root_root P B' hB' hlen j i
  rw [hB'.eq (P.root i) (P.root j)] at h₂
  exact mul_right_cancel₀ hd (h₂.symm.trans h₁)

end Image

end Langlands.LinearAlgebra.ConstantRootImage
