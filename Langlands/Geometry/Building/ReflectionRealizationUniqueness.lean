import Langlands.Geometry.Building.RootDatumValuation
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.Geometry.Building.RealTorusDuality

/-! # Normalizer points realizing the same reflection differ by the centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- On a split torus, a character vanishing on the real cocharacter space is zero. -/
theorem eq_zero_of_eval_eq_zero (hT : IsSplitTorus T.toGrp) {χ : characterLattice T}
    (h : ∀ v : V T, eval T χ v = 0) : χ = 0 := by
  by_contra hχ
  have hne : latticePairing T χ ≠ 0 := by
    intro h0
    apply hχ
    apply hT.isPerfPair_latticePairing.bijective_left.injective
    rw [h0, map_zero]
  obtain ⟨ν, hν⟩ : ∃ ν, latticePairing T χ ν ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (LinearMap.ext hall)
  have h1 := h ((1 : ℝ) ⊗ₜ[ℤ] ν)
  rw [eval_tmul, one_mul, Int.cast_eq_zero] at h1
  exact hν h1

/-- Evaluation is additive in the character. -/
theorem eval_sub_apply (χ ψ : characterLattice T) (v : V T) :
    eval T (χ - ψ) v = eval T χ v - eval T ψ v := by
  simp only [eval_eq_pair, TensorProduct.tmul_sub, map_sub, LinearMap.sub_apply]

/-- Evaluation is compatible with integral multiples of the character. -/
theorem eval_zsmul_apply (n : ℤ) (χ : characterLattice T) (v : V T) :
    eval T (n • χ) v = n * eval T χ v := by
  rw [eval_eq_pair, eval_eq_pair, TensorProduct.tmul_smul, map_zsmul, LinearMap.smul_apply,
    zsmul_eq_mul]

/-- On a split torus, the characters separate the real cocharacter space. -/
theorem eq_zero_of_forall_eval_eq_zero (hT : IsSplitTorus T.toGrp) {u : V T}
    (h : ∀ χ : characterLattice T, eval T χ u = 0) : u = 0 := by
  apply (isPerfPair_of_isSplitTorus hT).bijective_right.injective
  rw [map_zero]
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply, LinearMap.flip_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r χ =>
    rw [← mul_one r, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply,
      ← eval_eq_pair, h, smul_zero]
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

/-- On a split torus, a nonzero character is nonzero at some real cocharacter. -/
theorem exists_eval_ne_zero (hT : IsSplitTorus T.toGrp) {χ : characterLattice T} (hχ : χ ≠ 0) :
    ∃ v : V T, eval T χ v ≠ 0 := by
  by_contra h
  push Not at h
  exact hχ (eq_zero_of_eval_eq_zero hT h)

variable {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Iterates of a point fixing a character and its kernel translate a vector by a
fixed kernel vector. -/
theorem smul_pow_eq_add (z : normalizerPoints i) (a : characterLattice T)
    (hzH : ∀ v : V T, eval T a v = 0 → z • v = v) (v₀ : V T)
    (h₀ : eval T a (z • v₀ - v₀) = 0) (N : ℕ) :
    (z ^ N) • v₀ = v₀ + N • (z • v₀ - v₀) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', mul_smul, ih, smul_add, normalizer_smul_def i z (N • _), map_nsmul,
      ← normalizer_smul_def, hzH _ h₀, succ_nsmul]
    abel

variable [IsAffineHom G.X.hom]

/-- **Two realizations of one reflection differ by the centralizer.** In the presence of a
finite relative Weyl group acting faithfully on the root span, two normalizer points that
realize the reflection along a nonzero character of a split torus differ by a point
centralizing the torus. -/
theorem RealizesReflection.inv_mul_mem_centralizerPoints (hT : IsSplitTorus T.toGrp)
    [Finite (relativeWeylGroup i)] (hinj : Function.Injective (relativeWeylAction i))
    {a : characterLattice T} (ha : a ≠ 0) {n m : normalizerPoints i}
    (hn : RealizesReflection i a n) (hm : RealizesReflection i a m) :
    (m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ * n ∈ centralizerPoints i := by
  set z : normalizerPoints i := m⁻¹ * n
  -- `z` fixes the kernel of `a` pointwise.
  have hmH : ∀ v : V T, eval T a v = 0 → m⁻¹ • v = v := by
    intro v hv
    conv_lhs => rw [← hm.2 v hv]
    rw [inv_smul_smul]
  have hzH : ∀ v : V T, eval T a v = 0 → z • v = v := by
    intro v hv
    rw [mul_smul, hn.2 v hv, hmH v hv]
  -- `z` fixes `a`.
  have hza : weylAction i z⁻¹ a = a := by
    have h1 : weylAction i m a = -a := hm.1
    have h2 : weylAction i n a = -a := hn.1
    have h3 : weylAction i n⁻¹ (-a) = a := by
      rw [← h2, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    show weylAction i (m⁻¹ * n)⁻¹ a = a
    rw [mul_inv_rev, inv_inv, map_mul, LinearEquiv.mul_apply, h1, h3]
  have heval : ∀ v : V T, eval T a (z • v) = eval T a v := by
    intro v
    rw [eval_normalizer_smul, hza]
  obtain ⟨v₀, hv₀⟩ := exists_eval_ne_zero hT ha
  have h₀ : eval T a (z • v₀ - v₀) = 0 := by
    rw [map_sub, heval, sub_self]
  -- Finite order forces `z • v₀ = v₀`.
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, 0 < N ∧
      (QuotientGroup.mk z : relativeWeylGroup i) ^ N = 1 :=
    ⟨orderOf (QuotientGroup.mk z : relativeWeylGroup i), orderOf_pos _, pow_orderOf_eq_one _⟩
  have hzN : (z ^ N) • v₀ = v₀ := by
    have := congrArg (fun w : relativeWeylGroup i => w • v₀) hN
    simp only [one_smul] at this
    rw [← QuotientGroup.mk_pow, relativeWeyl_mk_smul] at this
    exact this
  have hfix : z • v₀ = v₀ := by
    have h := smul_pow_eq_add i z a hzH v₀ h₀ N
    rw [hzN, left_eq_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (by exact_mod_cast hNpos.ne')
    · exact sub_eq_zero.1 h
  -- Hence `z` acts trivially on the real cocharacter space.
  have hzV : ∀ v : V T, z • v = v := by
    intro v
    set c := eval T a v / eval T a v₀
    have hdec : v = (v - c • v₀) + c • v₀ := by abel
    have hker : eval T a (v - c • v₀) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv₀, sub_self]
    rw [hdec, smul_add, hzH _ hker, normalizer_smul_def i z (c • v₀), map_smul,
      ← normalizer_smul_def, hfix]
  -- Hence `z` acts trivially on characters.
  have hzX : weylAction i z = 1 := by
    have hinv : weylAction i z⁻¹ = 1 := by
      apply LinearEquiv.ext
      intro χ
      show weylAction i z⁻¹ χ = χ
      apply sub_eq_zero.1
      apply eq_zero_of_eval_eq_zero hT
      intro v
      rw [eval_sub_apply, ← eval_normalizer_smul, hzV, sub_self]
    rw [← inv_inv z, map_inv, hinv, inv_one]
  -- Faithfulness of the relative Weyl action.
  have hrel : relativeWeylAction i (QuotientGroup.mk z) = 1 := by
    rw [relativeWeylAction_mk]
    exact Langlands.LinearAlgebra.RationalSpan.spanAut_eq_one_of_eq_one _ _ _ hzX
  have hmk : (QuotientGroup.mk z : relativeWeylGroup i) = 1 := hinj (hrel.trans (map_one _).symm)
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmk
  exact hmk

end Langlands.Geometry.Building
