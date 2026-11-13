import Langlands.GroupScheme.Rational.DominantHighestWeightProof
import Langlands.GroupScheme.Reductive.DominantMultipleRootData
import Langlands.LinearAlgebra.RationalSpan
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Actual realized dominant characters span the character space -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open TensorProduct

namespace Langlands.RootDatum.DominantMultiple

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] [Finite ι]
    (P : RootPairing ι ℤ M N) (b : P.Base)

/-- Every finite based integral root pairing has an integral character strictly
positive on all simple coroots. No semisimplicity assumption is used. -/
theorem exists_strictly_dominant_character :
    ∃ δ : M, ∀ a ∈ b.support, 0 < P.toLinearMap δ (P.coroot a) := by
  classical
  have hdual : ∀ a : b.support, ∃ x : M,
      0 < P.toLinearMap x (P.coroot a) ∧
        ∀ c : b.support, c ≠ a → P.toLinearMap x (P.coroot c) = 0 := by
    intro a
    obtain ⟨x, _, d, hd, hx, hx0⟩ := exists_simple_dual P.flip b.flip a
    refine ⟨x, ?_, ?_⟩
    · change 0 < P.flip.toLinearMap (P.flip.root a) x
      rw [hx]
      exact hd
    · intro c hca
      change P.flip.toLinearMap (P.flip.root c) x = 0
      exact hx0 c c.property (fun h => hca (Subtype.ext h))
  choose x hxpos hxzero using hdual
  refine ⟨∑ a : b.support, x a, fun a ha => ?_⟩
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single (⟨a, ha⟩ : b.support)]
  · exact hxpos ⟨a, ha⟩
  · intro c _ hca
    exact hxzero c ⟨a, ha⟩ (Ne.symm hca)
  · simp

/-- Every integral character is a difference of two dominant integral characters,
including all directions orthogonal to the roots. -/
theorem exists_sub_dominant_characters (lam : M) :
    ∃ x y : M,
      (∀ a ∈ b.support, 0 ≤ P.toLinearMap x (P.coroot a)) ∧
      (∀ a ∈ b.support, 0 ≤ P.toLinearMap y (P.coroot a)) ∧ x - y = lam := by
  classical
  obtain ⟨δ, hδ⟩ := exists_strictly_dominant_character P b
  let K : ℤ := ∑ a : b.support, |P.toLinearMap lam (P.coroot a)|
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hbound (a : b.support) : |P.toLinearMap lam (P.coroot a)| ≤ K := by
    exact Finset.single_le_sum
      (fun (c : b.support) _ => abs_nonneg (P.toLinearMap lam (P.coroot c)))
      (Finset.mem_univ a)
  refine ⟨lam + K • δ, K • δ, ?_, ?_, by abel⟩
  · intro a ha
    rw [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have hp := hδ a ha
    have hb := hbound ⟨a, ha⟩
    have hl := neg_abs_le (P.toLinearMap lam (P.coroot a))
    have hδ1 : 1 ≤ P.toLinearMap δ (P.coroot a) := by omega
    nlinarith
  · intro a ha
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hK (hδ a ha).le

/-- A set containing a positive multiple of every dominant character spans a
submodule containing a positive multiple of every character. -/
theorem exists_pos_nsmul_mem_span_of_dominant_multiples
    (S : Set M)
    (hS : ∀ x : M, (∀ a ∈ b.support, 0 ≤ P.toLinearMap x (P.coroot a)) →
      ∃ m : ℕ, 0 < m ∧ m • x ∈ S) (lam : M) :
    ∃ m : ℕ, 0 < m ∧ m • lam ∈ Submodule.span ℤ S := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_sub_dominant_characters P b lam
  obtain ⟨m, hm, hxS⟩ := hS x hx
  obtain ⟨n, hn, hyS⟩ := hS y hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have heq : (m * n) • lam = n • (m • x) - m • (n • y) := by
    rw [← hxy, nsmul_sub, smul_smul, smul_smul, Nat.mul_comm n m]
  rw [heq]
  apply Submodule.sub_mem
  · simpa only [natCast_zsmul] using
      (Submodule.span ℤ S).smul_mem (n : ℤ) (Submodule.subset_span hxS)
  · simpa only [natCast_zsmul] using
      (Submodule.span ℤ S).smul_mem (m : ℤ) (Submodule.subset_span hyS)

end Langlands.RootDatum.DominantMultiple

namespace Langlands.LinearAlgebra.RationalSpan

variable {M : Type*} [AddCommGroup M]

/-- A set whose integral span contains a positive multiple of each element
spans the full rationalization. -/
theorem ratSpan_eq_top_of_multiples_mem_span (S : Set M)
    (hS : ∀ x : M, ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ S) :
    ratSpan S = ⊤ := by
  have hmap : ∀ x ∈ Submodule.span ℤ S, toRat x ∈ ratSpan S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact toRat_mem_ratSpan hx
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using (ratSpan S).add_mem hx hy
    | smul a x _ hx =>
      simpa only [map_zsmul, Int.cast_smul_eq_zsmul] using
        (ratSpan S).smul_mem (a : ℚ) hx
  have hgen (x : M) : toRat x ∈ ratSpan S := by
    obtain ⟨m, hm, hmx⟩ := hS x
    have h := hmap _ hmx
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at h
    exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.mpr hm.ne' : (m : ℚ) ≠ 0)).mp h
  have hall (z : ℚ ⊗[ℤ] M) : z ∈ ratSpan S := by
    induction z using TensorProduct.inductionOn with
    | tmul q x =>
      have h := (ratSpan S).smul_mem q (hgen x)
      simpa only [toRat_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
    | add x y hx hy => exact (ratSpan S).add_mem hx hy
  exact top_unique fun z _ => hall z

/-- For a finitely generated abelian group, containing positive multiples of
all elements makes the integral-span quotient finite. -/
theorem finite_quotient_span_of_multiples [Module.Finite ℤ M] (S : Set M)
    (hS : ∀ x : M, ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ S) :
    Finite (M ⧸ Submodule.span ℤ S) := by
  have : AddGroup.FG (M ⧸ Submodule.span ℤ S) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  apply AddCommGroup.finite_of_fg_isAddTorsion
  intro z
  induction z using Quotient.inductionOn' with
  | h x =>
    obtain ⟨m, hm, hmx⟩ := hS x
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨m, hm, ?_⟩
    change m • (Submodule.Quotient.mk x : M ⧸ Submodule.span ℤ S) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hmx

end Langlands.LinearAlgebra.RationalSpan

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SplitPinning

open Langlands.LinearAlgebra.RationalSpan Langlands.RootDatum.DominantMultiple

universe u

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- The actual integral characters that are dominant and realized by normalized
covariant coordinates of the supplied group. -/
def realizedDominantCharacters : Set (characterLattice p.torus) :=
  {lam | p.IsDominantWeight lam ∧ p.IsRealizedWeight lam}

/-- Every dominant character has a positive multiple among the realized dominant
characters, over the original field. -/
theorem exists_pos_nsmul_mem_realizedDominantCharacters (lam : characterLattice p.torus)
    (hlam : p.IsDominantWeight lam) :
    ∃ n : ℕ, 0 < n ∧ n • lam ∈ p.realizedDominantCharacters := by
  obtain ⟨n, hn, hreal⟩ := p.exists_pos_nsmul_isRealizedWeight lam hlam
  refine ⟨n, hn, ?_, hreal⟩
  intro a
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact mul_nonneg (Int.natCast_nonneg _) (hlam a)

/-- The realized dominant characters span a subgroup of finite index in the
full actual character lattice. -/
theorem finite_quotient_span_realizedDominantCharacters :
    Finite (characterLattice p.torus ⧸ Submodule.span ℤ p.realizedDominantCharacters) := by
  have : Module.Finite ℤ (characterLattice p.torus) := p.isSplitTorus.finite_characterLattice
  apply finite_quotient_span_of_multiples
  apply exists_pos_nsmul_mem_span_of_dominant_multiples p.rootDatum p.base
  intro lam hlam
  exact p.exists_pos_nsmul_mem_realizedDominantCharacters lam (fun a => hlam a a.property)

/-- Realized dominant characters span the full rational character space,
including the central-character directions. -/
theorem ratSpan_realizedDominantCharacters :
    ratSpan p.realizedDominantCharacters = ⊤ := by
  apply ratSpan_eq_top_of_multiples_mem_span
  apply exists_pos_nsmul_mem_span_of_dominant_multiples p.rootDatum p.base
  intro lam hlam
  exact p.exists_pos_nsmul_mem_realizedDominantCharacters lam (fun a => hlam a a.property)

end Langlands.GroupScheme.SplitPinning
