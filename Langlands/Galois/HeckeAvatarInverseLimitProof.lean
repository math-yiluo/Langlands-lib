import Langlands.Galois.HeckeAvatarInverseLimit
import Langlands.ClassFieldTheory.Global.LocalUnitPowers

/-! # The continuous congruence limit of finite Hecke avatars -/

noncomputable section

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global Topology

private theorem exists_of_compatible_residues {R : Type*} [CommRing R] (I : Ideal R)
    [IsPrecomplete I R] (a : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (ha : ∀ {n m : ℕ} (h : n ≤ m),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.succ_le_succ h)) (a m) = a n) :
    ∃ x : R, ∀ n, Ideal.Quotient.mk (I ^ (n + 1)) x = a n := by
  classical
  choose x hx using fun n => Ideal.Quotient.mk_surjective (a n)
  have hcompat {n m : ℕ} (h : n ≤ m) : x n ≡ x m [SMOD (I ^ (n + 1) : Ideal R)] := by
    rw [SModEq.sub_mem, ← Ideal.Quotient.eq]
    rw [hx n, ← ha h, ← hx m, Ideal.Quotient.factor_mk]
  obtain ⟨y, hy⟩ := IsPrecomplete.prec' (I := I) x (fun {n m} h => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact (hcompat h).mono (Ideal.pow_le_pow_right (Nat.le_succ n)))
  refine ⟨y, fun n => ?_⟩
  rw [← hx n, Ideal.Quotient.eq, ← SModEq.sub_mem]
  have hnext := hy (n + 1)
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at hnext
  exact ((hcompat (Nat.le_succ n)).trans hnext).symm

private theorem eq_of_residue_eq {R : Type*} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    {x y : R} (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ (n + 1)) x =
      Ideal.Quotient.mk (I ^ (n + 1)) y) : x = y := by
  apply (IsHausdorff.eq_iff_smodEq (I := I)).2
  intro n
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  refine SModEq.mono (Ideal.pow_le_pow_right (Nat.le_succ n)) ?_
  rw [SModEq.sub_mem, ← Ideal.Quotient.eq]
  exact h n

section Completion

variable {L : Type uL} [Field L] [NumberField L] (lam : FinitePlace L)

local notation "O" => lam.adicCompletionIntegers L
local notation "𝔪" => IsLocalRing.maximalIdeal O

private theorem exists_completionUnit_of_compatible (u : ∀ n : ℕ, CompletionUnitQuotient lam n)
    (hu : ∀ {n m : ℕ} (h : n ≤ m), completionUnitTransition lam h (u m) = u n) :
    ∃ x : Oˣ, ∀ n, completionUnitReduction lam n x = u n := by
  let := Langlands.ClassFieldTheory.Global.isAdicComplete_adicCompletionIntegers lam
  have liftValue (v : ∀ n : ℕ, CompletionUnitQuotient lam n)
      (hv : ∀ {n m : ℕ} (h : n ≤ m), completionUnitTransition lam h (v m) = v n) :
      ∃ x : O, ∀ n, Ideal.Quotient.mk (𝔪 ^ (n + 1)) x =
        (show (O ⧸ 𝔪 ^ (n + 1))ˣ from v n).val :=
    exists_of_compatible_residues 𝔪 _ fun {n m} h =>
      congrArg (Units.val (α := O ⧸ 𝔪 ^ (n + 1))) (hv h)
  obtain ⟨x, hx⟩ := liftValue u hu
  obtain ⟨y, hy⟩ := liftValue (fun n => (u n)⁻¹) (fun h => by rw [map_inv, hu h])
  have hxy : x * y = 1 := eq_of_residue_eq 𝔪 fun n => by
    rw [map_mul, map_one, hx n, hy n]
    exact (show (O ⧸ 𝔪 ^ (n + 1))ˣ from u n).val_inv
  refine ⟨⟨x, y, hxy, by rw [mul_comm y x, hxy]⟩, fun n => ?_⟩
  exact Units.ext (hx n)

private theorem completionUnitReduction_injective :
    Function.Injective (fun u : Oˣ => fun n : ℕ => completionUnitReduction lam n u) := by
  let := Langlands.ClassFieldTheory.Global.isAdicComplete_adicCompletionIntegers lam
  intro x y h
  apply Units.ext
  exact eq_of_residue_eq 𝔪 fun n =>
    congrArg (Units.val (α := O ⧸ 𝔪 ^ (n + 1))) (congrFun h n)

private theorem completionUnitReduction_isEmbedding :
    IsEmbedding (fun u : Oˣ => fun n : ℕ => completionUnitReduction lam n u) := by
  let : CompactSpace O := Langlands.ClassFieldTheory.Global.compactSpace_adicCompletionIntegers lam
  exact ((continuous_pi fun n => (completionUnitReduction lam n).continuous).isClosedEmbedding
    (completionUnitReduction_injective lam)).toIsEmbedding

end Completion

/-- Unique geometric lifts at all positive congruence powers yield a continuous
character into the completed integer units. -/
theorem heckeAvatarInverseLimit : HeckeAvatarInverseLimitStatement.{uK, uL} := by
  classical
  intro K _ _ L _ _ lam S η h
  choose r hr hunique using h
  have hrTransition (n m : ℕ) (hle : n ≤ m) :
      (completionUnitTransition lam hle).comp (r m) = r n := by
    apply hunique n
    intro v hv
    obtain ⟨hinertia, hfrob⟩ := hr m v hv
    constructor
    · intro i
      change completionUnitTransition lam hle (r m (localToGlobalGalois v i.val)) = 1
      rw [hinertia i, map_one]
    · intro π hπ g hg
      exact (congrArg (completionUnitTransition lam hle) (hfrob π hπ g hg)).trans
        (completionUnitTransition_reduction lam hle _)
  have hLift (g : Field.absoluteGaloisGroup K) :
      ∃ u : (lam.adicCompletionIntegers L)ˣ, ∀ n, completionUnitReduction lam n u = r n g :=
    exists_completionUnit_of_compatible lam (fun n => r n g)
      (fun {n m} hle => DFunLike.congr_fun (hrTransition n m hle) g)
  choose f hf using hLift
  have hext {x y : (lam.adicCompletionIntegers L)ˣ}
      (hxy : ∀ n, completionUnitReduction lam n x = completionUnitReduction lam n y) : x = y :=
    completionUnitReduction_injective lam (funext hxy)
  let ψ : Field.absoluteGaloisGroup K →ₜ* (lam.adicCompletionIntegers L)ˣ :=
    { toFun := f
      map_one' := hext (fun n => by simp only [hf, map_one])
      map_mul' := fun g k => hext (fun n => by simp only [hf, map_mul])
      continuous_toFun := by
        apply (completionUnitReduction_isEmbedding lam).continuous_iff.mpr
        apply continuous_pi
        intro n
        change Continuous (fun g => completionUnitReduction lam n (f g))
        exact (map_continuous (r n)).congr fun g => (hf g n).symm }
  have hψ (n : ℕ) (g : Field.absoluteGaloisGroup K) :
      completionUnitReduction lam n (ψ g) = r n g := hf g n
  refine ⟨r, ψ, hr, hrTransition, fun n => ContinuousMonoidHom.ext (hψ n), ?_⟩
  intro v hv
  constructor
  · intro i
    refine hext (fun n => ?_)
    rw [hψ, map_one]
    exact (hr n v hv).1 i
  · intro π hπ g hg
    refine hext (fun n => ?_)
    rw [hψ]
    exact (hr n v hv).2 π hπ g hg

end Langlands.GaloisRepresentation
