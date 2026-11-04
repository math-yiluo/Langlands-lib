import Langlands.Representation.MatrixCoefficient.CompactTranslateLatticeBoundStatement
import Langlands.Representation.Smooth.Admissibility.JacquetCartan
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-! # Uniform product bounds over compact translates -/

noncomputable section

open scoped BigOperators

namespace Langlands

universe uG uV uI

/-- Compact translates give finitely many smooth input pairs; finite maxima
preserve the positive radii and their strict weighted gaps. -/
theorem compactTranslateLatticeBound :
    CompactTranslateLatticeBoundStatement.{uG, uV, uI} := by
  intro G _ _ _ V _ _ ρ hρ I _ τ w hbound S₁ S₂ T hS₁ hS₂ hT φ v
  classical
  have hleft := JacquetCartanDatum.finite_image_of_isCompact
    (smoothContragredient ρ) (isSmooth_smoothPart ρ.dual) hS₁.inv φ
  have hright := JacquetCartanDatum.finite_image_of_isCompact
    ρ hρ (hT.isCompact.mul hS₂) v
  let L : Finset (SmoothDual ρ) := insert φ hleft.toFinset
  let W : Finset V := insert v hright.toFinset
  let P := (↑L : Type _) × (↑W : Type _)
  let p₀ : P := (⟨φ, by simp [L]⟩, ⟨v, by simp [W]⟩)
  have : Nonempty P := ⟨p₀⟩
  choose a ha C hC hcoeff using fun p : P =>
    hbound (p.1 : SmoothDual ρ) (p.2 : V)
  let b : I → ℝ := fun i => Finset.univ.sup' Finset.univ_nonempty (fun p : P => a p i)
  let D : ℝ := Finset.univ.sup' Finset.univ_nonempty C
  have hab : ∀ (p : P) i, a p i ≤ b i := by
    intro p i
    exact Finset.le_sup' (fun q : P => a q i) (Finset.mem_univ p)
  have hCD : ∀ p : P, C p ≤ D := by
    intro p
    exact Finset.le_sup' C (Finset.mem_univ p)
  have hb : ∀ i, 0 < b i ∧ b i ^ 2 * w i < 1 := by
    intro i
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.univ) Finset.univ_nonempty (fun q : P => a q i)
    change b i = a p i at hp
    rw [hp]
    exact ha p i
  refine ⟨b, hb, D, lt_of_lt_of_le (hC p₀) (hCD p₀), ?_⟩
  intro n k₁ hk₁ t ht k₂ hk₂
  let ψ := smoothContragredient ρ k₁⁻¹ φ
  let y := ρ (t * k₂) v
  have hψ : ψ ∈ L := by
    apply Finset.mem_insert_of_mem
    apply hleft.mem_toFinset.mpr
    exact ⟨k₁⁻¹, by simpa only [Set.mem_inv, inv_inv] using hk₁, rfl⟩
  have hy : y ∈ W := by
    apply Finset.mem_insert_of_mem
    apply hright.mem_toFinset.mpr
    exact ⟨t * k₂, ⟨t, ht, k₂, hk₂, rfl⟩, rfl⟩
  let p : P := (⟨ψ, hψ⟩, ⟨y, hy⟩)
  have heval : (φ : Module.Dual ℂ V) (ρ (k₁ * τ n * t * k₂) v) =
      (ψ : Module.Dual ℂ V) (ρ (τ n) y) := by
    change (φ : Module.Dual ℂ V) (ρ (k₁ * τ n * t * k₂) v) =
      (φ : Module.Dual ℂ V) (ρ (k₁⁻¹)⁻¹ (ρ (τ n) (ρ (t * k₂) v)))
    simp only [inv_inv, map_mul, Module.End.mul_apply]
  rw [heval]
  calc
    ‖(ψ : Module.Dual ℂ V) (ρ (τ n) y)‖ ≤ C p * ∏ i, a p i ^ n i := hcoeff p n
    _ ≤ D * ∏ i, b i ^ n i := by
      apply mul_le_mul (hCD p)
      · apply Finset.prod_le_prod₀
        · intro i _
          exact pow_nonneg (ha p i).1.le _
        · intro i _
          exact pow_le_pow_left₀ (ha p i).1.le (hab p i) _
      · exact Finset.prod_nonneg fun i _ => pow_nonneg (ha p i).1.le _
      · exact (lt_of_lt_of_le (hC p₀) (hCD p₀)).le

end Langlands
