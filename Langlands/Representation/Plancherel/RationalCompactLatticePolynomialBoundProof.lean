import Langlands.Representation.Plancherel.RationalCompactLatticePolynomialBoundStatement
import Langlands.Representation.MatrixCoefficient.CompactTranslateLatticeBoundProof
import Langlands.GroupScheme.Rational.CompactMatrixIntegrality
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # From exponential lattice estimates to polynomial matrix-norm bounds -/

noncomputable section

universe u uV uI

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators NNReal
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.LocalField

/-- Residue normalization preserves the order of the actual valuation. -/
theorem residueNormalizedAbsoluteValue_le_of_vle
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {x y : F} (hxy : x ≤ᵥ y) :
    residueNormalizedAbsoluteValue F x ≤ residueNormalizedAbsoluteValue F y := by
  have hq : (1 : ℝ≥0) < (residueCardinality F : ℝ≥0) := by
    exact_mod_cast residueCardinality_gt_one F
  apply NNReal.coe_le_coe.mpr
  apply (WithZeroMulInt.toNNReal_strictMono hq).monotone
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F x) ≤
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F y)
  exact (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)).2
    ((Valuation.Compatible.vle_iff_le x y).mp hxy)

end Langlands.LocalField

namespace Langlands.GroupScheme.MatrixRepresentation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Compact sets have bounded actual residue-normalized matrix norms. This
uses the canonical point topology without changing the field topology. -/
theorem exists_rationalMatrixNorm_bound (ρ : MatrixRepresentation G n)
    (C : Set (rationalPoints G))
    (hC : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact C)
    (hCinv : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (Inv.inv '' C)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ g ∈ C, rationalMatrixNorm F ρ g ≤ B := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  obtain ⟨b, _, hb⟩ := ρ.exists_rationalMatrix_entry_bound
    (C ∪ Inv.inv '' C) (hC.union hCinv)
  refine ⟨max 1 (LocalField.residueNormalizedAbsoluteValue F b), le_max_left _ _, ?_⟩
  intro g hg
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  apply HarishChandraSchwartz.glNorm_le
  · intro i j
    exact (LocalField.residueNormalizedAbsoluteValue_le_of_vle F
      (hb g (Or.inl hg) i j)).trans (le_max_right _ _)
  · intro i j
    change LocalField.residueNormalizedAbsoluteValue F
      (((ρ.rationalMatrix g)⁻¹).val i j) ≤ _
    have h := LocalField.residueNormalizedAbsoluteValue_le_of_vle F
      (hb g⁻¹ (Or.inr ⟨g, hg, rfl⟩) i j)
    simpa only [map_inv] using h.trans (le_max_right _ _)

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.Plancherel.CompactLatticePolynomialBound

open GroupScheme MatrixRepresentation

/-- One natural exponent dominates any finite family of positive coordinate
radii by powers of a fixed real number greater than one. -/
theorem exists_prod_le_pow_sum
    {I : Type uI} [Fintype I] (a : I → ℝ) (ha : ∀ i, 0 < a i)
    {q : ℝ} (hq : 1 < q) :
    ∃ d : ℕ, ∀ m : I → ℕ, ∏ i, a i ^ m i ≤ (q ^ (∑ i, m i)) ^ d := by
  classical
  have hi : ∀ i, ∃ d : ℕ, a i < q ^ d :=
    fun i => pow_unbounded_of_one_lt (a i) hq
  choose d hd using hi
  let D : ℕ := ∑ i, d i
  refine ⟨D, fun m => ?_⟩
  calc
    ∏ i, a i ^ m i ≤ ∏ i, (q ^ D) ^ m i := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact pow_nonneg (ha i).le _
      · intro i _
        apply pow_le_pow_left₀ (ha i).le
        exact (hd i).le.trans (pow_le_pow_right₀ hq.le (Finset.single_le_sum
          (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)))
    _ = (q ^ D) ^ (∑ i, m i) := by rw [Finset.prod_pow_eq_pow_sum]
    _ = (q ^ (∑ i, m i)) ^ D := by simp only [← pow_mul, Nat.mul_comm]

end Langlands.Plancherel.CompactLatticePolynomialBound

namespace Langlands.Plancherel

open GroupScheme MatrixRepresentation

/-- Convert a supplied coordinate-height comparison and product coefficient
estimates into polynomial bounds on all supplied compact lattice charts. -/
theorem rationalCompactLatticePolynomialBound_of_power_height :
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
      (ρ : MatrixRepresentation G n)
      (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G))
      (I : Type uI) [Fintype I] (τ : (I → ℕ) → rationalPoints G),
      (∀ (φ : SmoothDual π.representation) (v : π),
        ∃ a : I → ℝ, (∀ i, 0 < a i) ∧
          ∃ C : ℝ, 0 < C ∧ ∀ m : I → ℕ,
            ‖(φ : Module.Dual ℂ π) (π.representation (τ m) v)‖ ≤
              C * ∏ i, a i ^ m i) →
      (∃ (q A : ℝ) (D : ℕ), 1 < q ∧ 0 < A ∧ ∀ m : I → ℕ,
        q ^ (∑ i, m i) ≤ A * rationalMatrixNorm F ρ (τ m) ^ D) →
      ∀ (S₁ S₂ T : Set (rationalPoints G)), IsCompact S₁ → IsCompact S₂ → T.Finite →
        ∀ (φ : SmoothDual π.representation) (v : π),
          ∃ (d : ℕ) (c : ℝ), 0 < c ∧
            ∀ (m : I → ℕ) (k₁ : rationalPoints G), k₁ ∈ S₁ →
              ∀ t : rationalPoints G, t ∈ T →
                ∀ k₂ : rationalPoints G, k₂ ∈ S₂ →
                  ‖(φ : Module.Dual ℂ π)
                    (π.representation (k₁ * τ m * t * k₂) v)‖ ≤
                      c * rationalMatrixNorm F ρ (k₁ * τ m * t * k₂) ^ d := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro n _ _ _ ρ π I _ τ hcoeff hheight S₁ S₂ T hS₁ hS₂ hT φ v
  obtain ⟨q, A, D, hq, hA, hheight⟩ := hheight
  have hlattice : ∀ (ψ : SmoothDual π.representation) (w : π),
      ∃ a : I → ℝ, (∀ i, 0 < a i ∧ a i ^ 2 * (0 : ℝ) < 1) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ m : I → ℕ,
          ‖(ψ : Module.Dual ℂ π) (π.representation (τ m) w)‖ ≤
            C * ∏ i, a i ^ m i := by
    intro ψ w
    obtain ⟨a, ha, C, hC, hb⟩ := hcoeff ψ w
    exact ⟨a, fun i => ⟨ha i, by simp⟩, C, hC, hb⟩
  obtain ⟨a, ha, C, hC, hb⟩ := compactTranslateLatticeBound
    (rationalPoints G) π π.representation π.isSmooth I τ (fun _ => 0)
    hlattice S₁ S₂ T hS₁ hS₂ hT φ v
  obtain ⟨d, hd⟩ := CompactLatticePolynomialBound.exists_prod_le_pow_sum a
    (fun i => (ha i).1) hq
  obtain ⟨B₁, hB₁, hb₁⟩ := ρ.exists_rationalMatrixNorm_bound S₁ hS₁
    (hS₁.image continuous_inv)
  obtain ⟨B₂, hB₂, hb₂⟩ := ρ.exists_rationalMatrixNorm_bound S₂ hS₂
    (hS₂.image continuous_inv)
  obtain ⟨B₃, hB₃, hb₃⟩ := ρ.exists_rationalMatrixNorm_bound T hT.isCompact
    (hT.isCompact.image continuous_inv)
  let B := B₁ * B₂ * B₃
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨D * d, C * (A * B ^ D) ^ d, by positivity, ?_⟩
  intro m k₁ hk₁ t ht k₂ hk₂
  let g := k₁ * τ m * t * k₂
  have hn : ∀ g : rationalPoints G, 0 ≤ rationalMatrixNorm F ρ g :=
    fun g => zero_le_one.trans (one_le_rationalMatrixNorm F ρ g)
  have hτ : rationalMatrixNorm F ρ (τ m) ≤ B * rationalMatrixNorm F ρ g := by
    have he : τ m = k₁⁻¹ * g * k₂⁻¹ * t⁻¹ := by dsimp [g]; group
    calc
      rationalMatrixNorm F ρ (τ m) =
          rationalMatrixNorm F ρ (k₁⁻¹ * g * k₂⁻¹ * t⁻¹) := by rw [← he]
      _ ≤ ((rationalMatrixNorm F ρ k₁⁻¹ * rationalMatrixNorm F ρ g) *
          rationalMatrixNorm F ρ k₂⁻¹) * rationalMatrixNorm F ρ t⁻¹ := by
        exact (rationalMatrixNorm_mul_le F ρ _ _).trans
          (mul_le_mul_of_nonneg_right
            ((rationalMatrixNorm_mul_le F ρ _ _).trans
              (mul_le_mul_of_nonneg_right (rationalMatrixNorm_mul_le F ρ _ _)
                (hn _))) (hn _))
      _ ≤ ((B₁ * rationalMatrixNorm F ρ g) * B₂) * B₃ := by
        simp only [rationalMatrixNorm_inv]
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (hb₁ k₁ hk₁) (hn g)
          · exact hb₂ k₂ hk₂
          · exact hn _
          · exact mul_nonneg (zero_le_one.trans hB₁) (hn g)
        · exact hb₃ t ht
        · exact hn _
        · exact mul_nonneg (mul_nonneg (zero_le_one.trans hB₁) (hn g))
            (zero_le_one.trans hB₂)
      _ = B * rationalMatrixNorm F ρ g := by dsimp [B]; ring
  have hcoordinate : q ^ (∑ i, m i) ≤
      (A * B ^ D) * rationalMatrixNorm F ρ g ^ D := by
    calc
      _ ≤ A * rationalMatrixNorm F ρ (τ m) ^ D := hheight m
      _ ≤ A * (B * rationalMatrixNorm F ρ g) ^ D :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hn _) hτ D) hA.le
      _ = _ := by rw [mul_pow]; ring
  calc
    ‖(φ : Module.Dual ℂ π) (π.representation g v)‖ ≤ C * ∏ i, a i ^ m i :=
      hb m k₁ hk₁ t ht k₂ hk₂
    _ ≤ C * (q ^ (∑ i, m i)) ^ d := mul_le_mul_of_nonneg_left (hd m) hC.le
    _ ≤ C * ((A * B ^ D) * rationalMatrixNorm F ρ g ^ D) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (pow_nonneg (by linarith) _) hcoordinate d) hC.le
    _ = (C * (A * B ^ D) ^ d) * rationalMatrixNorm F ρ g ^ (D * d) := by
      rw [mul_pow, ← pow_mul]; ring


/-- The exact first-power-height statement follows by taking D = 1. -/
theorem rationalCompactLatticePolynomialBound :
    RationalCompactLatticePolynomialBoundStatement.{u, uV, uI} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro n _ _ _ ρ π I _ τ hcoeff hheight
  apply rationalCompactLatticePolynomialBound_of_power_height F G hG n ρ π I τ hcoeff
  obtain ⟨q, A, hq, hA, hb⟩ := hheight
  exact ⟨q, A, 1, hq, hA, by simpa only [pow_one] using hb⟩

end Langlands.Plancherel
