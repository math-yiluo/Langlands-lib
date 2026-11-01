import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceSupport
import Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof
import Langlands.Representation.Whittaker.TwoBlockJacquetCovarianceProof

/-! # Uniform rectangular support in a leading diagonal block -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear Whittaker HarmonicAnalysis TwoBlockDeformation TwoBlockConvergence
  TwoBlockLowerFixedSlice

universe uF uV

section Algebra

variable {K : Type uF} [Field K]

/-- The torus of concatenated exponent vectors is the actual block sum. -/
theorem blockSum_torus {a b : ℕ} (ϖ : Kˣ)
    (lam : Fin a → ℤ) (mu : Fin b → ℤ) :
    blockSum (Iwasawa.torus ϖ lam, Iwasawa.torus ϖ mu) =
      Iwasawa.torus ϖ (Fin.append lam mu) := by
  apply Units.ext
  ext i l
  induction i using Fin.addCases <;> induction l using Fin.addCases <;>
    simp [Iwasawa.torus_val, Matrix.diagonal_apply]
  all_goals
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega

/-- An ambient adjacent root bound restricts to the leading diagonal block. -/
theorem rootBounded_append_left {a b L : ℕ}
    {lam : Fin (a + 1) → ℤ} {mu : Fin (b + 1) → ℤ}
    (h : RootBounded (n := a + 1 + b) L
      (Fin.append (m := a + 1) (n := b + 1) lam mu)) : RootBounded L lam := by
  intro i
  have hi : i.val < a + 1 + b := by omega
  have hb := h ⟨i.val, hi⟩
  have hc : (⟨i.val, hi⟩ : Fin (a + 1 + b)).castSucc =
      i.castSucc.castAdd (b + 1) := Fin.ext rfl
  have hs : (⟨i.val, hi⟩ : Fin (a + 1 + b)).succ =
      i.succ.castAdd (b + 1) := Fin.ext rfl
  simpa only [hc, hs, Fin.append_left] using hb

/-- The same ambient bound restricts to the trailing diagonal block. -/
theorem rootBounded_append_right {a b L : ℕ}
    {lam : Fin (a + 1) → ℤ} {mu : Fin (b + 1) → ℤ}
    (h : RootBounded (n := a + 1 + b) L
      (Fin.append (m := a + 1) (n := b + 1) lam mu)) : RootBounded L mu := by
  intro i
  have hi : a + 1 + i.val < a + 1 + b := by omega
  have hb := h ⟨a + 1 + i.val, hi⟩
  have hc : (⟨a + 1 + i.val, hi⟩ : Fin (a + 1 + b)).castSucc =
      i.castSucc.natAdd (a + 1) := Fin.ext rfl
  have hs : (⟨a + 1 + i.val, hi⟩ : Fin (a + 1 + b)).succ =
      i.succ.natAdd (a + 1) := by apply Fin.ext; simp; omega
  simpa only [hc, hs, Fin.append_right] using hb

end Algebra

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- The actual block sum preserves integrality of both matrices and inverses. -/
theorem blockSum_mem_integralOpen {a b : ℕ}
    {A : GeneralLinear (a + 1) F.Carrier}
    {B : GeneralLinear (b + 1) F.Carrier}
    (hA : A ∈ integralOpen F a) (hB : B ∈ integralOpen F b) :
    blockSum (A, B) ∈ integralOpen F (a + 1 + b) := by
  have ha := (mem_integralOpen F A).mp hA
  have hb := (mem_integralOpen F B).mp hB
  apply (mem_integralOpen F _).mpr
  constructor
  · intro i l
    induction i using (Fin.addCases (m := a + 1) (n := b + 1)) <;>
      induction l using (Fin.addCases (m := a + 1) (n := b + 1)) <;>
      simp only [blockSum_apply_left, blockSum_apply_right,
        blockSum_apply_left_right, blockSum_apply_right_left]
    · exact ha.1 _ _
    · exact zero_mem _
    · exact zero_mem _
    · exact hb.1 _ _
  · rw [show (blockSum (A, B))⁻¹ = blockSum (A⁻¹, B⁻¹) by
      simpa using (map_inv blockSum (A, B)).symm]
    intro i l
    induction i using (Fin.addCases (m := a + 1) (n := b + 1)) <;>
      induction l using (Fin.addCases (m := a + 1) (n := b + 1)) <;>
      simp only [blockSum_apply_left, blockSum_apply_right,
        blockSum_apply_left_right, blockSum_apply_right_left]
    · exact ha.2 _ _
    · exact zero_mem _
    · exact zero_mem _
    · exact hb.2 _ _

/-- Nonvanishing of a smooth ambient coefficient gives root bounds in
independent Iwasawa decompositions of both actual diagonal blocks. -/
theorem exists_coefficient_blockSum_rootBounded (ψ : UnitaryAdditiveCharacter F.Carrier)
    {a b : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (a + 1 + (b + 1)) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ (a + 1 + b) π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ L : ℕ, ∀ (A : GeneralLinear (a + 1) F.Carrier)
      (B : GeneralLinear (b + 1) F.Carrier)
      (c : GeneralLinear (a + 1 + (b + 1)) F.Carrier),
      c ∈ integralOpen F (a + 1 + b) →
      W.val.val (blockSum (A, B) * c) ≠ 0 →
      ∃ (uA : GeneralLinear (a + 1) F.Carrier)
        (uB : GeneralLinear (b + 1) F.Carrier)
        (lam : Fin (a + 1) → ℤ) (mu : Fin (b + 1) → ℤ)
        (kA : GeneralLinear (a + 1) F.Carrier)
        (kB : GeneralLinear (b + 1) F.Carrier),
        uA ∈ upperUnipotent (a + 1) F.Carrier ∧
        uB ∈ upperUnipotent (b + 1) F.Carrier ∧
        kA ∈ integralOpen F a ∧ kB ∈ integralOpen F b ∧
        A = uA * Iwasawa.torus
          (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) lam * kA ∧
        B = uB * Iwasawa.torus
          (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) mu * kB ∧
        RootBounded L lam ∧ RootBounded L mu := by
  obtain ⟨L, hL⟩ := exists_coefficient_rootBounded F ψ π hπ ell W
  refine ⟨L, fun A B c hc hW => ?_⟩
  have hϖ := uniformizerUnit_isUniformizingElement F
  obtain ⟨uA, huA, lam, kA, hkA, heA⟩ := Iwasawa.exists_iwasawa hϖ A
  obtain ⟨uB, huB, mu, kB, hkB, heB⟩ := Iwasawa.exists_iwasawa hϖ B
  have hkA' : kA ∈ integralOpen F a :=
    (mem_integralOpen F kA).mpr ((Conductor.mem_integralSubgroup _ _ kA).mp hkA)
  have hkB' : kB ∈ integralOpen F b :=
    (mem_integralOpen F kB).mpr ((Conductor.mem_integralSubgroup _ _ kB).mp hkB)
  have hk : blockSum (kA, kB) * c ∈ integralOpen F (a + 1 + b) :=
    (integralOpen F _).mul_mem (blockSum_mem_integralOpen F hkA' hkB') hc
  have hu := blockSum_mem_upperUnipotent ⟨uA, huA⟩ ⟨uB, huB⟩
  have he : blockSum (A, B) * c =
      blockSum (uA, uB) * Iwasawa.torus
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
          (Fin.append lam mu) * (blockSum (kA, kB) * c) := by
    rw [← blockSum_torus, heA, heB]
    simp only [← mul_assoc, ← map_mul]
    rfl
  have hW' : W.val.val (Iwasawa.torus
      (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData)
        (Fin.append lam mu) * (blockSum (kA, kB) * c)) ≠ 0 := by
    intro hz
    apply hW
    rw [he, mul_assoc, W.val.property ⟨_, hu⟩, hz, mul_zero]
  have hroot := hL (Fin.append (m := a + 1) (n := b + 1) lam mu) _ hk hW'
  exact ⟨uA, uB, lam, mu, kA, kB, huA, huB, hkA', hkB', heA, heB,
    rootBounded_append_left hroot, rootBounded_append_right hroot⟩

/-- Integer adjacent root bounds imply the precise normalized ratio bound. -/
theorem normalizedAbs_ratios_of_rootBounded {a L : ℕ} {lam : Fin (a + 1) → ℤ}
    (h : RootBounded L lam) (i : Fin a) :
    F.canonicalTopologicalData.normalizedAbs
      (((LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData ^ lam i.castSucc) /
        (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData ^ lam i.succ) :
          F.Carrierˣ) : F.Carrier) ≤
      (F.canonicalTopologicalData.residueCardinality : ℝ) ^ L := by
  rw [div_eq_mul_inv, ← zpow_sub, normalizedAbs_uniformizer_zpow F]
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  calc
    _ ≤ (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (L : ℤ) :=
      (zpow_le_zpow_iff_right₀ hq).mpr (by have := h i; omega)
    _ = _ := zpow_natCast _ _

/-- A compact rectangle support set uniform in the leading group coordinate,
the other invertible diagonal block and the right integral factor. -/
def IsBlockSumRectangularSupport (ψ : UnitaryAdditiveCharacter F.Carrier)
    (n j k d : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F.Carrier) V)
    (ell : glFunctionals ψ (n + (j + k + 1) + 1 + d) π)
    (W : (coefficientModel π ell).toSubmodule)
    (C : Set (Matrix (Fin j) (Fin (n + 1)) F.Carrier)) : Prop :=
  IsCompact C ∧ ∀ (g : GeneralLinear (n + 1) F.Carrier)
    (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier)
    (D : GeneralLinear (d + 1) F.Carrier)
    (c : GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F.Carrier),
    c ∈ integralOpen F (n + (j + k + 1) + 1 + d) →
    W.val.val (blockSum (unequalRankMatrix j k g x, D) * c) ≠ 0 →
    x ∈ C

/-- A nonzero smooth ambient coefficient has compact rectangular support in a
leading unequal-rank block, uniformly in the entire other invertible block
and the supplied right integral factor. -/
theorem exists_blockSum_rectangular_support (ψ : UnitaryAdditiveCharacter F.Carrier)
    (n j k d : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ (n + (j + k + 1) + 1 + d) π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ C, IsBlockSumRectangularSupport F ψ n j k d π ell W C := by
  obtain ⟨L, hL⟩ := exists_coefficient_blockSum_rootBounded F ψ π hπ ell W
  have hq : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast (zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one)
  obtain ⟨C, hC, hsupport⟩ :=
    unequalRankIwasawaSupport F F.canonicalTopologicalData n j k
      ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ L) (pow_pos hq L)
  refine ⟨C, hC, fun g x D c hc hW => ?_⟩
  obtain ⟨uA, uB, lam, mu, kA, kB, huA, huB, hkA, hkB, heA, heB, hrA, hrB⟩ :=
    hL (unequalRankMatrix j k g x) D c hc hW
  exact hsupport g x uA
    (fun i => LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData ^ lam i)
    kA huA ((Conductor.mem_integralSubgroup _ _ kA).mpr ((mem_integralOpen F kA).mp hkA))
    heA (normalizedAbs_ratios_of_rootBounded F hrA)

end Langlands.RankinSelberg.TwoBlockDominantRectangular
