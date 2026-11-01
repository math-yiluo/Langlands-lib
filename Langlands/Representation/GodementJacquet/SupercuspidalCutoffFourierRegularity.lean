import Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourier
import Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof
import Langlands.Group.GL.MirabolicOppositeIntersection
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.HarmonicAnalysis.PadicLatticeGeometryProof
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Fourier regularity of actual supercuspidal coefficient cutoffs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open GeneralLinear HarmonicAnalysis

universe uF uV

section Geometry

variable {K : Type uF} [Field K] {m : ℕ} (hm : 0 < m)

private theorem binary_radical_inverseTranspose_head
    {u : GeneralLinear (m + 1) K}
    (hu : u ∈ (BlockShape.binary m 1 hm Nat.one_pos).unipotentSubgroup K)
    (i : Fin m) (j : Fin (m + 1)) :
    inverseTranspose (m + 1) K u i.castSucc j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i.castSucc j := by
  classical
  let B := BlockShape.binary m 1 hm Nat.one_pos
  have h := (B.mem_unipotentSubgroup_iff K (u⁻¹)).mp
    ((B.unipotentSubgroup K).inv_mem hu)
  have hfirst (k : Fin m) : B.index (0 : Fin 2) k = k.castSucc :=
    BlockShape.binary_index_zero m 1 hm Nat.one_pos k
  have hlast : B.index (1 : Fin 2) (0 : Fin 1) = Fin.last m :=
    BlockShape.binary_index_one m 1 hm Nat.one_pos 0
  rw [inverseTranspose_entry]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hz := (B.mem_parabolic_iff K _).mp h.1
      (1 : Fin 2) (0 : Fin 2) (0 : Fin 1) i
        (show (0 : Fin 2) < 1 from by decide)
    rw [hlast, hfirst] at hz
    simpa only [Matrix.one_apply, Fin.castSucc_ne_last, ite_false] using hz
  · have he := h.2 (0 : Fin 2) j i
    rw [hfirst, hfirst] at he
    simpa only [Matrix.one_apply, Fin.castSucc_inj,
      eq_comm (a := j) (b := i)] using he

private theorem mul_inverseTranspose_binary_radical
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : ∀ i, M i (Fin.last m) = 0)
    {u : GeneralLinear (m + 1) K}
    (hu : u ∈ (BlockShape.binary m 1 hm Nat.one_pos).unipotentSubgroup K) :
    M * (inverseTranspose (m + 1) K u).val = M := by
  classical
  calc
    M * (inverseTranspose (m + 1) K u).val = M * 1 := by
      ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, hM i, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro k _
      rw [binary_radical_inverseTranspose_head hm hu]
    _ = M := Matrix.mul_one M

include hm in
/-- Every singular matrix of dimension at least two admits a proper conjugate block
radical fixing it under the right inverse-transpose action. -/
theorem exists_singular_inverseTranspose_stabilizer
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hA : ¬ IsUnit A) :
    ∃ (B : BlockShape (m + 1)) (c : GeneralLinear (m + 1) K),
      B.parabolic K ≠ ⊤ ∧
        ∀ g ∈ B.conjugateUnipotent c,
          A * (inverseTranspose (m + 1) K g).val = A := by
  classical
  have hdet : A.det = 0 := by
    by_contra h
    exact hA ((Matrix.isUnit_iff_isUnit_det A).mpr (Ne.isUnit h))
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨h, hh⟩ := RankinSelberg.EqualRankFrobenius.exists_lastRow_eq v hv
  let Q := inverseTranspose (m + 1) K (h⁻¹)
  have hrow (k : Fin (m + 1)) : h.val (Fin.last m) k = v k := congrFun hh k
  have hAQ (i : Fin (m + 1)) : (A * Q.val) i (Fin.last m) = 0 := by
    simpa only [Matrix.mul_apply, Q, inverseTranspose_coe, inv_inv,
      Matrix.transpose_apply, hrow, Matrix.mulVec, dotProduct, Pi.zero_apply]
      using congrFun hAv i
  let B := BlockShape.binary m 1 hm Nat.one_pos
  refine ⟨B, inverseTranspose (m + 1) K Q, ?_, ?_⟩
  · intro hB
    have hs : Subsingleton (Fin 2) :=
      CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top B hB
    exact (show (0 : Fin 2) ≠ 1 from by decide) (hs.elim 0 1)
  · rintro g ⟨u, hu, rfl⟩
    change A * (inverseTranspose (m + 1) K
      (inverseTranspose (m + 1) K Q * u * (inverseTranspose (m + 1) K Q)⁻¹)).val = A
    simp only [map_mul, map_inv, inverseTranspose_involutive, Units.val_mul]
    calc
      A * (Q.val * (inverseTranspose (m + 1) K u).val * (Q⁻¹).val) =
          (A * Q.val) * (inverseTranspose (m + 1) K u).val * (Q⁻¹).val := by
            simp only [Matrix.mul_assoc]
      _ = (A * Q.val) * (Q⁻¹).val := by
        rw [mul_inverseTranspose_binary_radical hm _ hAQ hu]
      _ = A := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one]

end Geometry

section Cutoff

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {m : ℕ} (hm : 0 < m)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

include hm

/-- The actual raw Fourier transform of every supercuspidal coefficient cutoff
vanishes at every singular matrix, for the supplied additive Haar measure. -/
theorem supercuspidalCutoffMatrixTest_fourier_singular :
    letI := T.topology
    letI := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
      (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ) (v : V)
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier), ¬ IsUnit A →
      rectangularFourierIntegral ψ ν
        (supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ v) A = 0 := by
  let := T.topology
  let := borel F.Carrier
  intro ψ ν ρ hρ ℓ hℓ v A hA
  obtain ⟨B, c, hB, hstab⟩ := exists_singular_inverseTranspose_stabilizer hm A hA
  exact supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer T (Nat.succ_pos m)
    ψ ν ρ hρ ℓ hℓ (B.conjugateUnipotent c) (hρ.2 B hB c)
    (fun g hg => determinantNorm_eq_one_of_mem_conjugateUnipotent T B c hg)
    A hstab v

/-- With the supplied scalar self-dual measure, every actual coefficient cutoff
belongs to the support-defined Fourier-regular matrix test space. -/
theorem supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := (padicLatticeGeometry F T).1
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
      (hsd : IsSelfDual ψ ν)
      (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
      (hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (hℓ : IsSmoothVector ρ.dual ℓ) (v : V),
      supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ v ∈
        fourierRegularMatrixTests (m + 1) ψ ν hsd := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := (padicLatticeGeometry F T).1
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν hsd ρ hρ ℓ hℓ v
  refine ⟨?_, ?_⟩
  · exact supercuspidalCutoffMatrixTest_singular T (Nat.succ_pos m) ρ hρ ℓ hℓ v
  · intro A hA
    exact (rectangularFourierEquiv_apply ψ ν (m + 1) (m + 1) hsd
      (supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ v) A).trans
        (supercuspidalCutoffMatrixTest_fourier_singular T hm ψ ν ρ hρ ℓ hℓ v A hA)

/-- The actual coefficient-cutoff map, with its proved Fourier-regular range. -/
def supercuspidalFourierRegularCutoff :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := (padicLatticeGeometry F T).1
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
      (hsd : IsSelfDual ψ ν)
      (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
      (_hρ : IsSupercuspidal ρ) (ℓ : Module.Dual ℂ V)
      (_hℓ : IsSmoothVector ρ.dual ℓ),
      V →ₗ[ℂ] fourierRegularMatrixTests (m + 1) ψ ν hsd := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := (padicLatticeGeometry F T).1
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν hsd ρ hρ ℓ hℓ
  exact (supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ).codRestrict
    (fourierRegularMatrixTests (m + 1) ψ ν hsd)
    (supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests T hm ψ ν hsd ρ hρ ℓ hℓ)

end Cutoff

end Langlands.GodementJacquet
