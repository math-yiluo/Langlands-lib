import Langlands.AbelianScheme.Tate.FieldRationalFaithfulnessStatement
import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityProof
import Langlands.AbelianScheme.Tate.FullSeparation
import Langlands.AbelianScheme.AlgClosedPointDivisibility

/-! # Faithfulness of the actual full rational Tate Hom map over geometric fields -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

/-- A positive natural multiple of every element of `ℚ ⊗[ℤ] M` is a pure tensor `1 ⊗ x`. -/
theorem exists_nsmul_eq_one_tmul {M : Type*} [AddCommGroup M] (v : ℚ ⊗[ℤ] M) :
    ∃ N : ℕ, 0 < N ∧ ∃ x : M, N • v = (1 : ℚ) ⊗ₜ[ℤ] x := by
  induction v using TensorProduct.inductionOn with
  | tmul q x =>
    refine ⟨q.den, q.pos, q.num • x, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℚ]
    change (q.den : ℚ) • (q ⊗ₜ[ℤ] x) = (1 : ℚ) ⊗ₜ[ℤ] (q.num • x)
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, zsmul_eq_mul,
      mul_one, mul_comm, Rat.mul_den_eq_num]
  | add v w hv hw =>
    obtain ⟨N, hN, x, hx⟩ := hv
    obtain ⟨M, hM, y, hy⟩ := hw
    refine ⟨N * M, Nat.mul_pos hN hM, M • x + N • y, ?_⟩
    rw [smul_add, mul_comm N M, mul_smul, hx, mul_comm M N, mul_smul, hy,
      TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul]

variable {Ω : Type u} [Field Ω] {A B : AbelianScheme (Spec (CommRingCat.of Ω))}

/-- If the actual homomorphism `f` induces zero on the full rational Tate modules at
the identity test scheme, it induces zero on the full integral Tate groups. -/
theorem map_eq_zero_of_rationalMap_eq_zero (f : A ⟶ B)
    (hf : rationalMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) f = 0)
    (x : GroupScheme.Tate.Full A.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))) :
    GroupScheme.Tate.map (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True)
      (AbelianScheme.groupHom f) x = 0 := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of Ω)))
  apply GroupScheme.Tate.full_toRational_injective B.toGrp T
  rw [map_zero]
  exact LinearMap.congr_fun hf (GroupScheme.Tate.toRational A.toGrp T (fun _ => True) x)

/-- A zero map on the existing full rational Tate modules kills every actual
geometric torsion level of positive order. -/
theorem levelMap_eq_zero_of_rationalMap_eq_zero [IsAlgClosed Ω] [CharZero Ω] (f : A ⟶ B)
    (hf : rationalMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True) f = 0)
    (n : ℕ) (hn : 0 < n) :
    GroupScheme.Tate.levelMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))
      (AbelianScheme.groupHom f) n = 0 := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of Ω)))
  have hdiv : ∀ k : ℕ, 0 < k → ∀ y : T ⟶ A.toGrp.X, ∃ x, x ^ k = y := fun k hk y =>
    AbelianScheme.algClosedPointDivisibility _ A Ω (𝟙 _) k
      (Nat.cast_ne_zero.mpr hk.ne') y
  let i : GroupScheme.Tate.Index (fun _ => True) := ⟨n, hn, trivial⟩
  apply AddMonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := GroupScheme.Tate.full_evaluation_surjective_of_pow A.toGrp T hdiv i y
  have h := GroupScheme.Tate.evaluation_map T (fun _ => True) (AbelianScheme.groupHom f) i x
  rw [map_eq_zero_of_rationalMap_eq_zero f hf x, map_zero] at h
  exact h.symm

/-- The exact full rational faithfulness target follows from Zariski density of
the actual geometric two-power torsion locus. Density is an explicit premise. -/
theorem fieldRationalFaithfulness_of_twoPowerTorsionDensity
    (hdense : FieldTwoPowerTorsionDensityStatement.{u}) :
    FieldRationalFaithfulnessStatement.{u} := by
  intro Ω _ _ _ A B
  let T := Over.mk (𝟙 (Spec (CommRingCat.of Ω)))
  apply (injective_iff_map_eq_zero (rationalHomMap (A := A) (B := B) T (fun _ => True))).mpr
  intro v hv
  obtain ⟨N, hN, f, hNv⟩ := exists_nsmul_eq_one_tmul v
  have hf : rationalMap T (fun _ => True) f = 0 := by
    have h := congrArg (rationalHomMap (A := A) (B := B) T (fun _ => True)) hNv
    rw [map_nsmul, hv, smul_zero, rationalHomMap_tmul, one_smul] at h
    exact h.symm
  have hf0 : f = 0 := hom_eq_zero_of_dense_twoPowerTorsion (hdense Ω A) f
    (fun n => levelMap_eq_zero_of_rationalMap_eq_zero f hf (2 ^ n) (pow_pos two_pos n))
  have hv0 : N • v = 0 := by rw [hNv, hf0, TensorProduct.tmul_zero]
  rw [← Nat.cast_smul_eq_nsmul ℚ] at hv0
  exact (smul_eq_zero.mp hv0).resolve_left (Nat.cast_ne_zero.mpr hN.ne')

/-- The existing full rational Tate Hom map is injective for actual abelian schemes over
every algebraically closed characteristic-zero field. -/
theorem fieldRationalFaithfulness : FieldRationalFaithfulnessStatement.{u} :=
  fieldRationalFaithfulness_of_twoPowerTorsionDensity fieldTwoPowerTorsionDensity.{u}

end Langlands.AbelianScheme.Tate
