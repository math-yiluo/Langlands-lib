import Langlands.AbelianScheme.Tate.FieldPrimeRationalFaithfulnessStatement
import Langlands.AbelianScheme.Tate.PrimePowerTorsionDensity
import Langlands.AbelianScheme.Tate.FieldRationalFaithfulnessProof
import Langlands.AbelianScheme.Tate.PrimeAdicSeparation

/-! # Faithfulness of the actual rational Tate action at every prime -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

namespace PrimeAdic

variable {Ω : Type u} [Field Ω] {A B : AbelianScheme (Spec (CommRingCat.of Ω))}
  (p : ℕ) [Fact p.Prime]

/-- A zero rational prime Tate operator gives a zero integral prime Tate operator. -/
theorem map_eq_zero_of_rationalMap_eq_zero (f : A ⟶ B)
    (hf : rationalMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p f = 0)
    (x : Integral A (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p) :
    map (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p f x = 0 := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of Ω)))
  apply GroupScheme.Tate.PrimeAdic.toRational_injective B.toGrp T p
  rw [map_zero]
  exact LinearMap.congr_fun hf (toRational A T p x)

/-- A zero rational prime Tate operator kills every actual prime-power torsion level. -/
theorem levelMap_eq_zero_of_rationalMap_eq_zero [IsAlgClosed Ω] [CharZero Ω]
    (f : A ⟶ B)
    (hf : rationalMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p f = 0)
    (n : ℕ) :
    GroupScheme.Tate.levelMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))
      (AbelianScheme.groupHom f) (p ^ n) = 0 := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of Ω)))
  have hdiv : ∀ y : T ⟶ A.toGrp.X, ∃ x, x ^ p = y := fun y =>
    AbelianScheme.algClosedPointDivisibility _ A Ω (𝟙 _) p
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) y
  apply AddMonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ :=
    GroupScheme.Tate.PrimeAdic.evaluation_surjective_of_pow A.toGrp T p hdiv n y
  have h := GroupScheme.Tate.PrimeAdic.evaluation_map T p
    (AbelianScheme.groupHom f) n x
  rw [map_eq_zero_of_rationalMap_eq_zero p f hf x, map_zero] at h
  exact h.symm

end PrimeAdic

/-- The existing rational Tate Hom map at each prime is injective for actual
abelian schemes over every algebraically closed characteristic-zero field. -/
theorem fieldPrimeRationalFaithfulness : FieldPrimeRationalFaithfulnessStatement.{u} := by
  intro Ω _ _ _ A B p _
  let T := Over.mk (𝟙 (Spec (CommRingCat.of Ω)))
  apply (injective_iff_map_eq_zero
    (PrimeAdic.rationalHomMap (A := A) (B := B) T p)).mpr
  intro v hv
  obtain ⟨N, hN, f, hNv⟩ := exists_nsmul_eq_one_tmul v
  have hf : PrimeAdic.rationalMap T p f = 0 := by
    have h := congrArg (PrimeAdic.rationalHomMap (A := A) (B := B) T p) hNv
    rw [map_nsmul, hv, smul_zero, PrimeAdic.rationalHomMap_tmul, one_smul] at h
    exact h.symm
  have hf0 : f = 0 := PrimePowerTorsion.hom_eq_zero_of_dense_locus p
    (PrimePowerTorsion.dense_locus A p) f
    (PrimeAdic.levelMap_eq_zero_of_rationalMap_eq_zero p f hf)
  have hv0 : N • v = 0 := by
    rw [hNv, hf0, TensorProduct.tmul_zero]
  rw [← Nat.cast_smul_eq_nsmul ℚ] at hv0
  exact (smul_eq_zero.mp hv0).resolve_left (Nat.cast_ne_zero.mpr hN.ne')

end Langlands.AbelianScheme.Tate
