import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement
import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureInvarianceStatement
import Langlands.AbelianScheme.FieldMultiplicationFiniteEtale
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Invariance of the actual two-power torsion closure -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

variable {K : Type u} [Field K]
  (A : AbelianScheme (Spec (CommRingCat.of K)))

lemma pow_two_section_apply
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    (s ^ (2 : ℕ)).left (default : Spec (CommRingCat.of K)) =
      (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left
        (s.left (default : Spec (CommRingCat.of K))) := by
  have h : s ≫ (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom = s ^ (2 : ℕ) := by
    simpa only [zpow_natCast] using!
      (GroupScheme.points_multiplication A.toGrp (2 : ℤ) _ s)
  rw [← h, Over.comp_left, Scheme.Hom.comp_apply]

/-- Multiplication by two preserves the actual torsion locus. -/
theorem multiplication_two_mapsTo_twoPowerTorsionLocus :
    Set.MapsTo (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left
      (twoPowerTorsionLocus A) (twoPowerTorsionLocus A) := by
  rintro x ⟨n, s, hs, rfl⟩
  refine ⟨n, s ^ (2 : ℕ), ?_, pow_two_section_apply A s⟩
  rw [← pow_mul, Nat.mul_comm 2 (2 ^ n), pow_mul, hs, one_pow]

variable [IsAlgClosed K]

/-- The underlying point of every actual field-valued section is closed. -/
theorem isClosed_point_of_section
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    IsClosed ({s.left (default : Spec (CommRingCat.of K))} : Set A.X.left) := by
  have h := ((pointEquivClosedPoint A.X.hom) ⟨s.left, s.w⟩).property
  change IsClosed {s.left (IsLocalRing.closedPoint K)} at h
  simpa only [pointEquivClosedPoint_apply_coe,
    Subsingleton.elim (IsLocalRing.closedPoint K) (default : Spec (CommRingCat.of K))]
    using h

/-- Inverse images of actual two-power torsion lie in its closure. The argument
uses density of closed points in each actual fibre. -/
theorem preimage_twoPowerTorsionLocus_subset_closure :
    (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left ⁻¹'
      twoPowerTorsionLocus A ⊆ closure (twoPowerTorsionLocus A) := by
  let f := (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom
  have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  rintro x ⟨n, s, hs, hsx⟩
  let F : Set A.X.left := f.left ⁻¹'
    {s.left (default : Spec (CommRingCat.of K))}
  have hF : IsClosed F := (isClosed_point_of_section A s).preimage f.left.continuous
  have hsub : F ∩ closedPoints A.X.left ⊆ twoPowerTorsionLocus A := by
    rintro y ⟨hy, hyc⟩
    let t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X :=
      Over.homMk (pointOfClosedPoint A.X.hom y hyc)
        (pointOfClosedPoint_comp A.X.hom y hyc)
    have hty : t.left (default : Spec (CommRingCat.of K)) = y :=
      pointOfClosedPoint_apply A.X.hom y hyc _
    have ht : t ^ (2 : ℕ) = s := by
      apply Over.OverMorphism.ext
      apply ext_of_apply_closedPoint_eq A.X.hom (t ^ (2 : ℕ)).w s.w
      have he := pow_two_section_apply A t
      rw [hty] at he
      simpa only [Subsingleton.elim (IsLocalRing.closedPoint K)
        (default : Spec (CommRingCat.of K))] using! he.trans hy
    refine ⟨n + 1, t, ?_, ?_⟩
    · rw [pow_succ, Nat.mul_comm (2 ^ n) 2, pow_mul, ht, hs]
    · exact hty
  have hclosure : closure (F ∩ closedPoints A.X.left) = F := by
    rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hF.isLocallyClosed,
      hF.closure_eq]
  apply closure_mono hsub
  rw [hclosure]
  exact hsx.symm

variable [CharZero K]

/-- Multiplication by two maps the actual torsion locus onto itself. -/
theorem image_twoPowerTorsionLocus_multiplication_two :
    (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left ''
      twoPowerTorsionLocus A = twoPowerTorsionLocus A := by
  apply Set.Subset.antisymm
  · exact Set.image_subset_iff.mpr (multiplication_two_mapsTo_twoPowerTorsionLocus A)
  · rintro x ⟨n, s, hs, hsx⟩
    obtain ⟨t, ht⟩ := algClosedPointDivisibility _ A K (𝟙 _) 2
      (by norm_num : (2 : K) ≠ 0) s
    refine ⟨t.left (default : Spec (CommRingCat.of K)), ⟨n + 1, t, ?_, rfl⟩, ?_⟩
    · rw [pow_succ, Nat.mul_comm (2 ^ n) 2, pow_mul, ht, hs]
    · rw [← pow_two_section_apply A t, ht, hsx]

/-- The actual Zariski closure is stable under full inverse image by
multiplication by two. -/
theorem preimage_closure_twoPowerTorsionLocus_multiplication_two :
    (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left ⁻¹'
      closure (twoPowerTorsionLocus A) = closure (twoPowerTorsionLocus A) := by
  let f := (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left
  have : Etale f := multiplication_etale_of_field A 2 (by norm_num)
  rw [f.isOpenMap.preimage_closure_eq_closure_preimage f.continuous]
  apply Set.Subset.antisymm
  · exact (closure_mono (preimage_twoPowerTorsionLocus_subset_closure A)).trans_eq
      closure_closure
  · exact closure_mono (multiplication_two_mapsTo_twoPowerTorsionLocus A)

/-- The actual Zariski closure maps onto itself under multiplication by two. -/
theorem image_closure_twoPowerTorsionLocus_multiplication_two :
    (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left ''
      closure (twoPowerTorsionLocus A) = closure (twoPowerTorsionLocus A) := by
  let f := (GroupScheme.multiplication A.toGrp (2 : ℤ)).hom.hom.left
  have : IsFinite f := multiplication_isFinite_of_ne_zero A 2 (by norm_num)
  rw [← f.isClosedMap.closure_image_eq_of_continuous f.continuous,
    image_twoPowerTorsionLocus_multiplication_two]

/-- Multiplication by two preserves the actual torsion closure under both
full inverse image and image. -/
theorem twoPowerTorsionClosureInvariance :
    TwoPowerTorsionClosureInvarianceStatement.{u} := by
  intro K _ _ _ A
  exact ⟨preimage_closure_twoPowerTorsionLocus_multiplication_two A,
    image_closure_twoPowerTorsionLocus_multiplication_two A⟩

end Langlands.AbelianScheme.Tate
