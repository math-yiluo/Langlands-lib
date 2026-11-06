import Langlands.AlgebraicGeometry.Picard.ArtinianPicardSourceStep

/-! # An actual compatible tower of pointed Picard source quotients -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceTower

open Langlands.AlgebraicGeometry.Deformation
open ArtinianPicardSourceStep

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [Flat f] [IsProper f] (s₀ : Stage ε f M)

/-- Iterate the actual successor construction from the supplied pointed stage. -/
def stage : ℕ → Stage ε f M :=
  Nat.rec s₀ (fun _ s => s.next ε hε f M)

@[simp] lemma stage_zero : stage ε hε f M s₀ 0 = s₀ := rfl

@[simp] lemma stage_succ (n : ℕ) :
    stage ε hε f M s₀ (n + 1) = (stage ε hε f M s₀ n).next ε hε f M := rfl

/-- The actual augmented Artinian test at a tower stage. -/
abbrev test (n : ℕ) : ArtinianTest k K := (stage ε hε f M s₀ n).test

/-- Every tower test retains a surjective cover from the same original source. -/
abbrev cover (n : ℕ) : R →ₐ[k] (test ε hε f M s₀ n).algebra :=
  (stage ε hε f M s₀ n).cover

lemma cover_surjective (n : ℕ) : Function.Surjective (cover ε hε f M s₀ n) :=
  (stage ε hε f M s₀ n).cover_surjective

lemma augmentation_cover (n : ℕ) :
    (test ε hε f M s₀ n).augmentation.comp (cover ε hε f M s₀ n) = ε :=
  (stage ε hε f M s₀ n).augmentation_cover

/-- The actual pointed line bundle at every stage of the tower. -/
abbrev family (n : ℕ) : ArtinianTestDeformations.Deformations f M (test ε hε f M s₀ n) :=
  (stage ε hε f M s₀ n).family

/-- The actual elementary test reduction between consecutive stages. -/
abbrev step (n : ℕ) : test ε hε f M s₀ (n + 1) ⟶ test ε hε f M s₀ n :=
  (stage ε hε f M s₀ n).reduction ε hε f M

lemma step_elementary (n : ℕ) : ArtinianTest.IsElementarySurjection (step ε hε f M s₀ n) :=
  (stage ε hε f M s₀ n).reduction_elementary ε hε f M

lemma step_cover (n : ℕ) :
    (ArtinianTest.toAlgHom (step ε hε f M s₀ n)).comp (cover ε hε f M s₀ (n + 1)) =
      cover ε hε f M s₀ n :=
  (stage ε hε f M s₀ n).reduction_cover ε hε f M

/-- The actual pointed transition of stage n; stage_succ identifies its source with stage n+1. -/
def transition (n : ℕ) :=
  (stage ε hε f M s₀ n).transition ε hε f M

/-- The genuine kernel of the fixed-source cover at a tower stage. -/
abbrev equations (n : ℕ) : Ideal R := (stage ε hε f M s₀ n).equations ε f M

lemma equations_succ_le (n : ℕ) :
    equations ε hε f M s₀ (n + 1) ≤ equations ε hε f M s₀ n :=
  (stage ε hε f M s₀ n).next_equations_le ε hε f M

lemma maximalIdeal_mul_equations_le (n : ℕ) :
    IsLocalRing.maximalIdeal R * equations ε hε f M s₀ n ≤
      equations ε hε f M s₀ (n + 1) :=
  (stage ε hε f M s₀ n).maximalIdeal_mul_equations_le ε hε f M

lemma equations_antitone : Antitone (equations ε hε f M s₀) :=
  antitone_nat_of_succ_le (equations_succ_le ε hε f M s₀)

/-- Every original equation times the n-th maximal-ideal power is a stage-n equation. -/
lemma maximalIdeal_pow_mul_equations_le (n : ℕ) :
    IsLocalRing.maximalIdeal R ^ n * s₀.equations ε f M ≤ equations ε hε f M s₀ n := by
  induction n with
  | zero => simpa only [equations, stage_zero, pow_zero, one_mul] using le_refl (s₀.equations ε f M)
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact (mul_le_mul' le_rfl ih).trans (maximalIdeal_mul_equations_le ε hε f M s₀ n)

/-- Any initial maximal-ideal bound advances along the entire actual tower. -/
lemma maximalIdeal_pow_le (a : ℕ)
    (ha : IsLocalRing.maximalIdeal R ^ a ≤ s₀.equations ε f M) (n : ℕ) :
    IsLocalRing.maximalIdeal R ^ (n + a) ≤ equations ε hε f M s₀ n := by
  rw [pow_add]
  exact (mul_le_mul' le_rfl ha).trans
    (maximalIdeal_pow_mul_equations_le ε hε f M s₀ n)

/-- The actual ideal of all fixed-source equations that hold at every tower stage. -/
def limitingEquations : Ideal R := ⨅ n, equations ε hε f M s₀ n

lemma limitingEquations_le (n : ℕ) :
    limitingEquations ε hε f M s₀ ≤ equations ε hε f M s₀ n :=
  iInf_le _ n

lemma limitingEquations_le_augmentation :
    limitingEquations ε hε f M s₀ ≤ RingHom.ker ε.toRingHom :=
  (limitingEquations_le ε hε f M s₀ 0).trans
    (ElementarySourceExtension.equations_le_augmentation ε s₀.test s₀.cover s₀.augmentation_cover)

/-- The actual quotient source ring determined by the entire tower. -/
abbrev limitRing := R ⧸ limitingEquations ε hε f M s₀

/-- The original augmentation descends to the actual quotient source. -/
def limitAugmentation : limitRing ε hε f M s₀ →ₐ[k] K :=
  Ideal.Quotient.liftₐ _ ε (fun _ ha => RingHom.mem_ker.mp
    (limitingEquations_le_augmentation ε hε f M s₀ ha))

lemma limitAugmentation_surjective : Function.Surjective (limitAugmentation ε hε f M s₀) := by
  intro c
  obtain ⟨a, ha⟩ := hε c
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

instance : Nontrivial (limitRing ε hε f M s₀) :=
  (limitAugmentation ε hε f M s₀).toRingHom.domain_nontrivial

instance : IsLocalRing (limitRing ε hε f M s₀) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

instance : IsNoetherianRing (limitRing ε hε f M s₀) :=
  isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The limiting quotient projects onto every original tower test. -/
def projection (n : ℕ) : limitRing ε hε f M s₀ →ₐ[k] (test ε hε f M s₀ n).algebra :=
  Ideal.Quotient.liftₐ _ (cover ε hε f M s₀ n) (fun _ ha => RingHom.mem_ker.mp
    (limitingEquations_le ε hε f M s₀ n ha))

lemma projection_surjective (n : ℕ) : Function.Surjective (projection ε hε f M s₀ n) := by
  intro b
  obtain ⟨a, ha⟩ := cover_surjective ε hε f M s₀ n b
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

lemma projection_step (n : ℕ) :
    (ArtinianTest.toAlgHom (step ε hε f M s₀ n)).comp (projection ε hε f M s₀ (n + 1)) =
      projection ε hε f M s₀ n := by
  apply Ideal.Quotient.algHom_ext
  simp only [projection, AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
  exact step_cover ε hε f M s₀ n

lemma augmentation_projection (n : ℕ) :
    (test ε hε f M s₀ n).augmentation.comp (projection ε hε f M s₀ n) =
      limitAugmentation ε hε f M s₀ := by
  apply Ideal.Quotient.algHom_ext
  simp only [projection, limitAugmentation, AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
  exact augmentation_cover ε hε f M s₀ n

/-- The stage-n projection kernel is the actual image of the stage-n equation ideal. -/
lemma ker_projection (n : ℕ) :
    RingHom.ker (projection ε hε f M s₀ n).toRingHom =
      (equations ε hε f M s₀ n).map
        (Ideal.Quotient.mk (limitingEquations ε hε f M s₀)) := by
  change RingHom.ker (Ideal.Quotient.lift _ (cover ε hε f M s₀ n).toRingHom _) = _
  exact Ideal.ker_quotient_lift _ _

/-- The actual tower projections jointly separate elements of the limiting quotient. -/
lemma iInf_ker_projection :
    (⨅ n, RingHom.ker (projection ε hε f M s₀ n).toRingHom) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (limitingEquations ε hε f M s₀) a = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  refine (Submodule.mem_iInf _).mpr (fun n => ?_)
  have hn := ((Submodule.mem_iInf _).mp hx) n
  change cover ε hε f M s₀ n a = 0 at hn
  exact hn

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceTower
