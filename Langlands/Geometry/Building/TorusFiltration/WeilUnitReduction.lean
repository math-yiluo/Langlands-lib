import Langlands.BruhatTits.IntegralModels.WeilCongruenceModel
import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.Rational.ParabolicWhiteheadIsomorphism
import Langlands.Algebra.IdealTensorRelation

/-! # Reduction of Weil restriction unit coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 180000

namespace Langlands.GroupScheme.WeilGm

variable (A : Type u) [CommRing A] [IsLocalRing A] (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

local notation "k" => IsLocalRing.ResidueField A
local notation "G" => groupScheme (CommRingCat.of A) B

/-- Points of the special fibre of a Weil restriction in residue unit coordinates. -/
def residueUnitsEquiv :
    rationalPoints ((GroupScheme.baseChange (IntegralModel.residueBaseMap A)).obj G) ≃*
      (k ⊗[A] B)ˣ :=
  (rationalPoints.mapEquiv (algebraBaseChangeIso (CommRingCat.of A) (CommRingCat.of k) B)).trans
    (sectionUnitsEquiv (CommRingCat.of k) (k ⊗[A] B))

set_option maxHeartbeats 1300000 in
/-- Restricting a section to the residue field tensors its unit coordinate with one. -/
theorem residueUnitsEquiv_section (x : rationalPoints G) :
    (residueUnitsEquiv A B (baseChangeSectionHom (IntegralModel.residueBaseMap A) G x) :
      k ⊗[A] B) = 1 ⊗ₜ (sectionUnitsEquiv (CommRingCat.of A) B x : B) := by
  let a := CommRingCat.of A
  let b := CommRingCat.of k
  let T := Over.mk (𝟙 (Spec b))
  let h : (Over.map (baseMap a b)).obj T ⟶ Over.mk (𝟙 (Spec a)) :=
    Over.homMk (baseMap a b) (by simp [T])
  let : Algebra b (restrictedSections a b T) := restrictedSectionsAlgebra a b T
  let : IsScalarTower a b (restrictedSections a b T) := restrictedSectionsScalarTower a b T
  change sectionTensorEquiv b (k ⊗[A] B) (pointsEquiv b (k ⊗[A] B) T
      (baseChangeSectionHom (baseMap a b) G x ≫ (algebraBaseChangeIso a b B).hom.hom.hom)) =
    1 ⊗ₜ sectionTensorEquiv a B (pointsEquiv a B (Over.mk (𝟙 (Spec a))) x)
  rw [algebraBaseChangeIso_hom_points a b B T,
    baseChangePointsEquiv_baseChangeSectionHom, pointsEquiv_naturality]
  suffices hTensor : ∀ z : B ⊗[a] ((algΓ a).obj (Over.mk (𝟙 (Spec a)))).unop,
      sectionTensorEquiv b (k ⊗[A] B)
        (baseChangeTensorEquiv a b B (restrictedSections a b T)
          (Algebra.TensorProduct.lTensor (S := B) B ((algΓ a).map h).unop.hom z)) =
        (1 : k) ⊗ₜ[A] sectionTensorEquiv a B z by
    exact hTensor _
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c r =>
      simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
        baseChangeTensorEquiv_tmul, sectionTensorEquiv_tmul]
      have hnat := ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A k))) r
      change (Scheme.ΓSpecIso b).hom ((baseMap a b).appTop r) =
        algebraMap A k ((Scheme.ΓSpecIso a).hom r) at hnat
      change (Scheme.ΓSpecIso b).hom ((baseMap a b).appTop r) • ((1 : k) ⊗ₜ[A] c) = _
      rw [hnat, TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]
  | add z z' hz hz' =>
      simp only [map_add, TensorProduct.tmul_add, hz, hz']

set_option maxHeartbeats 900000 in
/-- A section reduces to the identity exactly when its unit coordinate differs
from one by the maximal ideal extended to the coefficient algebra. -/
theorem residueSection_eq_one_iff (x : rationalPoints G) :
    baseChangeSectionHom (IntegralModel.residueBaseMap A) G x = 1 ↔
      (sectionUnitsEquiv (CommRingCat.of A) B x : B) - 1 ∈
        (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
  rw [← (residueUnitsEquiv A B).injective.eq_iff, map_one, ← Units.val_inj]
  rw [residueUnitsEquiv_section, Units.val_one, ← sub_eq_zero]
  change ((1 : k) ⊗ₜ[A] (sectionUnitsEquiv (CommRingCat.of A) B x : B)) -
      ((1 : k) ⊗ₜ[A] (1 : B)) = 0 ↔ _
  rw [← TensorProduct.tmul_sub,
    Langlands.Algebra.IdealTensorRelation.one_tmul_eq_zero_iff,
    Ideal.smul_top_eq_map]
  rfl

end Langlands.GroupScheme.WeilGm

namespace Langlands.BruhatTits.IntegralModels.WeilCongruence

open Langlands.GroupScheme

section Pairs

variable (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  {C : Type u} [CommRing C] [Algebra A C] [Module.Finite A C] [Module.Free A C]
  (J : Ideal C)

local notation "D" => pairs A J
local notation "S" => Spec (CommRingCat.of A)
local notation "ι" => GroupScheme.kernelι (quotient A J)

/-- The section's unit coordinate in the coefficient algebra of pairs. -/
def sectionUnit (x : rationalPoints (group A J)) : (D)ˣ :=
  WeilGm.sectionUnitsEquiv (CommRingCat.of A) D (rationalPoints.map ι x)

set_option maxHeartbeats 800000 in
theorem first_sectionUnit (x : rationalPoints (group A J)) : first A J (sectionUnit A J x) = 1 := by
  have h := (GroupScheme.kernelPointsEquiv (quotient A J) (Over.mk (𝟙 S)) x).property
  change rationalPoints.map (quotient A J) (rationalPoints.map ι x) = 1 at h
  have hu := coefficientMap_sectionUnits (first A J) (rationalPoints.map ι x)
  rw [show coefficientMap (first A J) = quotient A J from rfl, h, map_one] at hu
  exact (congrArg Units.val hu).symm

set_option maxHeartbeats 1000000 in
/-- The congruent-unit group reduces to the identity exactly when its pair
differs from one by the maximal ideal of the base. -/
theorem reduction_eq_one_iff [IsLocalRing A] (x : rationalPoints (group A J)) :
    baseChangeSectionHom (IntegralModel.residueBaseMap A) (group A J) x = 1 ↔
      (sectionUnit A J x : D) - 1 ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A D) := by
  let p := IntegralModel.residueBaseMap A
  let i := (GroupScheme.baseChange p).map ι
  let : Mono (ι).hom.hom := GroupScheme.kernelι_mono (quotient A J)
  let : Mono i.hom.hom := by
    change Mono ((Over.pullback p).map (ι).hom.hom)
    infer_instance
  have hi : Function.Injective (rationalPoints.map i) :=
    fun _ _ h => (cancel_mono i.hom.hom).mp h
  rw [← hi.eq_iff, map_one, rationalPoints.map_apply]
  change baseChangeSectionHom p (group A J) x ≫ ((GroupScheme.baseChange p).map ι).hom.hom =
    1 ↔ _
  rw [← baseChangeSectionHom_naturality p ι x]
  exact WeilGm.residueSection_eq_one_iff A D (rationalPoints.map ι x)

end Pairs

end Langlands.BruhatTits.IntegralModels.WeilCongruence
