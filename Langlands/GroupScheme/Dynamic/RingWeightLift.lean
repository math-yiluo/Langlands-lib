import Langlands.GroupScheme.Dynamic.RingLieProof
import Langlands.GroupScheme.Rational.GenericLieWeights
import Langlands.GroupScheme.Lie.WeightImagePullback
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Weight vectors in represented dynamic subgroups over a ring -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {A : Type u} [CommRing A] [Algebra R A]

/-- The differential image of a represented subgroup is its actual dual-number
membership condition, over any base and any coefficient algebra. -/
theorem mem_range_targetMapLinear_iff {F : SubgroupFunctor G} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) (X : Additive (lieKernel G A)) :
    X ∈ LinearMap.range (targetMapLinear j A) ↔
      X.toMul.val ∈ F.carrier _ := by
  have : Mono j.hom.hom := hj.1
  constructor
  · rintro ⟨Y, rfl⟩
    exact (hj.pointsEquiv _ Y.toMul.val).property
  · intro hX
    let Y := (hj.pointsEquiv _).symm ⟨X.toMul.val, hX⟩
    have hcomp : Y ≫ j.hom.hom = X.toMul.val := hj.pointsEquiv_symm_comp _
    have hY : reduction H Y = 1 := by
      apply (cancel_mono j.hom.hom).mp
      change reduction G (Y ≫ j.hom.hom) = 1 ≫ j.hom.hom
      rw [hcomp, X.toMul.property, MonObj.one_comp]
    refine ⟨Additive.ofMul ⟨Y, hY⟩, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext hcomp

end Lie

namespace Dynamic

variable {R : Type u} [CommRing R]
  {T : CommGroupScheme (Spec (CommRingCat.of R))}
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFinitePresentation G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (χ : characterLattice T)
  {j : H ⟶ G}

/-- A character with trivial restriction lifts through a represented dynamic centralizer. -/
theorem weightSpace_le_range_centralizer_of_comp_eq
    (hj : (centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hχ : ν ≫ χ = Gm.powerHom _ 0) :
    weightSpace i χ ≤ LinearMap.range (Lie.targetMapLinear j (CommRingCat.of R)) := by
  intro X hX
  apply (Lie.mem_range_targetMapLinear_iff hj X).mpr
  apply (dynamicRingLie R G (CommGroupScheme.groupHom ν ≫ i) X.toMul).1.mpr
  have h := weightSpace_le_comp ν i χ hX
  rwa [hχ] at h

/-- A character with positive power restriction lifts through a represented
dynamic contracting subgroup. -/
theorem weightSpace_le_range_unipotent_of_comp_eq
    (hj : (unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (n : ℕ) (hχ : ν ≫ χ = Gm.powerHom _ (n + 1)) :
    weightSpace i χ ≤ LinearMap.range (Lie.targetMapLinear j (CommRingCat.of R)) := by
  intro X hX
  apply (Lie.mem_range_targetMapLinear_iff hj X).mpr
  apply (dynamicRingLie R G (CommGroupScheme.groupHom ν ≫ i) X.toMul).2.2.mpr
  apply Submodule.mem_iSup_of_mem n
  have h := weightSpace_le_comp ν i χ hX
  rwa [hχ] at h

/-- The actual centralizer differential preserves exactly a weight whose
cocharacter restriction is trivial. The torus factor is explicitly supplied. -/
theorem map_weightSpace_centralizer_of_comp_eq
    (hj : (centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hχ : ν ≫ χ = Gm.powerHom _ 0)
    (t : T.toGrp ⟶ H) (ht : t ≫ j = i) :
    (weightSpace t χ).map (Lie.targetMapLinear j (CommRingCat.of R)) =
      weightSpace i χ := by
  have : Mono j.hom.hom := hj.1
  apply le_antisymm
  · rintro X ⟨Y, hY, rfl⟩
    have h := lieKernelHomLinear_mem_weightSpace j t χ hY
    rwa [ht] at h
  · intro X hX
    obtain ⟨Y, hY⟩ := weightSpace_le_range_centralizer_of_comp_eq i ν χ hj hχ hX
    refine ⟨Y, ?_, hY⟩
    apply (lieKernelHomLinear_mem_weightSpace_iff j t χ Y).mp
    rw [ht, hY]
    exact hX

/-- The weight comparison for a represented centralizer over any commutative base. -/
def centralizerWeightSpaceEquivOfCompEq
    (hj : (centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hχ : ν ≫ χ = Gm.powerHom _ 0)
    (t : T.toGrp ⟶ H) (ht : t ≫ j = i) :
    weightSpace t χ ≃ₗ[CommRingCat.of R] weightSpace i χ := by
  have : Mono j.hom.hom := hj.1
  exact (Submodule.equivMapOfInjective (Lie.targetMapLinear j (CommRingCat.of R))
    (Lie.targetMapLinear_injective j _) (weightSpace t χ)).trans
      (LinearEquiv.ofEq _ _ (map_weightSpace_centralizer_of_comp_eq i ν χ hj hχ t ht))

@[simp]
theorem centralizerWeightSpaceEquivOfCompEq_coe
    (hj : (centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hχ : ν ≫ χ = Gm.powerHom _ 0)
    (t : T.toGrp ⟶ H) (ht : t ≫ j = i) (X : weightSpace t χ) :
    (centralizerWeightSpaceEquivOfCompEq i ν χ hj hχ t ht X :
      Additive (lieKernel G (CommRingCat.of R))) =
        Lie.targetMapLinear j (CommRingCat.of R) X := rfl

/-- The unique linear lift of a positive character weight into the actual
Lie module of a represented contracting subgroup. -/
def unipotentWeightLiftOfCompEq
    (hj : (unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (n : ℕ) (hχ : ν ≫ χ = Gm.powerHom _ (n + 1)) :
    weightSpace i χ →ₗ[CommRingCat.of R] Additive (lieKernel H (CommRingCat.of R)) := by
  have : Mono j.hom.hom := hj.1
  exact (weightSpace i χ).subtype.codRestrictOfInjective
    (Lie.targetMapLinear j (CommRingCat.of R)) (Lie.targetMapLinear_injective j _)
      (fun X => weightSpace_le_range_unipotent_of_comp_eq i ν χ hj n hχ X.property)

@[simp]
theorem targetMapLinear_unipotentWeightLiftOfCompEq
    (hj : (unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (n : ℕ) (hχ : ν ≫ χ = Gm.powerHom _ (n + 1)) (X : weightSpace i χ) :
    Lie.targetMapLinear j (CommRingCat.of R)
      (unipotentWeightLiftOfCompEq i ν χ hj n hχ X) = X := by
  simp only [unipotentWeightLiftOfCompEq, LinearMap.codRestrictOfInjective_comp_apply,
    Submodule.subtype_apply]

end Dynamic

end Langlands.GroupScheme
