import Langlands.GroupScheme.Rational.RootConeGroupSemigroup
import Langlands.GroupScheme.Rational.RootSubgroupTorusRestriction
import Langlands.GroupScheme.Rational.SemigroupBaseChange
import Langlands.Geometry.Building.FiniteRealTorusSpace
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.AutomorphicAction.BaseChangeCompatibility

/-! # Lifting cone-selected groups to a larger split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Real scalar extension of character restriction along a torus homomorphism. -/
def rootConeCharacterRestriction (f : S ⟶ T) :
    RealTorusSpace.Vstar T →ₗ[ℝ] RealTorusSpace.Vstar S :=
  (characterLattice.comapHom (CommGroupScheme.groupHom f)).toIntLinearMap.baseChange ℝ

@[simp] theorem rootConeCharacterRestriction_tmul (f : S ⟶ T)
    (r : ℝ) (χ : characterLattice T) :
    rootConeCharacterRestriction f (r ⊗ₜ[ℤ] χ) = r ⊗ₜ[ℤ] (f ≫ χ) := rfl

/-- Pulling back the cone retains all larger-torus characters with zero restriction. -/
def rootConePreimage (f : S ⟶ T) (C : PointedCone ℝ (RealTorusSpace.Vstar S)) :
    PointedCone ℝ (RealTorusSpace.Vstar T) :=
  C.comap (rootConeCharacterRestriction f)

@[simp] theorem rootConePreimage_inf (f : S ⟶ T)
    (C D : PointedCone ℝ (RealTorusSpace.Vstar S)) :
    rootConePreimage f (C ⊓ D) = rootConePreimage f C ⊓ rootConePreimage f D := rfl

@[simp] theorem rootConeSemigroup_preimage (f : S ⟶ T)
    (C : PointedCone ℝ (RealTorusSpace.Vstar S)) :
    rootConeSemigroup (rootConePreimage f C) =
      RelativeRoot.characterSemigroupPreimage f (rootConeSemigroup C) := by
  ext χ
  rfl

/-- Closed cones pull back to closed cones for the real module topologies. -/
theorem isClosed_rootConePreimage (f : S ⟶ T)
    (C : PointedCone ℝ (RealTorusSpace.Vstar S))
    (hC : @IsClosed _ (moduleTopology ℝ _) (C : Set (RealTorusSpace.Vstar S))) :
    @IsClosed _ (moduleTopology ℝ _)
      (rootConePreimage f C : Set (RealTorusSpace.Vstar T)) := by
  let := moduleTopology ℝ (RealTorusSpace.Vstar S)
  let := moduleTopology ℝ (RealTorusSpace.Vstar T)
  have : ContinuousAdd (RealTorusSpace.Vstar S) :=
    IsModuleTopology.toContinuousAdd ℝ _
  have : ContinuousSMul ℝ (RealTorusSpace.Vstar S) :=
    ModuleTopology.continuousSMul ℝ _
  exact hC.preimage
    (IsModuleTopology.continuous_of_linearMap (rootConeCharacterRestriction f))

namespace RelativeRoot

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- The whole semigroup group for the smaller split torus is the group for the
preimage semigroup of the larger split torus, on all scheme tests. -/
theorem semigroupSubgroup_comp_torusHom
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    (A : AddSubsemigroup (characterLattice S)) :
    semigroupSubgroup (AutomorphicAction.conjugation
        (CommGroupScheme.groupHom f ≫ j)) A =
      semigroupSubgroup (AutomorphicAction.conjugation j)
        (characterSemigroupPreimage f A) := by
  symm
  apply eq_semigroupSubgroup_of_exact_lieImage
    (AutomorphicAction.conjugation (CommGroupScheme.groupHom f ≫ j)) hS A
    (isSmoothConnectedClosed_semigroupSubgroup (AutomorphicAction.conjugation j) hT
      (characterSemigroupPreimage f A))
  · intro U s x hx
    have h := semigroupSubgroup_isStable (AutomorphicAction.conjugation j)
      (characterSemigroupPreimage f A) U (s ≫ (CommGroupScheme.groupHom f).hom.hom) x hx
    simpa only [AutomorphicAction.conjugation_act, Grp.comp_hom_hom, Category.assoc] using h
  · rw [semigroupWeightSpan_comp_torusHom hS hT f j A]
    exact hasLieImage_semigroupSubgroup (AutomorphicAction.conjugation j) hT
      (characterSemigroupPreimage f A)

end RelativeRoot

section FieldExtension

variable {K : Type u} [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (hS : IsSplitTorus S.toGrp)

/-- Real scalar extension of the unchanged character lattice of a split torus. -/
def rootConeCharacterBaseChange :
    RealTorusSpace.Vstar S ≃ₗ[ℝ]
      RealTorusSpace.Vstar ((CommGroupScheme.baseChange b).obj S) :=
  LinearEquiv.baseChange ℤ ℝ _ _
    (characterLattice.baseChangeEquiv b S hS).toIntLinearEquiv

@[simp] theorem rootConeCharacterBaseChange_tmul (r : ℝ) (χ : characterLattice S) :
    rootConeCharacterBaseChange b hS (r ⊗ₜ[ℤ] χ) =
      r ⊗ₜ[ℤ] (characterLattice.baseChange b S χ) := rfl

/-- The original cone expressed in the character space of the extended torus. -/
def rootConeBaseChange (C : PointedCone ℝ (RealTorusSpace.Vstar S)) :
    PointedCone ℝ (RealTorusSpace.Vstar ((CommGroupScheme.baseChange b).obj S)) :=
  C.comap (rootConeCharacterBaseChange b hS).symm.toLinearMap

@[simp] theorem mem_rootConeBaseChange_tmul
    (C : PointedCone ℝ (RealTorusSpace.Vstar S)) (χ : characterLattice S) :
    (1 : ℝ) ⊗ₜ[ℤ] (characterLattice.baseChange b S χ) ∈ rootConeBaseChange b hS C ↔
      (1 : ℝ) ⊗ₜ[ℤ] χ ∈ C := by
  change (rootConeCharacterBaseChange b hS).symm
    ((1 : ℝ) ⊗ₜ[ℤ] (characterLattice.baseChange b S χ)) ∈ C ↔ _
  rw [← rootConeCharacterBaseChange_tmul b hS, LinearEquiv.symm_apply_apply]

@[simp] theorem rootConeBaseChange_inf
    (C D : PointedCone ℝ (RealTorusSpace.Vstar S)) :
    rootConeBaseChange b hS (C ⊓ D) =
      rootConeBaseChange b hS C ⊓ rootConeBaseChange b hS D := rfl

/-- Closedness is preserved by the canonical real character equivalence. -/
theorem isClosed_rootConeBaseChange
    (C : PointedCone ℝ (RealTorusSpace.Vstar S))
    (hC : @IsClosed _ (moduleTopology ℝ _) (C : Set (RealTorusSpace.Vstar S))) :
    @IsClosed _ (moduleTopology ℝ _)
      (rootConeBaseChange b hS C :
        Set (RealTorusSpace.Vstar ((CommGroupScheme.baseChange b).obj S))) := by
  let := moduleTopology ℝ (RealTorusSpace.Vstar S)
  let := moduleTopology ℝ (RealTorusSpace.Vstar ((CommGroupScheme.baseChange b).obj S))
  have : ContinuousAdd (RealTorusSpace.Vstar S) :=
    IsModuleTopology.toContinuousAdd ℝ _
  have : ContinuousSMul ℝ (RealTorusSpace.Vstar S) :=
    ModuleTopology.continuousSMul ℝ _
  exact hC.preimage (IsModuleTopology.continuous_of_linearMap
    (rootConeCharacterBaseChange b hS).symm.toLinearMap)

/-- The integral semigroup of the transported cone is actual character pullback. -/
theorem rootConeSemigroup_baseChange
    (C : PointedCone ℝ (RealTorusSpace.Vstar S)) :
    rootConeSemigroup (rootConeBaseChange b hS C) =
      RelativeRoot.characterSemigroupBaseChange b S (rootConeSemigroup C) := by
  ext ψ
  obtain ⟨χ, rfl⟩ := (hS.characterLattice_baseChange_bijective b S).surjective ψ
  constructor
  · intro hχ
    exact ⟨χ, (mem_rootConeBaseChange_tmul b hS C χ).mp hχ, rfl⟩
  · rintro ⟨χ', hχ', he⟩
    have he' := (hS.characterLattice_baseChange_bijective b S).injective he
    subst χ'
    exact (mem_rootConeBaseChange_tmul b hS C χ).mpr hχ'

end FieldExtension

section GroupFieldExtension

variable {K : Type u} [Field K] [Algebra k K]
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Cone-selected groups commute with every field extension on all test schemes. -/
theorem rootConeSemigroupGroup_baseChange
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (C : PointedCone ℝ (RealTorusSpace.Vstar S)) :
    (RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i)
      (rootConeSemigroup C)).baseChange (algebraBaseMap k K) =
      RelativeRoot.semigroupSubgroup
        (AutomorphicAction.conjugation ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
        (rootConeSemigroup (rootConeBaseChange (algebraBaseMap k K) hS C)) := by
  rw [rootConeSemigroup_baseChange]
  simpa only [AutomorphicAction.baseChange_conjugation] using
    RelativeRoot.semigroupSubgroup_baseChange (K := K)
      (AutomorphicAction.conjugation i) hS (rootConeSemigroup C)

end GroupFieldExtension

end Langlands.GroupScheme
