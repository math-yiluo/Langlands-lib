import Langlands.Sheaf.Equivariant.Abelian
import Langlands.Sheaf.Equivariant.Godement.Complex
import Langlands.Sheaf.Godement.ExactnessStatement
import Langlands.Cohomology.Flasque.Statement
import Langlands.Cohomology.EquivariantSections

/-!
# Exactness and comparisons of the equivariant Godement complex

These proposition definitions concern the published degree-zero equivariant
Godement functor of stalk families and the published equivariant Godement
cokernel complex. Exactness, the comparison with the ordinary Godement complex
and the computation of derived section representations are conclusions; none
is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.EquivariantGodement

universe u

open Langlands.Sheaf.Equivariant

variable (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
variable [ContinuousConstSMul G X]

/-- Forgetting equivariance is additive: morphisms are added on each open. -/
instance toSheaf_additive : (toSheaf G X (ModuleCat.{u} R)).Additive where
  map_add := rfl

/-- The augmentation chain map from a sheaf, placed in degree zero, to the
published equivariant Godement complex. -/
abbrev augmentationMap (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (CochainComplex.single₀ (TopologicalSheaf G X (ModuleCat.{u} R))).obj F ⟶
      (Sheaf.Equivariant.Godement.complexFunctor R G X).obj F :=
  CokernelComplex.augmentationMap (Sheaf.Equivariant.Godement.zeroFunctor R G X)
    (Sheaf.Equivariant.Godement.coaugmentation R G X) F

end Langlands.Cohomology.EquivariantGodement

namespace Langlands.Cohomology

universe u

open Langlands.Sheaf.Equivariant

/-- The degree-zero equivariant Godement functor is exact on equivariant module
sheaves. -/
def EquivariantGodementZeroExactStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X],
    PreservesFiniteLimits (Sheaf.Equivariant.Godement.zeroFunctor R G X) ∧
    PreservesFiniteColimits (Sheaf.Equivariant.Godement.zeroFunctor R G X)

/-- After forgetting equivariance, the equivariant Godement complex is
naturally isomorphic to the ordinary Godement complex built from all points of
the space, by an isomorphism compatible with the two augmentations. -/
def EquivariantGodementUnderlyingStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X],
    ∃ e : Sheaf.Equivariant.Godement.complexFunctor R G X ⋙
          (toSheaf G X (ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up ℕ) ≅
        toSheaf G X (ModuleCat.{u} R) ⋙
          Sheaf.Godement.complexFunctor (Flasque.spacePoints (TopCat.of X)) (ModuleCat.{u} R),
      ∀ F : TopologicalSheaf G X (ModuleCat.{u} R),
        (toSheaf G X (ModuleCat.{u} R)).map
            ((Sheaf.Equivariant.Godement.coaugmentation R G X).app F) ≫ (e.hom.app F).f 0 =
          Sheaf.Godement.augmentation (Flasque.spacePoints (TopCat.of X)) (ModuleCat.{u} R)
            ((toSheaf G X (ModuleCat.{u} R)).obj F)

/-- The equivariant Godement complex computes the right-derived functors of
the section representation and of the compactly supported section
representation. The comparison map to an injective resolution is any chain map
under the augmentations. -/
def EquivariantGodementComputesSectionsStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X]
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) (I : InjectiveResolution F)
    (φ : (Sheaf.Equivariant.Godement.complexFunctor R G X).obj F ⟶ I.cocomplex),
    EquivariantGodement.augmentationMap R G X F ≫ φ = I.ι →
    ∀ n : ℕ,
      IsIso
        (((sectionRepresentation R G X).mapHomologicalComplex _ ⋙
            HomologicalComplex.homologyFunctor _ _ n).map φ ≫
          (I.isoRightDerivedObj (sectionRepresentation R G X) n).inv) ∧
      IsIso
        (((CompactSections.functor R G X).mapHomologicalComplex _ ⋙
            HomologicalComplex.homologyFunctor _ _ n).map φ ≫
          (I.isoRightDerivedObj (CompactSections.functor R G X) n).inv)

/-- The exactness and comparison family for the equivariant Godement complex.
No component is assumed to define the conjunction. -/
def EquivariantGodementStatements : Prop :=
  EquivariantGodementZeroExactStatement.{u} ∧
  EquivariantGodementUnderlyingStatement.{u} ∧
  EquivariantGodementComputesSectionsStatement.{u}

end Langlands.Cohomology
