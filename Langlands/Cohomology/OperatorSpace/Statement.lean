import Langlands.Sheaf.Equivariant.Abelian
import Langlands.Cohomology.EquivariantSections
import Langlands.Cohomology.TopologicalDerivedSections
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Cohomology of spaces with operators

These proposition definitions concern the published category of equivariant
module sheaves for a group acting by continuous operators on a topological
space. Injectivity, flasqueness and every comparison isomorphism are
conclusions; none is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe u

open Langlands.Sheaf.Equivariant TopologicalDerivedSections

/-- Global sections of an injective equivariant sheaf form an injective
representation. -/
def EquivariantInjectiveSectionsStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] (A : TopologicalSheaf G X (ModuleCat.{u} R)),
    Injective A → Injective ((sectionRepresentation R G X).obj A)

/-- The underlying ordinary sheaf of an injective equivariant sheaf is flasque. -/
def EquivariantInjectiveFlasqueStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] (A : TopologicalSheaf G X (ModuleCat.{u} R)),
    Injective A → ((toSheaf G X (ModuleCat.{u} R)).obj A).IsFlasque

/-- The right-derived functors of global sections, with values in
representations, have the ordinary sheaf cohomology as underlying modules.
The natural isomorphisms are the left-exactness identification in degree zero. -/
def EquivariantSectionsDerivedStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X],
    ∃ e : ∀ n : ℕ,
        (sectionRepresentation R G X).rightDerived n ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ≅
          toSheaf G X (ModuleCat.{u} R) ⋙ ordinaryCohomology (TopCat.of X) R n,
      ∀ A : TopologicalSheaf G X (ModuleCat.{u} R),
        (forget₂ (Rep.{u} R G) (ModuleCat.{u} R)).map
            ((sectionRepresentation R G X).toRightDerivedZero.app A) ≫ (e 0).hom.app A =
          (ordinaryCohomologyZeroIso (TopCat.of X) R).inv.app
            ((toSheaf G X (ModuleCat.{u} R)).obj A)

/-- The right-derived functors of compactly supported sections, with values in
representations, have compactly supported cohomology as underlying modules.
The group carries no topology, so this is the discrete-group case. -/
def EquivariantCompactSectionsDerivedStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X],
    ∃ e : ∀ n : ℕ,
        (CompactSections.functor R G X).rightDerived n ⋙
            forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ≅
          toSheaf G X (ModuleCat.{u} R) ⋙ compactCohomology (TopCat.of X) R n,
      ∀ A : TopologicalSheaf G X (ModuleCat.{u} R),
        (forget₂ (Rep.{u} R G) (ModuleCat.{u} R)).map
            ((CompactSections.functor R G X).toRightDerivedZero.app A) ≫ (e 0).hom.app A =
          (compactCohomologyZeroIso (TopCat.of X) R).inv.app
            ((toSheaf G X (ModuleCat.{u} R)).obj A)

/-- If the underlying sheaf has no higher cohomology, the derived functors of
invariant global sections are the group cohomology of the global sections.
The isomorphisms are natural and are the invariant identification in degree zero. -/
def EquivariantAcyclicGroupCohomologyStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X],
    ∃ e : ∀ (A : TopologicalSheaf G X (ModuleCat.{u} R)),
        (∀ q : ℕ, IsZero ((ordinaryCohomology (TopCat.of X) R (q + 1)).obj
          ((toSheaf G X (ModuleCat.{u} R)).obj A))) →
        ∀ n : ℕ,
          ((sectionRepresentation R G X ⋙ Rep.invariantsFunctor R G).rightDerived n).obj A ≅
            groupCohomology ((sectionRepresentation R G X).obj A) n,
      (∀ A hA,
        (sectionRepresentation R G X ⋙ Rep.invariantsFunctor R G).toRightDerivedZero.app A ≫
            (e A hA 0).hom =
          (groupCohomology.H0Iso ((sectionRepresentation R G X).obj A)).inv) ∧
      ∀ (A B : TopologicalSheaf G X (ModuleCat.{u} R)) hA hB (f : A ⟶ B) (n : ℕ),
        ((sectionRepresentation R G X ⋙ Rep.invariantsFunctor R G).rightDerived n).map f ≫
            (e B hB n).hom =
          (e A hA n).hom ≫
            (groupCohomology.functor R G n).map ((sectionRepresentation R G X).map f)

/-- For a finite group whose order is invertible in the coefficients, the
derived functors of invariant global sections are the invariants of the
derived section representations. The isomorphisms are the invariant
identification in degree zero. -/
def FiniteEquivariantSectionsInvariantsStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [Finite G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X],
    IsUnit (Nat.card G : R) →
    ∃ e : ∀ n : ℕ,
        (sectionRepresentation R G X ⋙ Rep.invariantsFunctor R G).rightDerived n ≅
          (sectionRepresentation R G X).rightDerived n ⋙ Rep.invariantsFunctor R G,
      ∀ A : TopologicalSheaf G X (ModuleCat.{u} R),
        (sectionRepresentation R G X ⋙ Rep.invariantsFunctor R G).toRightDerivedZero.app A ≫
            (e 0).hom.app A =
          (Rep.invariantsFunctor R G).map
            ((sectionRepresentation R G X).toRightDerivedZero.app A)

/-- The compactly supported form of the finite-group invariant comparison. -/
def FiniteEquivariantCompactSectionsInvariantsStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [Finite G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X],
    IsUnit (Nat.card G : R) →
    ∃ e : ∀ n : ℕ,
        (CompactSections.functor R G X ⋙ Rep.invariantsFunctor R G).rightDerived n ≅
          (CompactSections.functor R G X).rightDerived n ⋙ Rep.invariantsFunctor R G,
      ∀ A : TopologicalSheaf G X (ModuleCat.{u} R),
        (CompactSections.functor R G X ⋙ Rep.invariantsFunctor R G).toRightDerivedZero.app A ≫
            (e 0).hom.app A =
          (Rep.invariantsFunctor R G).map
            ((CompactSections.functor R G X).toRightDerivedZero.app A)

/-- For a finite group, if the underlying sheaf has no higher compactly
supported cohomology, the derived functors of invariant compactly supported
sections are the group cohomology of the compactly supported sections. The
isomorphisms are natural and are the invariant identification in degree zero.
Finiteness is needed: the translation action of the integers on themselves is
a counterexample for an infinite discrete group. -/
def FiniteEquivariantCompactAcyclicGroupCohomologyStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [Finite G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X],
    ∃ e : ∀ (A : TopologicalSheaf G X (ModuleCat.{u} R)),
        (∀ q : ℕ, IsZero ((compactCohomology (TopCat.of X) R (q + 1)).obj
          ((toSheaf G X (ModuleCat.{u} R)).obj A))) →
        ∀ n : ℕ,
          ((CompactSections.functor R G X ⋙ Rep.invariantsFunctor R G).rightDerived n).obj A ≅
            groupCohomology ((CompactSections.functor R G X).obj A) n,
      (∀ A hA,
        (CompactSections.functor R G X ⋙ Rep.invariantsFunctor R G).toRightDerivedZero.app A ≫
            (e A hA 0).hom =
          (groupCohomology.H0Iso ((CompactSections.functor R G X).obj A)).inv) ∧
      ∀ (A B : TopologicalSheaf G X (ModuleCat.{u} R)) hA hB (f : A ⟶ B) (n : ℕ),
        ((CompactSections.functor R G X ⋙ Rep.invariantsFunctor R G).rightDerived n).map f ≫
            (e B hB n).hom =
          (e A hA n).hom ≫
            (groupCohomology.functor R G n).map ((CompactSections.functor R G X).map f)

/-- The cohomology statements for spaces with operators, taken together. -/
def OperatorSpaceCohomologyStatements : Prop :=
  EquivariantInjectiveSectionsStatement.{u} ∧
    EquivariantInjectiveFlasqueStatement.{u} ∧
    EquivariantSectionsDerivedStatement.{u} ∧
    EquivariantCompactSectionsDerivedStatement.{u} ∧
    EquivariantAcyclicGroupCohomologyStatement.{u} ∧
    FiniteEquivariantSectionsInvariantsStatement.{u} ∧
    FiniteEquivariantCompactSectionsInvariantsStatement.{u} ∧
    FiniteEquivariantCompactAcyclicGroupCohomologyStatement.{u}

end Langlands.Cohomology
