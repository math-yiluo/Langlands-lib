import Langlands.BruhatTits.SpecialCompact.SmallSubgroupPredicates
import Langlands.BruhatTits.SpecialCompact.ContractionPredicates
import Langlands.Geometry.Building.CocharacterUniformizer
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.PointTopology

/-!
# The simultaneous basis property on actual standard subgroups

The structural target will apply this property to the shared geometric `K0`.
This module defines no replacement for that compact subgroup or for its
construction from valid KP data.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- The actual opposite standard radical: reverse the positive system and the
simple-root index in the existing choice-free standard subgroup construction. -/
abbrev standardOppositeUnipotentPoints (J : Set (characterLattice S)) :
    Subgroup (rationalPoints G) :=
  standardUnipotentPoints i (-ν) (Neg.neg '' J)

/-- Actual algebraic meaning of a split component compatible with the fixed
maximal split torus. The Levi inclusion represents the standard subgroup on
every test scheme; no compact-subgroup conclusion is included. -/
def IsCompatibleStandardSplitComponent
    (J : Set (characterLattice S))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    (q : A.toGrp ⟶ S.toGrp) : Prop :=
  IsSplitSubtorus q ∧
    ∃ (M : GroupScheme (Spec (CommRingCat.of F))) (j : M ⟶ G)
      (a : A.toGrp ⟶ M),
      (standardLevi i ν J).IsRepresentedBy j ∧
      IsClosedSubgroup j ∧ IsConnectedReductive M ∧
      IsSplitComponent a ∧ a ≫ j = q ≫ i

variable {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- Restriction of actual torus characters along the specified algebraic map. -/
def componentCharacterRestriction (q : A.toGrp ⟶ S.toGrp) :
    characterLattice S →+ characterLattice A :=
  (rationalCharacters.equivCharacterLattice A).toAddMonoidHom.comp
    ((characterRestrict q).comp
      (rationalCharacters.equivCharacterLattice S).symm.toAddMonoidHom)

/-- Renard's `Delta(P_J)`: restrictions of the outside-`J` simple characters.
This is not asserted to be a simple system of a root system. -/
def standardParabolicComponentCharacters
    (J : Set (characterLattice S)) (q : A.toGrp ⟶ S.toGrp) :
    Set (characterLattice A) :=
  componentCharacterRestriction q '' (simpleRelativeRoots i ν \ J)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The image in the actual `G(F)` of the intrinsic common-uniformizer section
of `A(F)`. -/
def standardComponentCA (q : A.toGrp ⟶ S.toGrp) :
    Subgroup (rationalPoints G) :=
  (CocharacterUniformizer.CA F A).map (rationalPoints.map (q ≫ i))

/-- The weak character chamber, mapped by the same algebraic inclusion. -/
def standardComponentCAplus
    (J : Set (characterLattice S)) (q : A.toGrp ⟶ S.toGrp) :
    Set (rationalPoints G) :=
  rationalPoints.map (q ≫ i) ''
    CocharacterUniformizer.CAplus F A
      (standardParabolicComponentCharacters i ν J q)

/-- The strict character chamber, mapped by the same algebraic inclusion. -/
def standardComponentCAstrict
    (J : Set (characterLattice S)) (q : A.toGrp ⟶ S.toGrp) :
    Set (rationalPoints G) :=
  rationalPoints.map (q ≫ i) ''
    CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν J q)

/-- Renard's strict epsilon chamber, with the common uniformizer and without
an additional weak-chamber restriction. -/
def standardComponentCAepsilon
    (J : Set (characterLattice S)) (q : A.toGrp ⟶ S.toGrp) (ε : ℝ) :
    Set (rationalPoints G) :=
  rationalPoints.map (q ≫ i) ''
    CocharacterUniformizer.CAepsilon F A
      (standardParabolicComponentCharacters i ν J q) ε

/-- The ordered-intersection and contraction clauses for one actual standard
parabolic, one specified split component and one subgroup `K`. All topology
is the named canonical rational-point topology and its subgroup topologies. -/
def StandardParabolicBasisMember
    (J : Set (characterLattice S)) (q : A.toGrp ⟶ S.toGrp)
    (K : Subgroup (rationalPoints G)) : Prop :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  HasIwahoriIntersectionDecomposition K
      (standardLeviPoints i ν J)
      (standardUnipotentPoints i ν J)
      (standardOppositeUnipotentPoints i ν J) ∧
    ContractionAndCofinality K
      (standardLeviPoints i ν J)
      (standardUnipotentPoints i ν J)
      (standardOppositeUnipotentPoints i ν J)
      (standardComponentCA i q : Set (rationalPoints G))
      (standardComponentCAplus i ν J q)
      (standardComponentCAstrict i ν J q)
      (standardComponentCAepsilon i ν J q)

/-- Existence of one normal compact-open basis before every actual standard
parabolic. Each parabolic has an actual compatible split component, fixed before
all members of the common basis; its inherited Levi family is literal.

This is a property of the supplied `K0`, not a theorem for arbitrary `K0`.
The structural statements must substitute the shared geometric compact
stabilizer and retain its general existence separately. -/
def SimultaneousStandardBasisAt (K0 : Subgroup (rationalPoints G)) : Prop :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  ∃ B : Set (Subgroup (rationalPoints G)),
    CompactOpenNormalBasis K0 B ∧
      ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
        InheritedCompactOpenNormalBasis K0 (standardLeviPoints i ν J) B ∧
          ∃ (A : CommGroupScheme (Spec (CommRingCat.of F)))
            (q : A.toGrp ⟶ S.toGrp),
            IsCompatibleStandardSplitComponent i ν J A q ∧
              ∀ K ∈ B, StandardParabolicBasisMember i ν J q K

end Langlands.BruhatTits.SpecialCompact
