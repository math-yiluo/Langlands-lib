import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Dynamic.Functoriality
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Product propositions on actual parabolic point carriers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.BruhatTits.Iwasawa

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G : Langlands.GroupScheme (Spec (CommRingCat.of F))}

/-- Both literal set-product orders cover the actual rational-point group. -/
def PointProductEqualities (P K : Subgroup (rationalPoints G)) : Prop :=
  (Set.univ : Set (rationalPoints G)) = (P : Set (rationalPoints G)) * K ∧
    (Set.univ : Set (rationalPoints G)) = (K : Set (rationalPoints G)) * P

/-- Product conclusions for every actual algebraic parabolic inclusion. -/
def AlgebraicParabolicProducts (K : Subgroup (rationalPoints G)) : Prop :=
  ∀ (P : Langlands.GroupScheme (Spec (CommRingCat.of F))) (j : P ⟶ G),
    IsParabolicSubgroup j →
      PointProductEqualities (rationalPoints.map j).range K

/-- Product conclusions for every actual dynamic parabolic. -/
def DynamicParabolicProducts (K : Subgroup (rationalPoints G)) : Prop :=
  ∀ χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G,
    PointProductEqualities
      ((Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) K

/-- Product conclusions for actual algebraic parabolics conjugated by `g`.
The subgroup is the point-map range of the literal conjugated inclusion. -/
def AlgebraicConjugateParabolicProducts (K : Subgroup (rationalPoints G)) : Prop :=
  ∀ (P : Langlands.GroupScheme (Spec (CommRingCat.of F))) (j : P ⟶ G),
    IsParabolicSubgroup j → ∀ g : rationalPoints G,
      PointProductEqualities
        (rationalPoints.map (j ≫ (G.innerIso g).hom)).range K

/-- Product conclusions for dynamic parabolics of the conjugated cocharacter. -/
def DynamicConjugateParabolicProducts (K : Subgroup (rationalPoints G)) : Prop :=
  ∀ (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : rationalPoints G),
    PointProductEqualities
      ((Dynamic.parabolic (χ ≫ (G.innerIso g).hom)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))) K

variable [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Product conclusions for every valid standard index, including the endpoints. -/
def StandardParabolicProducts (K : Subgroup (rationalPoints G)) : Prop :=
  ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
    PointProductEqualities (standardParabolicPoints i ν J) K

/-- Product conclusions for every rational conjugate `g P_J g⁻¹`.
Pullback through the inverse inner automorphism has this orientation. -/
def StandardConjugateParabolicProducts (K : Subgroup (rationalPoints G)) : Prop :=
  ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
    ∀ g : rationalPoints G,
      PointProductEqualities
        (((standardParabolic i ν J).comap (G.innerIso g).inv).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))) K

/-- All actual-parabolic product conclusions with one fixed subgroup `K`.
This defines a conclusion body; it asserts no building or subgroup existence. -/
def ParabolicPointProductFamily (K : Subgroup (rationalPoints G)) : Prop :=
  AlgebraicParabolicProducts K ∧
    DynamicParabolicProducts K ∧
    StandardParabolicProducts i ν K ∧
    AlgebraicConjugateParabolicProducts K ∧
    DynamicConjugateParabolicProducts K ∧
    StandardConjugateParabolicProducts i ν K

end Langlands.BruhatTits.Iwasawa
