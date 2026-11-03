import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Geometric radicals, rational Levi subgroups, and central subtori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A represented ground-field solvable radical, greatest among smooth connected
solvable normal closed subgroups defined over the ground field. -/
structure IsSolvableRadical {R P : GroupScheme (Spec (CommRingCat.of k))}
    (r : R ⟶ P) : Prop where
  isClosedSubgroup : IsClosedSubgroup r
  smooth : Smooth R.X.hom
  connectedSpace : ConnectedSpace R.X.left
  isSolvableGroupScheme : IsSolvableGroupScheme R
  isNormal : (SubgroupFunctor.range r).IsNormal
  greatest : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ P),
    IsClosedSubgroup h → Smooth H.X.hom → ConnectedSpace H.X.left →
      IsSolvableGroupScheme H → (SubgroupFunctor.range h).IsNormal →
        SubgroupFunctor.range h ≤ SubgroupFunctor.range r

/-- A represented solvable radical whose base change is also the radical over
the algebraic closure. This predicate asserts no existence or descent theorem. -/
def IsGeometricSolvableRadical {R P : GroupScheme (Spec (CommRingCat.of k))}
    (r : R ⟶ P) : Prop :=
  IsSolvableRadical r ∧
    IsSolvableRadical ((GroupScheme.baseChange (toAlgebraicClosure k)).map r)

/-- A represented unipotent radical whose base change is also the radical over
the algebraic closure, using the existing ground-field radical predicate. -/
def LeviSubgroup.IsGeometricUnipotentRadical {U P : GroupScheme (Spec (CommRingCat.of k))}
    (r : U ⟶ P) : Prop :=
  IsUnipotentRadical r ∧
    IsUnipotentRadical ((GroupScheme.baseChange (toAlgebraicClosure k)).map r)

section Multiplication

variable {S : Scheme.{u}} {L U P : GroupScheme S}

/-- The actual multiplication morphism of two subgroup maps, with Levi factor
first. It is a morphism of schemes over the base, without a group-homomorphism claim. -/
def subgroupMultiplication (l : L ⟶ P) (r : U ⟶ P) : L.X ⊗ U.X ⟶ P.X :=
  (fst L.X U.X ≫ l.hom.hom) * (snd L.X U.X ≫ r.hom.hom)

/-- Evaluation of the subgroup multiplication morphism on an arbitrary test scheme. -/
theorem comp_subgroupMultiplication (l : L ⟶ P) (r : U ⟶ P)
    {V : Over S} (x : V ⟶ L.X) (y : V ⟶ U.X) :
    lift x y ≫ subgroupMultiplication l r = (x ≫ l.hom.hom) * (y ≫ r.hom.hom) := by
  simp only [subgroupMultiplication, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

end Multiplication

/-- A rational Levi subgroup is a connected reductive closed subgroup whose
multiplication with a represented geometric unipotent radical is an isomorphism
of schemes over the ground field. -/
structure IsRationalLeviSubgroup {L P : GroupScheme (Spec (CommRingCat.of k))}
    (l : L ⟶ P) : Prop where
  isAffineHom : IsAffineHom P.X.hom
  isClosedSubgroup : IsClosedSubgroup l
  isConnectedReductive : IsConnectedReductive L
  exists_unipotentRadical :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ P),
      LeviSubgroup.IsGeometricUnipotentRadical r ∧ IsIso (subgroupMultiplication l r)

/-- A largest central subtorus, characterized among actual closed central tori
by containment of their images on every test scheme. No representative is chosen. -/
structure IsLargestCentralSubtorus
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    {L : GroupScheme (Spec (CommRingCat.of k))} (z : Z.toGrp ⟶ L) : Prop where
  isTorus : IsTorus Z.toGrp
  isClosedSubgroup : IsClosedSubgroup z
  isCentral : IsCentral z
  greatest : ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ L),
    IsTorus A.toGrp → IsClosedSubgroup a → IsCentral a →
      SubgroupFunctor.range a ≤ SubgroupFunctor.range z

end Langlands.GroupScheme
