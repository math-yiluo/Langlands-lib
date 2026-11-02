import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Rational.Characters

/-! # Statements: derived subgroups are annihilated by commutative targets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every homomorphism to a commutative affine finite-type field group after an arbitrary
algebra scalar extension annihilates the actual derived inclusion (Milne 6.19(d)). -/
def DerivedCommutativeAnnihilationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : D ⟶ G),
    IsDerivedSubgroup d →
    ∀ (H : CommGroupScheme (Spec (CommRingCat.of k)))
      [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
      (R : Type u) [CommRing R] [Algebra k R],
      let b := Spec.map (CommRingCat.ofHom (algebraMap k R))
      ∀ f : (GroupScheme.baseChange b).obj G ⟶
          ((CommGroupScheme.baseChange b).obj H).toGrp,
        (GroupScheme.baseChange b).map d ≫ f = 1

/-- Every rational character after an arbitrary algebra scalar extension is zero on the
actual derived inclusion. The zero character takes the identity value on every test scheme. -/
def DerivedCharacterAnnihilationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : D ⟶ G),
    IsDerivedSubgroup d → ∀ (R : Type u) [CommRing R] [Algebra k R],
      let b := Spec.map (CommRingCat.ofHom (algebraMap k R))
      ∀ χ : rationalCharacters ((GroupScheme.baseChange b).obj G),
        characterRestrict ((GroupScheme.baseChange b).map d) χ = 0

/-- The two commutative-annihilation targets, with the character specialization explicit.
These proposition definitions do not assert either target. -/
def DerivedAnnihilationStatement : Prop :=
  DerivedCommutativeAnnihilationStatement.{u} ∧ DerivedCharacterAnnihilationStatement.{u}

end Langlands.GroupScheme
