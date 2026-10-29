import Langlands.AlgebraicGeometry.Modules.EqualCompositePullback
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Faithfully flat descent of line bundles with trivialized pullback -/

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

namespace Langlands.Scheme.Modules

/-- Along an affine faithfully flat morphism, line bundles whose pullbacks have
trivializations with the same comparison scalars on all equal-composite pairs
are isomorphic. -/
def UnitCocycleDescentUniquenessStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (p : X ⟶ Y), IsAffineHom p → Flat p → Surjective p →
    ∀ (L L' : LineBundle Y)
      (α : (Scheme.Modules.pullback p).obj L.obj ≅ SheafOfModules.unit X.ringCatSheaf)
      (α' : (Scheme.Modules.pullback p).obj L'.obj ≅ SheafOfModules.unit X.ringCatSheaf),
      (∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
        structureAutScalar (equalCompositeUnitAut p a b h α) =
          structureAutScalar (equalCompositeUnitAut p a b h α')) →
      Nonempty (L ≅ L')

/-- Along an affine faithfully flat morphism, every family of global units on
all equal-composite pairs that is natural under precomposition and
multiplicative along triples is the comparison-scalar family of a line bundle
with a trivialized pullback. -/
def UnitCocycleDescentEffectiveStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (p : X ⟶ Y), IsAffineHom p → Flat p → Surjective p →
    ∀ (c : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p → Γ(U, ⊤)ˣ),
      (∀ (U V : Scheme.{u}) (q : V ⟶ U) (a b : U ⟶ X) (h : a ≫ p = b ≫ p)
          (h' : (q ≫ a) ≫ p = (q ≫ b) ≫ p),
        c V (q ≫ a) (q ≫ b) h' = Units.map q.appTop.hom.toMonoidHom (c U a b h)) →
      (∀ (U : Scheme.{u}) (a b d : U ⟶ X) (h : a ≫ p = b ≫ p) (h' : b ≫ p = d ≫ p)
          (h'' : a ≫ p = d ≫ p),
        c U a b h * c U b d h' = c U a d h'') →
      ∃ (L : LineBundle Y)
        (α : (Scheme.Modules.pullback p).obj L.obj ≅ SheafOfModules.unit X.ringCatSheaf),
        ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
          structureAutScalar (equalCompositeUnitAut p a b h α) = c U a b h

/-- Uniqueness and effectivity of descent for line bundles with trivialized
pullback along affine faithfully flat morphisms. -/
def UnitCocycleDescentStatements : Prop :=
  UnitCocycleDescentUniquenessStatement.{u} ∧ UnitCocycleDescentEffectiveStatement.{u}

end Langlands.Scheme.Modules
