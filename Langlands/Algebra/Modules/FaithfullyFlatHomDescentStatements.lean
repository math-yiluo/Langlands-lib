import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Descent of compatible module morphisms along faithfully flat maps -/

universe u

open CategoryTheory ModuleCat

namespace Langlands.Algebra.Modules

/-- A morphism between extended modules which commutes with their canonical
coactions descends to a unique morphism over the original ring. -/
def FaithfullyFlatModuleHomDescentStatement : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] (f : A →+* B),
    f.FaithfullyFlat →
      ∀ (M N : ModuleCat.{u} A)
        (g : (extendScalars f).obj M ⟶ (extendScalars f).obj N),
        g ≫ (extendScalars f).map ((extendRestrictScalarsAdj f).unit.app N) =
          (extendScalars f).map ((extendRestrictScalarsAdj f).unit.app M) ≫
            (extendScalars f).map ((restrictScalars f).map g) →
        ∃! h : M ⟶ N, (extendScalars f).map h = g

/-- An isomorphism between extended modules whose forward map commutes with
their canonical coactions descends to a unique isomorphism. -/
def FaithfullyFlatModuleIsoDescentStatement : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] (f : A →+* B),
    f.FaithfullyFlat →
      ∀ (M N : ModuleCat.{u} A)
        (e : (extendScalars f).obj M ≅ (extendScalars f).obj N),
        e.hom ≫ (extendScalars f).map ((extendRestrictScalarsAdj f).unit.app N) =
          (extendScalars f).map ((extendRestrictScalarsAdj f).unit.app M) ≫
            (extendScalars f).map ((restrictScalars f).map e.hom) →
        ∃! e₀ : M ≅ N, (extendScalars f).mapIso e₀ = e

/-- Morphism and isomorphism descent for the canonical coactions on extended
modules along faithfully flat maps of commutative rings. -/
def FaithfullyFlatModuleHomIsoDescentStatement : Prop :=
  FaithfullyFlatModuleHomDescentStatement.{u} ∧
    FaithfullyFlatModuleIsoDescentStatement.{u}

end Langlands.Algebra.Modules
