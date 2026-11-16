import Langlands.Cohomology.SiteCech.FreeNerve
import Mathlib.Algebra.Homology.QuasiIso

/-! # Exactness target for free sheaf Čech nerves of covering presheaf arrows -/

namespace Langlands.Cohomology.SiteCech

open CategoryTheory

universe u v w

/-- A locally surjective arrow of set-valued presheaves gives an exact augmented
free sheaf Čech complex, expressed as a quasi-isomorphism to its target in degree zero. -/
def FreeCechCoverExactnessStatement
    (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)] : Prop :=
  ∀ (f : Arrow (Cᵒᵖ ⥤ Type w)), Presheaf.IsLocallySurjective J f.hom →
    QuasiIso (freeCechAugmentation J R f)

end Langlands.Cohomology.SiteCech
