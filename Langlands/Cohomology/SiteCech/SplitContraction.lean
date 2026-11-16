import Langlands.Cohomology.SiteCech.FreeNerve
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.Algebra.Homology.QuasiIso

/-! # Contraction of the free sheaf Čech nerve of a split presheaf arrow -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]
variable (f : Arrow (Cᵒᵖ ⥤ Type w)) (S : SplitEpi f.hom)

/-- A section of a presheaf arrow induces an extra degeneracy on its free sheaf
Čech nerve. -/
def freeCechExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy (freeAugmentedCechNerve J R f) :=
  (Arrow.AugmentedCechNerve.extraDegeneracy f S).map (freeSheafFunctor J R)

/-- The augmented free sheaf Čech complex of a split presheaf arrow is homotopy
equivalent to the free sheaf on its target, concentrated in degree zero. -/
def freeCechHomotopyEquiv :
    HomotopyEquiv (freeCechChainComplex J R f)
      ((ChainComplex.single₀ _).obj ((freeSheafFunctor J R).obj f.right)) :=
  (freeCechExtraDegeneracy J R f S).homotopyEquiv

@[simp]
theorem freeCechHomotopyEquiv_hom :
    (freeCechHomotopyEquiv J R f S).hom = freeCechAugmentation J R f :=
  rfl

/-- The actual free sheaf Čech augmentation is a quasi-isomorphism when the
presheaf arrow has a section. -/
theorem quasiIso_freeCechAugmentation_of_splitEpi (S : SplitEpi f.hom) :
    QuasiIso (freeCechAugmentation J R f) :=
  (freeCechHomotopyEquiv J R f S).quasiIso_hom

end Langlands.Cohomology.SiteCech
