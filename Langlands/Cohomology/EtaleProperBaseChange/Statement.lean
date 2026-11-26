import Langlands.Geometry.EtaleDerivedAdjunction
import Langlands.Geometry.EtaleDerivedInverseImageCoherence
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Proper base change for bounded torsion étale coefficients

The proper base change theorem on the small étale sites of the four
schemes, expressed by the mate in the bounded-below derived categories.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Geometry
open EtaleDerivedSections EtaleDerivedInverseImage EtaleDerivedDirectImage

universe u wS wY wT wZ

set_option autoImplicit false

namespace Langlands.Cohomology

variable {S Y T Z : Scheme.{u}} (R : Type u) [CommRing R]
  [HasDerivedCategory.{wS} (ModuleSheaf S R)] [HasDerivedCategory.{wY} (ModuleSheaf Y R)]
  [HasDerivedCategory.{wT} (ModuleSheaf T R)] [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  {f : Y ⟶ S} {g : T ⟶ S} {f' : Z ⟶ T} {g' : Z ⟶ Y}

/-- The derived comparison for a commutative square. Its adjunct under
`g⁻¹ ⊣ Rg_*` is the image of the unit of `g'⁻¹ ⊣ Rg'_*`, followed by
the comparison of the composite derived direct images. -/
def etaleDerivedBaseChangeMap (square : g' ≫ f = f' ≫ g)
    (F : DerivedCategory.Plus (ModuleSheaf Y R)) :
    (plusFunctor g R).obj ((rightDerivedFunctor f R).obj F) ⟶
      (rightDerivedFunctor f' R).obj ((plusFunctor g' R).obj F) :=
  let pullbackIso : plusFunctor g R ⋙ plusFunctor f' R ≅
      plusFunctor f R ⋙ plusFunctor g' R :=
    plusFunctorComp R g f' ≪≫
      eqToIso (congrArg (fun h : Z ⟶ S => plusFunctor h R) square.symm) ≪≫
      (plusFunctorComp R f g').symm
  let fAdj := EtaleDerivedAdjunction.adjunction f R
  let gAdj := EtaleDerivedAdjunction.adjunction g R
  let f'Adj := EtaleDerivedAdjunction.adjunction f' R
  let g'Adj := EtaleDerivedAdjunction.adjunction g' R
  let pushforwardIso :=
    (fAdj.comp g'Adj).rightAdjointUniq ((gAdj.comp f'Adj).ofNatIsoLeft pullbackIso)
  (gAdj.homEquiv _ _).symm
    ((rightDerivedFunctor f R).map (g'Adj.unit.app F) ≫
      pushforwardIso.hom.app ((plusFunctor g' R).obj F))

/-- For a proper morphism and a Cartesian square, the canonical base-change
arrow is an isomorphism on any coefficient sheaf killed by a positive
integer, placed in degree zero. -/
def EtaleProperBaseChangeStatement (square : IsPullback g' f' f g) [IsProper f] : Prop :=
  ∀ F : ModuleSheaf Y R, (∃ N : ℕ, 0 < N ∧ N • (𝟙 F) = 0) →
    IsIso (etaleDerivedBaseChangeMap R square.w
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf Y R) 0).obj F))

end Langlands.Cohomology
