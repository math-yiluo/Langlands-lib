import Langlands.Sheaf.CompactSupport
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Action.Basic

/-!
# Derived section constructions on actual topological module sheaves

Enough injectives are supplied by Mathlib's Grothendieck-category theorem.
The chosen complexes compute the derived functors and are functorial in the
homotopy category. The inclusion of compact sections induces comparison maps.
-/

noncomputable section

namespace Langlands.Cohomology.TopologicalDerivedSections

open CategoryTheory CategoryTheory.Limits

universe u uK vK w

variable (X : TopCat.{u}) (R : Type u) [CommRing R]

/-- The existing category of module sheaves on the open-set site. -/
abbrev ModuleSheaf := TopCat.Sheaf (ModuleCat.{u} R) X

/-- Apply compact sections to Mathlib's constructed injective resolution. -/
def compactComplex (F : ModuleSheaf X R) : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((Langlands.Sheaf.CompactSupport.functor (X := X) (R := R)).mapHomologicalComplex _).obj
    (injectiveResolution F).cocomplex

/-- The corresponding functor takes values in the homotopy category. -/
def compactHomotopyFunctor :
    ModuleSheaf X R ⥤ HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℕ) :=
  (Langlands.Sheaf.CompactSupport.functor (X := X) (R := R)).rightDerivedToHomotopyCategory

/-- The actual right-derived compact-section functor in degree `n`. -/
def compactCohomology (n : ℕ) : ModuleSheaf X R ⥤ ModuleCat.{u} R :=
  (Langlands.Sheaf.CompactSupport.functor (X := X) (R := R)).rightDerived n

/-- Left exactness identifies the zeroth compact-support cohomology with compact sections. -/
def compactCohomologyZeroIso :
    compactCohomology X R 0 ≅ Langlands.Sheaf.CompactSupport.functor (X := X) (R := R) :=
  (Langlands.Sheaf.CompactSupport.functor (X := X) (R := R)).rightDerivedZeroIsoSelf

/-- The derived object is represented by the constructed complex. -/
def compactComplexIso (F : ModuleSheaf X R) :
    (compactHomotopyFunctor X R).obj F ≅
      (HomotopyCategory.quotient _ _).obj (compactComplex X R F) :=
  (injectiveResolution F).isoRightDerivedToHomotopyCategoryObj _

/-- Its cohomology is the actual homology of that representative. -/
def compactCohomologyIso (F : ModuleSheaf X R) (n : ℕ) :
    (compactCohomology X R n).obj F ≅ (compactComplex X R F).homology n :=
  (injectiveResolution F).isoRightDerivedObj _ n

/-- Derived ordinary global sections over the same actual sheaf category. -/
def ordinaryHomotopyFunctor :
    ModuleSheaf X R ⥤ HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℕ) :=
  (Langlands.Sheaf.CompactSupport.globalSections (X := X) (R := R)).rightDerivedToHomotopyCategory

/-- Ordinary cohomology as a module-valued derived functor. -/
def ordinaryCohomology (n : ℕ) : ModuleSheaf X R ⥤ ModuleCat.{u} R :=
  (Langlands.Sheaf.CompactSupport.globalSections (X := X) (R := R)).rightDerived n

/-- Left exactness of ordinary sections identifies its zeroth derived functor. -/
def ordinaryCohomologyZeroIso :
    ordinaryCohomology X R 0 ≅
      Langlands.Sheaf.CompactSupport.globalSections (X := X) (R := R) :=
  (Langlands.Sheaf.CompactSupport.globalSections (X := X) (R := R)).rightDerivedZeroIsoSelf

/-- The actual support-forgetting map of derived objects. -/
def forgetSupportHomotopy : compactHomotopyFunctor X R ⟶ ordinaryHomotopyFunctor X R :=
  (Langlands.Sheaf.CompactSupport.inclusion (X := X) (R := R)).rightDerivedToHomotopyCategory

/-- Forgetting support gives a natural map on each cohomology module. -/
def forgetSupport (n : ℕ) : compactCohomology X R n ⟶ ordinaryCohomology X R n :=
  (Langlands.Sheaf.CompactSupport.inclusion (X := X) (R := R)).rightDerived n

/-- Algebraic actions by fixed-space sheaf automorphisms act on the derived cohomology. -/
def actionFunctor (G : Type w) [Monoid G] (n : ℕ) :
    Action (ModuleSheaf X R) G ⥤ Action (ModuleCat.{u} R) G :=
  (compactCohomology X R n).mapAction G

/-- Every actual diagram of coefficient sheaves induces a diagram of cohomology modules. -/
def diagramFunctor (K : Type uK) [Category.{vK} K] (n : ℕ) :
    (K ⥤ ModuleSheaf X R) ⥤ (K ⥤ ModuleCat.{u} R) :=
  (Functor.whiskeringRight K (ModuleSheaf X R) (ModuleCat.{u} R)).obj
    (compactCohomology X R n)

/-- Support-forgetting is compatible with every map of the coefficient diagram. -/
def diagramForgetSupport (K : Type uK) [Category.{vK} K] (n : ℕ) :
    diagramFunctor X R K n ⟶
      (Functor.whiskeringRight K (ModuleSheaf X R) (ModuleCat.{u} R)).obj
        (ordinaryCohomology X R n) :=
  (Functor.whiskeringRight K (ModuleSheaf X R) (ModuleCat.{u} R)).map
    (forgetSupport X R n)

end Langlands.Cohomology.TopologicalDerivedSections
