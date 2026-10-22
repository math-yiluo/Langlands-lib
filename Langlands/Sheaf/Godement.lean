import Langlands.Cohomology.CokernelComplex
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Godement constructions from actual points of a site

The degree-zero functor is the product, over a supplied family of site points,
of skyscraper sheaves of fibers. Its coaugmentation is constructed from the
stalk/skyscraper adjunctions. Iterating actual cokernels produces a functorial
cochain complex. No cohomology or comparison result is supplied as input.
-/

noncomputable section

namespace Langlands.Sheaf.Godement

open CategoryTheory CategoryTheory.Limits

universe wI w v u vA uA

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type wI} (points : I → GrothendieckTopology.Point.{w} J)
variable (A : Type uA) [Category.{vA} A]
variable [HasProducts.{w} A] [HasProducts.{wI} A] [HasColimitsOfSize.{w, w} A]

/-- The stalk/skyscraper endofunctor attached to one actual point. -/
def pointFunctor (i : I) : CategoryTheory.Sheaf J A ⥤ CategoryTheory.Sheaf J A :=
  (points i).sheafFiber ⋙ (points i).skyscraperSheafFunctor

/-- The degree-zero Godement functor, a categorical product of skyscrapers. -/
def zeroFunctor : CategoryTheory.Sheaf J A ⥤ CategoryTheory.Sheaf J A :=
  ∏ᶜ fun i => pointFunctor points A i

/-- The coaugmentation uses the units of the actual fiber/skyscraper adjunctions. -/
def coaugmentation : 𝟭 (CategoryTheory.Sheaf J A) ⟶ zeroFunctor points A :=
  Pi.lift fun i => (points i).skyscraperSheafAdjunction.unit

/-- Projection of the Godement coaugmentation is the corresponding adjunction unit. -/
@[reassoc (attr := simp)]
theorem coaugmentation_π (i : I) :
    coaugmentation points A ≫ Pi.π (fun i => pointFunctor points A i) i =
      (points i).skyscraperSheafAdjunction.unit :=
  Pi.lift_comp_π (fun i => (points i).skyscraperSheafAdjunction.unit) i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A jointly faithful family of fibers makes the constructed coaugmentation monic. -/
theorem mono_coaugmentation_of_jointlyFaithful
    (hpoints : JointlyFaithful (fun i => (points i).sheafFiber (A := A)))
    (F : CategoryTheory.Sheaf J A) :
    Mono ((coaugmentation points A).app F) := by
  constructor
  intro E f g h
  change E ⟶ F at f g
  apply hpoints.map_injective
  intro i
  have hunit :
      f ≫ (points i).skyscraperSheafAdjunction.unit.app F =
        g ≫ (points i).skyscraperSheafAdjunction.unit.app F := by
    have hπ := congrArg
      (fun t => t ≫ (Pi.π (fun i => pointFunctor points A i) i).app F) h
    simpa only [Category.assoc, ← NatTrans.comp_app, coaugmentation_π] using hπ
  have hadj := congrArg
    ((points i).skyscraperSheafAdjunction.homEquiv E
      ((points i).sheafFiber.obj F)).symm hunit
  have hidentity :
      ((points i).skyscraperSheafAdjunction.homEquiv F
        ((points i).sheafFiber.obj F)).symm
        ((points i).skyscraperSheafAdjunction.unit.app F) = 𝟙 _ :=
    (points i).skyscraperSheafAdjunction.homEquiv_symm_unit F
  have hf := (points i).skyscraperSheafAdjunction.homEquiv_naturality_left_symm
    f ((points i).skyscraperSheafAdjunction.unit.app F)
  have hg := (points i).skyscraperSheafAdjunction.homEquiv_naturality_left_symm
    g ((points i).skyscraperSheafAdjunction.unit.app F)
  rw [hidentity, Category.comp_id] at hf hg
  exact hf.symm.trans (hadj.trans hg)

variable [Abelian A] [HasSheafify J A]

/-- The cochain complex of sheaves obtained by iterated cokernels. -/
def complexFunctor :
    CategoryTheory.Sheaf J A ⥤ CochainComplex (CategoryTheory.Sheaf J A) ℕ :=
  Cohomology.CokernelComplex.functor (zeroFunctor points A) (coaugmentation points A)

/-- The Godement cochain complex of a sheaf, relative to the family of points. -/
abbrev complex (F : CategoryTheory.Sheaf J A) :
    CochainComplex (CategoryTheory.Sheaf J A) ℕ :=
  (complexFunctor points A).obj F

/-- The canonical morphism from a sheaf to degree zero of its Godement complex. -/
def augmentation (F : CategoryTheory.Sheaf J A) :
    F ⟶ (complex points A F).X 0 :=
  (coaugmentation points A).app F

@[reassoc (attr := simp)]
theorem augmentation_d (F : CategoryTheory.Sheaf J A) :
    augmentation points A F ≫ (complex points A F).d 0 1 = 0 :=
  Cohomology.CokernelComplex.augmentation_d _ _ F

end Langlands.Sheaf.Godement
