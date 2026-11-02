import Langlands.AlgebraicGeometry.Picard.Groupoid
import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Mathlib.CategoryTheory.IsomorphismClasses

/-! # Isomorphism classes of the actual Picard groupoid -/

universe v u w

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Passing a Cat-valued pseudofunctor to isomorphism classes gives a functor. -/
def pseudofunctorIsoClasses (F : LocallyDiscrete C ⥤ᵖ Cat.{v, w}) : C ⥤ Type w where
  obj X := Quotient (isIsomorphicSetoid (F.obj (.mk X)))
  map f := isomorphismClasses.map (F.map f.toLoc)
  map_id X := by
    ext q
    induction q using Quotient.ind with | _ L =>
      exact Quotient.sound ⟨(Cat.Hom.toNatIso (F.mapId (.mk X))).app L⟩
  map_comp f g := by
    ext q
    induction q using Quotient.ind with | _ L =>
      exact Quotient.sound ⟨(Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)).app L⟩

end Langlands.CategoryTheory

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

variable {X Y : Scheme.{u}}

/-- Isomorphism classes of the actual line-bundle groupoid. -/
abbrev IsoClasses (X : Scheme.{u}) := Quotient (isIsomorphicSetoid (PicardGroupoid X))

/-- The isomorphism class of an actual line bundle regarded in the core. -/
def isoClass (L : PicardGroupoid X) : IsoClasses X := Quotient.mk _ L

/-- The quotient class determines the published ordinary Picard group element. -/
def classMap (X : Scheme.{u}) : IsoClasses X → Group X :=
  Quotient.lift (fun L ↦ L.of.classOf) (fun _ _ ⟨e⟩ ↦
    (LineBundle.classOf_eq_iff_iso _ _).mpr ⟨e.hom.iso⟩)

@[simp]
lemma classMap_isoClass (L : PicardGroupoid X) : classMap X (isoClass L) = L.of.classOf := rfl

/-- Quotienting the core gives exactly the ordinary published line-bundle classes. -/
def classEquiv (X : Scheme.{u}) : IsoClasses X ≃ Group X where
  toFun := classMap X
  invFun q := isoClass ⟨Group.lineBundleRepresentative X q⟩
  left_inv q := by
    induction q using Quotient.ind with | _ L =>
      apply Quotient.sound
      exact ⟨Core.isoMk ((LineBundle.classOf_eq_iff_iso _ _).mp
        (Group.classOf_lineBundleRepresentative X L.of.classOf)).some⟩
  right_inv q := Group.classOf_lineBundleRepresentative X q

/-- The isomorphism-class presheaf of the actual pullback pseudofunctor. -/
def classPresheaf : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) :=
  Langlands.CategoryTheory.pseudofunctorIsoClasses pseudofunctor

/-- The comparison is natural for every actual scheme morphism. -/
def classPresheafIso : classPresheaf ≅ Group.functor ⋙ forget AddCommGrpCat :=
  NatIso.ofComponents (fun X ↦ (classEquiv X.unop).toIso) (by
    intro X Y f
    ext q
    induction q using Quotient.ind with | _ L =>
      exact (Group.pullback_lineBundle_classOf f.unop L.of).symm)

/-- Isomorphism classes in the relative actual Picard groupoid. -/
def relativeClassPresheaf {S X : Scheme.{u}} (f : X ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  Langlands.CategoryTheory.pseudofunctorIsoClasses (relative f)

/-- Comparison with the exact ordinary class presheaf on all test schemes. -/
def relativeClassPresheafIso {S X : Scheme.{u}} (f : X ⟶ S) :
    relativeClassPresheaf f ≅ RelativePicard.classPresheaf f :=
  Functor.isoWhiskerLeft (relativeSpace f).op classPresheafIso

/-- The fppf sheaf of isomorphism classes of the actual relative groupoid. -/
def relativeClassSheaf {S X : Scheme.{u}} (f : X ⟶ S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (relativeClassPresheaf f)

/-- Its fppf sheafification is the exact published relative Picard sheaf. -/
def relativeClassSheafIso {S X : Scheme.{u}} (f : X ⟶ S) :
    relativeClassSheaf f ≅ RelativePicard.classSheaf f :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso
    (relativeClassPresheafIso f)

/-- The ordinary unit from groupoid isomorphism classes to their fppf sheaf. -/
def relativeToClassSheaf {S X : Scheme.{u}} (f : X ⟶ S) :
    relativeClassPresheaf f ⟶ (relativeClassSheaf f).obj :=
  toSheafify (Scheme.fppfTopology.over S) (relativeClassPresheaf f)

@[reassoc (attr := simp)]
lemma relativeToClassSheaf_comparison {S X : Scheme.{u}} (f : X ⟶ S) :
    relativeToClassSheaf f ≫ (relativeClassSheafIso f).hom.hom =
      (relativeClassPresheafIso f).hom ≫ RelativePicard.toClassSheaf f :=
  (toSheafify_naturality (Scheme.fppfTopology.over S)
    (relativeClassPresheafIso f).hom).symm

@[simp]
lemma relativeToClassSheaf_comparison_isoClass {S X : Scheme.{u}} (f : X ⟶ S)
    (T : Over S) (L : LineBundle ((relativeSpace f).obj T)) :
    (relativeClassSheafIso f).hom.hom.app (op T)
        ((relativeToClassSheaf f).app (op T) (isoClass ⟨L⟩)) =
      RelativePicard.sheafClassOf f T L :=
  congrArg (fun η ↦ η.app (op T) (isoClass ⟨L⟩))
    (relativeToClassSheaf_comparison f)

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
