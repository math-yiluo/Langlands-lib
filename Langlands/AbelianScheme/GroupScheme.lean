import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Group schemes over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace Langlands

/-- Group schemes over `S`, with their actual multiplication, unit and inverse maps. -/
abbrev GroupScheme (S : AlgebraicGeometry.Scheme.{u}) := Grp (Over S)

namespace GroupScheme

variable {S T : AlgebraicGeometry.Scheme.{u}}

/-- The group-valued functor of points on all schemes over the base. -/
abbrev points (G : GroupScheme S) : (Over S)ᵒᵖ ⥤ GrpCat :=
  yonedaGrpObj G.X

/-- A group-scheme homomorphism acts naturally on points by postcomposition. -/
abbrev pointsMap {G H : GroupScheme S} (f : G ⟶ H) : G.points ⟶ H.points :=
  yonedaGrp.map f

@[simp] theorem pointsMap_apply {G H : GroupScheme S} (f : G ⟶ H)
    (U : Over S) (x : U ⟶ G.X) : (pointsMap f).app (op U) x = x ≫ f.hom.hom := rfl

/-- The underlying set-valued functor of points is represented by the scheme over `S`. -/
abbrev pointsRepresentableBy (G : GroupScheme S) :
    (G.points ⋙ forget GrpCat).RepresentableBy G.X :=
  yonedaGrpObjRepresentableBy G.X

/-- Homomorphisms in additive notation. The target alone needs to be commutative. -/
abbrev HomAdd (G H : GroupScheme S) := Additive (G ⟶ H)

instance (G H : GroupScheme S) [IsCommMonObj H.X] : AddCommGroup (HomAdd G H) :=
  inferInstanceAs (AddCommGroup (Additive (G ⟶ H)))

/-- Evaluation at a point is additive in a homomorphism into a commutative group scheme. -/
def evalHom (G H : GroupScheme S) [IsCommMonObj H.X] (U : Over S) (x : U ⟶ G.X) :
    HomAdd G H →+ Additive (U ⟶ H.X) where
  toFun f := Additive.ofMul (x ≫ f.toMul.hom.hom)
  map_zero' := by
    change x ≫ (1 : G ⟶ H).hom.hom = (1 : U ⟶ H.X)
    simp
  map_add' f g := by
    change x ≫ (f.toMul * g.toMul).hom.hom =
      (x ≫ f.toMul.hom.hom) * (x ≫ g.toMul.hom.hom)
    simp [MonObj.comp_mul]

/-- Base change is the actual scheme pullback, with its induced group law. -/
abbrev baseChange (f : T ⟶ S) : GroupScheme S ⥤ GroupScheme T :=
  (Over.pullback f).mapGrp

end GroupScheme

/-- A commutative group scheme. Commutativity is explicit, without geometric assumptions. -/
structure CommGroupScheme (S : AlgebraicGeometry.Scheme.{u}) extends GroupScheme S where
  [comm : IsCommMonObj X]

attribute [instance] CommGroupScheme.comm

namespace CommGroupScheme

variable {S T : AlgebraicGeometry.Scheme.{u}}

/-- The additive notation on homomorphisms is the pointwise group law. -/
instance : Category (CommGroupScheme S) where
  Hom G H := Additive (G.toGrp ⟶ H.toGrp)
  id G := Additive.ofMul (𝟙 G.toGrp)
  comp f g := Additive.ofMul (f.toMul ≫ g.toMul)
  id_comp := by
    intro G H f
    exact congrArg Additive.ofMul (Category.id_comp f.toMul)
  comp_id := by
    intro G H f
    exact congrArg Additive.ofMul (Category.comp_id f.toMul)
  assoc := by
    intro G H I J f g h
    exact congrArg Additive.ofMul (Category.assoc f.toMul g.toMul h.toMul)

/-- Forget additive notation on a homomorphism. -/
abbrev groupHom {G H : CommGroupScheme S} (f : G ⟶ H) : G.toGrp ⟶ H.toGrp :=
  Additive.toMul f

/-- Every Hom group is the actual pointwise commutative group, written additively. -/
instance (G H : CommGroupScheme S) : AddCommGroup (G ⟶ H) :=
  inferInstanceAs (AddCommGroup (Additive (G.toGrp ⟶ H.toGrp)))

instance : Preadditive (CommGroupScheme S) where
  add_comp := by
    intro G H I f g h
    change (f.toMul * g.toMul) ≫ h.toMul = _
    exact MonObj.mul_comp _ _ _
  comp_add := by
    intro G H I f g h
    change f.toMul ≫ (g.toMul * h.toMul) = _
    exact MonObj.comp_mul _ _ _

/-- Underlying morphism of schemes of a commutative-group-scheme homomorphism. -/
abbrev hom {G H : CommGroupScheme S} (f : G ⟶ H) : G.X.left ⟶ H.X.left :=
  (groupHom f).hom.hom.left

@[simp] theorem hom_id (G : CommGroupScheme S) : hom (𝟙 G) = 𝟙 G.X.left := rfl

@[simp] theorem hom_comp {G H I : CommGroupScheme S} (f : G ⟶ H) (g : H ⟶ I) :
    hom (f ≫ g) = hom f ≫ hom g := rfl

/-- Base change of commutative group schemes and their homomorphisms. -/
def baseChange (f : T ⟶ S) : CommGroupScheme S ⥤ CommGroupScheme T where
  obj G := { (GroupScheme.baseChange f).obj G.toGrp with
    comm := Functor.isCommMonObj_obj (F := Over.pullback f) (M := G.X) }
  map g := Additive.ofMul ((GroupScheme.baseChange f).map (groupHom g))
  map_id G := congrArg Additive.ofMul ((GroupScheme.baseChange f).map_id G.toGrp)
  map_comp g h := congrArg Additive.ofMul
    ((GroupScheme.baseChange f).map_comp (groupHom g) (groupHom h))

/-- Endomorphisms, with composition as multiplication and pointwise addition. -/
abbrev End (G : CommGroupScheme S) := CategoryTheory.End G

instance (G : CommGroupScheme S) : Ring (End G) := inferInstanceAs (Ring (CategoryTheory.End G))

end CommGroupScheme
end Langlands
