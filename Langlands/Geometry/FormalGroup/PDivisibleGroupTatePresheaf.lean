import Langlands.Geometry.FormalGroup.PDivisibleGroupMorphisms
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Limits

/-! # The schematic Tate point functor of a p-divisible group -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

variable {S : Scheme.{u}}

/-- Actual scheme-valued test points, written additively and covariant in the group scheme. -/
def additivePointFunctor (S : Scheme.{u}) :
    CommGroupScheme S ⥤ ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj G := GroupScheme.additivePoints G.toGrp
  map f :=
    { app T := AddCommGrpCat.ofHom
        (MonoidHom.toAdditive ((GroupScheme.pointsMap (groupHom f)).app T).hom)
      naturality T U b := by
        ext x
        change (b.unop ≫ x.toMul) ≫ (groupHom f).hom.hom =
          b.unop ≫ (x.toMul ≫ (groupHom f).hom.hom)
        exact Category.assoc _ _ _ }
  map_id G := by
    apply NatTrans.ext
    funext T
    ext x
    change x.toMul ≫ 𝟙 G.X = x.toMul
    exact Category.comp_id _
  map_comp f g := by
    apply NatTrans.ext
    funext T
    ext x
    change x.toMul ≫ ((groupHom f).hom.hom ≫ (groupHom g).hom.hom) =
      (x.toMul ≫ (groupHom f).hom.hom) ≫ (groupHom g).hom.hom
    exact (Category.assoc _ _ _).symm

@[simp] theorem additivePointFunctor_map_apply {G H : CommGroupScheme S} (f : G ⟶ H)
    (T : (Over S)ᵒᵖ) (x : Additive (T.unop ⟶ G.X)) :
    ((additivePointFunctor S).map f).app T x =
      Additive.ofMul (x.toMul ≫ (groupHom f).hom.hom) := rfl

instance : (additivePointFunctor S).Additive where
  map_add {G H} f g := by
    apply NatTrans.ext
    funext T
    ext x
    exact (GroupScheme.evalHom G.toGrp H.toGrp T.unop x.toMul).map_add f g

end Langlands.CommGroupScheme

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]

/-- The inverse diagram of a p-divisible group is functorial in actual tower morphisms. -/
def inverseDiagramFunctor (R : CommRingCat.{u}) (p : ℕ) [Fact p.Prime] :
    PDivisibleGroup R p ⥤ (ℕᵒᵖ ⥤ CommGroupScheme (Spec R)) where
  obj G := G.inverseSystem
  map f :=
    { app n := f.app n.unop
      naturality _ _ i := f.transfer_naturality i.unop }
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (inverseDiagramFunctor R p).Additive where
  map_add := rfl

/-- The inverse diagram of points of the actual finite group schemes. -/
def schematicTatePointSystem (R : CommRingCat.{u}) (p : ℕ) [Fact p.Prime] :
    PDivisibleGroup R p ⥤ (ℕᵒᵖ ⥤ ((Over (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u})) :=
  inverseDiagramFunctor R p ⋙
    (Functor.whiskeringRight _ _ _).obj (CommGroupScheme.additivePointFunctor (Spec R))

instance : (schematicTatePointSystem R p).Additive := by
  unfold schematicTatePointSystem
  infer_instance

/-- The schematic Tate point presheaf, formed by taking the inverse limit of the actual levels. -/
def schematicTatePointFunctor (R : CommRingCat.{u}) (p : ℕ) [Fact p.Prime] :
    PDivisibleGroup R p ⥤ ((Over (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  schematicTatePointSystem R p ⋙ lim

/-- Projection from the schematic Tate point presheaf to the actual level `n`. -/
def schematicTatePointProjection (G : PDivisibleGroup R p) (n : ℕ) :
    (schematicTatePointFunctor R p).obj G ⟶
      GroupScheme.additivePoints (G.inclusions.obj n).toGrp :=
  limit.π ((schematicTatePointSystem R p).obj G) (op n)

@[reassoc] theorem schematicTatePointProjection_transfer (G : PDivisibleGroup R p)
    {m n : ℕ} (i : m ⟶ n) :
    G.schematicTatePointProjection n ≫
      (CommGroupScheme.additivePointFunctor (Spec R)).map (G.transfer i) =
    G.schematicTatePointProjection m :=
  limit.w ((schematicTatePointSystem R p).obj G) i.op

@[reassoc] theorem schematicTatePointProjection_naturality {G H : PDivisibleGroup R p}
    (f : G ⟶ H) (n : ℕ) :
    (schematicTatePointFunctor R p).map f ≫ H.schematicTatePointProjection n =
      G.schematicTatePointProjection n ≫
        (CommGroupScheme.additivePointFunctor (Spec R)).map (f.app n) :=
  limMap_π ((schematicTatePointSystem R p).map f) (op n)

instance : (schematicTatePointFunctor R p).Additive where
  map_add {G H} f g := by
    apply limit.hom_ext
    intro n
    change (schematicTatePointFunctor R p).map (f + g) ≫
      H.schematicTatePointProjection n.unop =
      ((schematicTatePointFunctor R p).map f + (schematicTatePointFunctor R p).map g) ≫
        H.schematicTatePointProjection n.unop
    rw [Preadditive.add_comp]
    simp only [schematicTatePointProjection_naturality]
    have h : (f + g).app n.unop = f.app n.unop + g.app n.unop := rfl
    rw [h, Functor.map_add, Preadditive.comp_add]

/-- The schematic Tate presheaf is a sheaf for every subcanonical topology on the scheme tests. -/
theorem isSheaf_schematicTatePoints (G : PDivisibleGroup R p)
    (J : GrothendieckTopology (Over (Spec R))) [J.Subcanonical] :
    Presheaf.IsSheaf J ((schematicTatePointFunctor R p).obj G) := by
  let F := (schematicTatePointSystem R p).obj G
  let F' : ℕᵒᵖ ⥤ Sheaf J AddCommGrpCat.{u} := ObjectProperty.lift _ F fun n =>
    GroupScheme.Cartier.FiniteDual.isSheaf_additivePoints J (G.inclusions.obj n.unop).toGrp
  exact Sheaf.isSheaf_of_isLimit F' (limit.cone F) (limit.isLimit F)

end Langlands.PDivisibleGroup
