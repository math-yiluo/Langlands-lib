import Langlands.Sheaf.Godement
import Langlands.Cohomology.Flasque.Statement
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Godement degree zero from the points of a topological space

For a point `x` of a topological space, the fiber functor of the site point
`Opens.pointGrothendieckTopology x` is identified with the ordinary stalk
functor. Its skyscraper sheaf functor is identified with the ordinary
skyscraper sheaf functor, compatibly with the adjunction units. Hence the
degree-zero Godement functor over all points of the space is the product of the
ordinary stalk skyscrapers, with the product of the ordinary units as
coaugmentation.
-/

noncomputable section

namespace Langlands.Sheaf.Godement

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe v u

attribute [local instance] Classical.propDecidable

variable {C : Type u} [Category.{v} C] [HasColimits.{v} C]
variable {X : TopCat.{v}} (x : X)

/-- Map an ordinary stalk to the fiber at the corresponding site point. -/
def stalkToFiber (P : X.Presheaf C) :
    P.stalk x ⟶ (Opens.pointGrothendieckTopology x).presheafFiber.obj P :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ P)
    { pt := _
      ι :=
        { app U := (Opens.pointGrothendieckTopology x).toPresheafFiber
            U.unop.1 ⟨⟨U.unop.2⟩⟩ P
          naturality U V i :=
            ((Opens.pointGrothendieckTopology x).toPresheafFiber_w
              ((OpenNhds.inclusion x).map i.unop) ⟨⟨V.unop.2⟩⟩ P).trans
              ((congrArg (fun y => (Opens.pointGrothendieckTopology x).toPresheafFiber
                U.unop.1 y P) (Subsingleton.elim _ _)).trans (Category.comp_id _).symm) } }

@[reassoc (attr := simp)]
theorem germ_stalkToFiber (P : X.Presheaf C) (U : Opens X) (hx : x ∈ U) :
    P.germ U x hx ≫ stalkToFiber x P =
      (Opens.pointGrothendieckTopology x).toPresheafFiber U ⟨⟨hx⟩⟩ P :=
  colimit.ι_desc _ _

/-- Map the fiber at the site point to the ordinary stalk. -/
def fiberToStalk (P : X.Presheaf C) :
    (Opens.pointGrothendieckTopology x).presheafFiber.obj P ⟶ P.stalk x :=
  (Opens.pointGrothendieckTopology x).presheafFiberDesc
    (fun U h => P.germ U x h.down.down) (fun _ _ f _ => P.germ_res f x _)

@[reassoc (attr := simp)]
theorem toPresheafFiber_fiberToStalk (P : X.Presheaf C) (U : Opens X)
    (h : (Opens.pointGrothendieckTopology x).fiber.obj U) :
    (Opens.pointGrothendieckTopology x).toPresheafFiber U h P ≫ fiberToStalk x P =
      P.germ U x h.down.down :=
  (Opens.pointGrothendieckTopology x).toPresheafFiber_presheafFiberDesc _ _ U h

variable (C) in
/-- The ordinary stalk functor is the fiber functor of the site point. -/
def stalkFiberIso :
    Presheaf.stalkFunctor C x ≅ (Opens.pointGrothendieckTopology x).presheafFiber :=
  NatIso.ofComponents
    (fun P =>
      { hom := stalkToFiber x P
        inv := fiberToStalk x P
        hom_inv_id := P.stalk_hom_ext fun U hx => by
          erw [germ_stalkToFiber_assoc, toPresheafFiber_fiberToStalk, Category.comp_id]
        inv_hom_id := (Opens.pointGrothendieckTopology x).presheafFiber_hom_ext
          fun U h => by
            erw [toPresheafFiber_fiberToStalk_assoc, germ_stalkToFiber, Category.comp_id]
            rfl })
    (fun {P Q} f => P.stalk_hom_ext fun U hx => by
      erw [Presheaf.stalkFunctor_map_germ_assoc, germ_stalkToFiber, germ_stalkToFiber_assoc,
        (Opens.pointGrothendieckTopology x).toPresheafFiber_naturality])

@[simp]
theorem stalkFiberIso_hom_app (P : X.Presheaf C) :
    (stalkFiberIso C x).hom.app P = stalkToFiber x P :=
  rfl

variable [HasLimits.{v} C]

variable (C) in
/-- On sheaves, the ordinary stalk functor is the fiber functor of the site point. -/
def sheafStalkFiberIso :
    Sheaf.forget C X ⋙ Presheaf.stalkFunctor C x ≅
      (Opens.pointGrothendieckTopology x).sheafFiber :=
  Functor.isoWhiskerLeft (Sheaf.forget C X) (stalkFiberIso C x)

variable (C) in
/-- The ordinary skyscraper sheaf functor is the skyscraper functor of the site
point: both are right adjoint to the identified fiber functors. -/
def skyscraperIso :
    skyscraperSheafFunctor x ≅
      (Opens.pointGrothendieckTopology x).skyscraperSheafFunctor (A := C) :=
  Adjunction.rightAdjointUniq
    ((stalkSkyscraperSheafAdjunction x).ofNatIsoLeft (sheafStalkFiberIso C x))
    (Opens.pointGrothendieckTopology x).skyscraperSheafAdjunction

variable (C) in
/-- The ordinary stalk-skyscraper endofunctor at `x` is the Godement point functor. -/
def pointFunctorIso :
    (Sheaf.forget C X ⋙ Presheaf.stalkFunctor C x) ⋙ skyscraperSheafFunctor x ≅
      pointFunctor (Cohomology.Flasque.spacePoints X) C x :=
  Functor.isoWhiskerRight (sheafStalkFiberIso C x) _ ≪≫
    Functor.isoWhiskerLeft _ (skyscraperIso C x)

/-- The identification carries the ordinary unit to the unit of the site point. -/
@[reassoc (attr := simp)]
theorem unit_pointFunctorIso_hom_app (F : X.Sheaf C) :
    (stalkSkyscraperSheafAdjunction x).unit.app F ≫ (pointFunctorIso C x).hom.app F =
      (Opens.pointGrothendieckTopology x).skyscraperSheafAdjunction.unit.app F := by
  exact (Category.assoc _ _ _).symm.trans (Adjunction.unit_rightAdjointUniq_hom_app
    ((stalkSkyscraperSheafAdjunction x).ofNatIsoLeft (sheafStalkFiberIso C x))
    (Opens.pointGrothendieckTopology x).skyscraperSheafAdjunction F)

variable (C X)

/-- The product over all points of the ordinary stalk skyscrapers. -/
def topZeroFunctor : X.Sheaf C ⥤ X.Sheaf C :=
  ∏ᶜ fun x : X => (Sheaf.forget C X ⋙ Presheaf.stalkFunctor C x) ⋙ skyscraperSheafFunctor x

/-- The product of the ordinary stalk-skyscraper units. -/
def topCoaugmentation : 𝟭 (X.Sheaf C) ⟶ topZeroFunctor C X :=
  Pi.lift fun x => (stalkSkyscraperSheafAdjunction x).unit

/-- The Godement degree-zero functor over all points is the product of the
ordinary stalk skyscrapers. -/
def topZeroFunctorIso : topZeroFunctor C X ≅ zeroFunctor (Cohomology.Flasque.spacePoints X) C :=
  Pi.mapIso fun x => pointFunctorIso C x

/-- The identification carries the ordinary coaugmentation to the Godement one. -/
@[reassoc (attr := simp)]
theorem topCoaugmentation_topZeroFunctorIso :
    topCoaugmentation C X ≫ (topZeroFunctorIso C X).hom =
      coaugmentation (Cohomology.Flasque.spacePoints X) C := by
  refine Pi.hom_ext (f := fun x => pointFunctor (Cohomology.Flasque.spacePoints X) C x)
    _ _ fun x => ?_
  have h1 := Pi.mapIso_hom_π (fun x => pointFunctorIso C x) x
  have h2 := Pi.lift_comp_π (fun x => (stalkSkyscraperSheafAdjunction (C := C) x).unit) x
  have h3 := coaugmentation_π (Cohomology.Flasque.spacePoints X) C x
  have h4 : (stalkSkyscraperSheafAdjunction (C := C) x).unit ≫ (pointFunctorIso C x).hom =
      (Opens.pointGrothendieckTopology x).skyscraperSheafAdjunction.unit :=
    NatTrans.ext (funext fun F => unit_pointFunctorIso_hom_app x F)
  exact (Category.assoc _ _ _).trans ((congrArg _ h1).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (pointFunctorIso C x).hom) h2).trans (h4.trans h3.symm))))

end Langlands.Sheaf.Godement
