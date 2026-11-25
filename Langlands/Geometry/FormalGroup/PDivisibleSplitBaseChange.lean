import Langlands.Geometry.FormalGroup.PDivisibleProductBaseChange
import Langlands.GroupScheme.Cartier.FiniteSchemeDualBaseChange

/-! # Pullback of the split polarized tower and its order action -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier GroupScheme.Cartier.FiniteDual GroupScheme.HomScheme

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime]
variable (G : PDivisibleGroup (CommRingCat.of R) p)

local notation "F" => baseChangeFunctor R S p
local notation "BC" => CommGroupScheme.baseChange (specBase R S)

local instance splitBaseChangeLevelFinite {T : CommRingCat.{u}} (W : PDivisibleGroup T p) (n : ℕ) :
    IsFinite (W.inclusions.obj n).X.hom := (W.finiteLocallyFree n).1
local instance splitBaseChangeLevelFlat {T : CommRingCat.{u}} (W : PDivisibleGroup T p) (n : ℕ) :
    Flat (W.inclusions.obj n).X.hom := (W.finiteLocallyFree n).2.1
local instance splitBaseChangeLevelFinitePresentation {T : CommRingCat.{u}} (W : PDivisibleGroup T p) (n : ℕ) :
    LocallyOfFinitePresentation (W.inclusions.obj n).X.hom := (W.finiteLocallyFree n).2.2

variable (hExact : FiniteCartierDualExactnessStatement.{u})

/-- The actual Cartier dual of the tower commutes with base change. -/
def baseChangeDualIso : (F).obj (G.dual hExact) ≅ ((F).obj G).dual hExact := by
  let U := (F).obj (G.dual hExact)
  let V := ((F).obj G).dual hExact
  let e (n : ℕ) : U.inclusions.obj n ≅ V.inclusions.obj n :=
    schemeDualBaseChangeIso (S := S) (G.inclusions.obj n)
  have h : ∀ {m n : ℕ} (i : m ⟶ n),
      U.inclusions.map i ≫ (e n).hom = (e m).hom ≫ V.inclusions.map i := by
    intro m n i
    exact schemeDualBaseChangeIso_naturality (S := S) (G.transfer i)
  have hi : ∀ {m n : ℕ} (i : m ⟶ n),
      V.inclusions.map i ≫ (e n).inv = (e m).inv ≫ U.inclusions.map i := by
    intro m n i
    apply (cancel_mono (e n).hom).mp
    rw [Category.assoc, (e n).inv_hom_id, Category.comp_id, Category.assoc, h i,
      ← Category.assoc, (e m).inv_hom_id, Category.id_comp]
  exact {
    hom := Hom.ofNaturalTransformation {
      app := fun n => (e n).hom
      naturality _ _ i := h i }
    inv := Hom.ofNaturalTransformation {
      app := fun n => (e n).inv
      naturality _ _ i := hi i }
    hom_inv_id := Hom.ext fun n => (e n).hom_inv_id
    inv_hom_id := Hom.ext fun n => (e n).inv_hom_id }

@[simp] theorem baseChangeDualIso_hom_app (n : ℕ) :
    ((baseChangeDualIso (S := S) G hExact).hom).app n =
      (schemeDualBaseChangeIso (S := S) (G.inclusions.obj n)).hom := rfl

/-- The actual base-change comparison commutes with dualization of tower maps. -/
theorem baseChangeDualIso_naturality {H : PDivisibleGroup (CommRingCat.of R) p} (f : G ⟶ H) :
    (F).map (f.dual hExact) ≫ (baseChangeDualIso (S := S) G hExact).hom =
      (baseChangeDualIso (S := S) H hExact).hom ≫ ((F).map f).dual hExact :=
  Hom.ext fun n => schemeDualBaseChangeIso_naturality (S := S) (f.app n)

/-- The product of actual integral tower isomorphisms. -/
def isoProdMap {T : CommRingCat.{u}} {A B C D : PDivisibleGroup T p} (e : A ≅ B) (f : C ≅ D) :
    A.prod C ≅ B.prod D where
  hom := Hom.prodMap e.hom f.hom
  inv := Hom.prodMap e.inv f.inv
  hom_inv_id := by rw [← Hom.prodMap_comp, e.hom_inv_id, f.hom_inv_id, Hom.prodMap_id]
  inv_hom_id := by rw [← Hom.prodMap_comp, e.inv_hom_id, f.inv_hom_id, Hom.prodMap_id]

/-- Pulling back the actual split tower gives the split tower of the pulled-back primal. -/
def baseChangeSplitIso : (F).obj (G.splitWithDual hExact) ≅ ((F).obj G).splitWithDual hExact :=
  baseChangeProdIso (S := S) G (G.dual hExact) ≪≫
    isoProdMap (Iso.refl ((F).obj G)) (baseChangeDualIso (S := S) G hExact)

/-- Pullback sends an actual integral endomorphism ring to the new one. -/
def baseChangeEnd : End G →+* End ((F).obj G) where
  toFun f := End.of ((F).map f.asHom)
  map_one' := congrArg End.of ((F).map_id G)
  map_mul' f g := congrArg End.of ((F).map_comp g.asHom f.asHom)
  map_zero' := congrArg End.of ((F).mapAddHom (X := G) (Y := G)).map_zero
  map_add' f g := congrArg End.of ((F).map_add (f := f.asHom) (g := g.asHom))

/-- The pullback comparison respects the full split order action. -/
theorem baseChangeSplitIso_order {A : Type v} [Ring A] (action : A →+* End G) (a : Aᵐᵒᵖ × A) :
    (F).map (splitOrderAction action hExact a).asHom ≫ (baseChangeSplitIso (S := S) G hExact).hom =
      (baseChangeSplitIso (S := S) G hExact).hom ≫
        (splitOrderAction ((baseChangeEnd (S := S) G).comp action) hExact a).asHom := by
  let x := action a.2
  let y := action a.1.unop
  let e := (baseChangeDualIso (S := S) G hExact).hom
  let t := (baseChangeProdIso (S := S) G (G.dual hExact)).hom
  change (F).map (Hom.prodMap x.asHom (y.asHom.dual hExact)) ≫ (t ≫ Hom.prodMap (𝟙 ((F).obj G)) e) =
    (t ≫ Hom.prodMap (𝟙 ((F).obj G)) e) ≫ Hom.prodMap ((F).map x.asHom) (((F).map y.asHom).dual hExact)
  rw [← Category.assoc, baseChangeProdIso_naturality, Category.assoc, Category.assoc,
    ← Hom.prodMap_comp, ← Hom.prodMap_comp, Category.comp_id, Category.id_comp,
    baseChangeDualIso_naturality]

end Langlands.PDivisibleGroup
