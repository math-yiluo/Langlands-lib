import Langlands.GroupScheme.IsomorphismPresheaf
import Langlands.GroupScheme.RelativeInnerForm

/-! # Transport of full Isom representatives along a group isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H K : GroupScheme S} {U : Over S}

namespace LocalGroupIso

/-- Postcompose a natural local family by an actual group-scheme isomorphism. -/
def postcompose (e : LocalGroupIso G H U) (i : H ≅ K) : LocalGroupIso G K U where
  toFun a := (e.toFun a).trans ((ofIso i U).toFun a)
  naturality t a g := by
    change e.toFun (t ≫ a) (t ≫ g) ≫ i.hom.hom.hom =
      t ≫ (e.toFun a g ≫ i.hom.hom.hom)
    rw [e.naturality, Category.assoc]

@[simp] theorem postcompose_refine (e : LocalGroupIso G H U) (i : H ≅ K)
    {V : Over S} (r : V ⟶ U) :
    (e.postcompose i).refine r = (e.refine r).postcompose i := rfl

@[simp] theorem postcompose_symm (e : LocalGroupIso G H U) (i : H ≅ K) :
    (e.postcompose i).postcompose i.symm = e := by
  apply ext_toFun
  intro T a g
  change (e.toFun a g ≫ i.hom.hom.hom) ≫ i.inv.hom.hom = e.toFun a g
  change e.toFun a g ≫ (i.hom ≫ i.inv).hom.hom = e.toFun a g
  rw [i.hom_inv_id]
  exact Category.comp_id _

/-- Postcomposition is a bijection on all natural local families. -/
def postcomposeEquiv (i : H ≅ K) (U : Over S) :
    LocalGroupIso G H U ≃ LocalGroupIso G K U where
  toFun e := e.postcompose i
  invFun e := e.postcompose i.symm
  left_inv e := e.postcompose_symm i
  right_inv e := e.postcompose_symm i.symm

/-- The bijections given by postcomposition commute with every test refinement. -/
def postcomposePresheafIso (i : H ≅ K) :
    presheaf G H ≅ presheaf G K :=
  NatIso.ofComponents (fun T => (postcomposeEquiv i T.unop).toIso)
    (fun _ => rfl)

end LocalGroupIso

namespace GroupIsomorphismScheme

/-- Transport a supplied full Isom representative, retaining its actual parameter scheme. -/
def postcompose (I : GroupIsomorphismScheme G H) (i : H ≅ K) :
    GroupIsomorphismScheme G K where
  parameter := I.parameter
  universalIso := I.universalIso.postcompose i
  bijective T := by
    exact ((I.pointsEquiv T).trans (LocalGroupIso.postcomposeEquiv i T)).bijective

@[simp] theorem postcompose_parameter (I : GroupIsomorphismScheme G H) (i : H ≅ K) :
    (I.postcompose i).parameter = I.parameter := rfl

@[simp] theorem postcompose_pointsEquiv (I : GroupIsomorphismScheme G H) (i : H ≅ K)
    (T : Over S) (p : T ⟶ I.parameter) :
    (I.postcompose i).pointsEquiv T p = (I.pointsEquiv T p).postcompose i := rfl

/-- A supplied isomorphism identifies the full Isom parameter with a supplied Aut parameter. -/
def ofAutomorphism (I : GroupIsomorphismScheme G G) (i : G ≅ H) :
    GroupIsomorphismScheme G H :=
  I.postcompose i

end GroupIsomorphismScheme

end Langlands.GroupScheme
