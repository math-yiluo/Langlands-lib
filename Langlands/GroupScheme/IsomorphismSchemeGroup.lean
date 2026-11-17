import Langlands.GroupScheme.IsomorphismPresheaf
import Langlands.GroupScheme.AutomorphismScheme

/-! # The group scheme carried by a supplied automorphism representer -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}

/-- Natural local automorphisms form a group under composition, with the right
factor acting first. -/
instance : Group (LocalGroupIso G G U) where
  one :=
    { toFun _ := MulEquiv.refl _
      naturality _ _ _ := rfl }
  mul e f :=
    { toFun a := (f.toFun a).trans (e.toFun a)
      naturality t a g := by
        change e.toFun (t ≫ a) (f.toFun (t ≫ a) (t ≫ g)) =
          t ≫ e.toFun a (f.toFun a g)
        rw [f.naturality, e.naturality] }
  inv e := e.symm
  mul_assoc e f h := by
    apply ext_toFun
    intro T a g
    rfl
  one_mul e := by
    apply ext_toFun
    intro T a g
    rfl
  mul_one e := by
    apply ext_toFun
    intro T a g
    rfl
  inv_mul_cancel e := by
    apply ext_toFun
    intro T a g
    exact (e.toFun a).symm_apply_apply g

@[simp] theorem one_toFun {T : Over S} (a : T ⟶ U) (g : T ⟶ G.X) :
    (1 : LocalGroupIso G G U).toFun a g = g := rfl

@[simp] theorem mul_toFun (e f : LocalGroupIso G G U)
    {T : Over S} (a : T ⟶ U) (g : T ⟶ G.X) :
    (e * f).toFun a g = e.toFun a (f.toFun a g) := rfl

@[simp] theorem inv_toFun (e : LocalGroupIso G G U)
    {T : Over S} (a : T ⟶ U) (g : T ⟶ G.X) :
    (e⁻¹).toFun a g = (e.toFun a).symm g := rfl

/-- Refinement is a homomorphism for composition of local automorphisms. -/
def refineHom {V : Over S} (r : V ⟶ U) :
    LocalGroupIso G G U →* LocalGroupIso G G V where
  toFun e := e.refine r
  map_one' := by
    apply ext_toFun
    intro T a g
    rfl
  map_mul' e f := by
    apply ext_toFun
    intro T a g
    rfl

/-- The full automorphism functor with its composition group law. -/
def automorphismPresheaf (G : GroupScheme S) : (Over S)ᵒᵖ ⥤ GrpCat where
  obj T := GrpCat.of (LocalGroupIso G G T.unop)
  map r := GrpCat.ofHom (refineHom r.unop)
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro e
    exact refine_id e
  map_comp r s := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro e
    exact (refine_comp e r.unop s.unop).symm

end LocalGroupIso

namespace GroupIsomorphismScheme

variable {S : Scheme.{u}} {G : GroupScheme S}
  (I : GroupIsomorphismScheme G G)

/-- A supplied Isom scheme also represents the underlying set functor of the
group-valued automorphism presheaf. -/
def automorphismRepresentableBy :
    (LocalGroupIso.automorphismPresheaf G ⋙ forget GrpCat).RepresentableBy I.parameter where
  homEquiv := I.pointsEquiv _
  homEquiv_comp r p := (LocalGroupIso.refine_comp I.universalIso p r).symm

/-- Composition of natural local automorphisms induces a group structure on the
same parameter scheme. -/
def automorphismGroup : GroupScheme S :=
  letI := GrpObj.ofRepresentableBy I.parameter
    (LocalGroupIso.automorphismPresheaf G) I.automorphismRepresentableBy
  Grp.mk I.parameter

/-- The represented point groups are the groups of all natural local
automorphisms, with the right factor acting first. -/
def automorphismPointsEquiv (T : Over S) :
    (T ⟶ I.automorphismGroup.X) ≃* LocalGroupIso G G T where
  toEquiv := I.pointsEquiv T
  map_mul' p q := by
    let R := I.automorphismRepresentableBy
    change R.homEquiv (lift p q ≫ R.homEquiv.symm
      (R.homEquiv (fst I.parameter I.parameter) *
        R.homEquiv (snd I.parameter I.parameter))) =
      R.homEquiv p * R.homEquiv q
    rw [R.homEquiv_comp, Equiv.apply_symm_apply]
    apply LocalGroupIso.ext_toFun
    intro W t g
    change ((I.universalIso.refine (fst I.parameter I.parameter) *
      I.universalIso.refine (snd I.parameter I.parameter)).refine (lift p q)).toFun t g =
        (I.universalIso.refine p * I.universalIso.refine q).toFun t g
    simp only [LocalGroupIso.mul_toFun,
      LocalGroupIso.refine_toFun, Category.assoc, lift_fst, lift_snd]

@[simp] theorem automorphismPointsEquiv_apply (T : Over S)
    (p : T ⟶ I.automorphismGroup.X) :
    I.automorphismPointsEquiv T p = I.universalIso.refine p := rfl

/-- Evaluation of the universal family is an actual morphism of schemes. -/
def evaluationHom : I.parameter ⊗ G.X ⟶ G.X :=
  I.universalIso.toFun (fst I.parameter G.X) (snd I.parameter G.X)

theorem evaluationHom_eval {T : Over S} (p : T ⟶ I.parameter) (g : T ⟶ G.X) :
    lift p g ≫ I.evaluationHom = I.universalIso.toFun p g := by
  simpa only [evaluationHom, lift_fst, lift_snd] using
    (I.universalIso.naturality (lift p g)
      (fst I.parameter G.X) (snd I.parameter G.X)).symm

theorem universalIso_one {T : Over S} (g : T ⟶ G.X) :
    I.universalIso.toFun (1 : T ⟶ I.automorphismGroup.X) g = g := by
  have h := congrArg (fun e : LocalGroupIso G G T => e.toFun (𝟙 T) g)
    (I.automorphismPointsEquiv T).map_one
  simpa only [automorphismPointsEquiv_apply, LocalGroupIso.refine_toFun,
    Category.id_comp, LocalGroupIso.one_toFun] using h

theorem universalIso_mul {T : Over S} (p q : T ⟶ I.automorphismGroup.X)
    (g : T ⟶ G.X) :
    I.universalIso.toFun (p * q) g =
      I.universalIso.toFun p (I.universalIso.toFun q g) := by
  have h := congrArg (fun e : LocalGroupIso G G T => e.toFun (𝟙 T) g)
    ((I.automorphismPointsEquiv T).map_mul p q)
  simpa only [automorphismPointsEquiv_apply, LocalGroupIso.refine_toFun,
    Category.id_comp, LocalGroupIso.mul_toFun] using h

/-- The universal automorphism family is the evaluation action of the represented
automorphism group scheme. -/
def evaluationAction : AutomorphicAction I.automorphismGroup G where
  hom := I.evaluationHom
  one_left g := by
    rw [I.evaluationHom_eval, I.universalIso_one]
  mul_left p q g := by
    simp only [I.evaluationHom_eval, I.universalIso_mul]
  mul_right p g h := by
    simp only [I.evaluationHom_eval, map_mul]

@[simp] theorem evaluationAction_act {T : Over S}
    (p : T ⟶ I.automorphismGroup.X) (g : T ⟶ G.X) :
    I.evaluationAction.act p g = I.universalIso.toFun p g :=
  I.evaluationHom_eval p g

/-- The action-induced local family agrees with the original universal family
on every refinement of every relative test scheme. -/
@[simp] theorem evaluationAction_localIso {T : Over S}
    (p : T ⟶ I.automorphismGroup.X) :
    I.evaluationAction.localIso p = I.universalIso.refine p := by
  apply LocalGroupIso.ext_toFun
  intro W t g
  exact I.evaluationAction_act (t ≫ p) g

/-- A supplied scheme representing all automorphisms canonically supplies the
full automorphism group scheme and its universal action. -/
def toGroupAutomorphismScheme : GroupAutomorphismScheme G where
  group := I.automorphismGroup
  action := I.evaluationAction
  bijective T := by
    have h : (fun x : T ⟶ I.automorphismGroup.X => I.evaluationAction.localIso x) =
        (I.automorphismPointsEquiv T : _ → _) := by
      funext x
      rw [I.evaluationAction_localIso, I.automorphismPointsEquiv_apply]
    rw [h]
    exact (I.automorphismPointsEquiv T).bijective

@[simp] theorem toGroupAutomorphismScheme_group_X :
    I.toGroupAutomorphismScheme.group.X = I.parameter := rfl

end GroupIsomorphismScheme

end Langlands.GroupScheme
