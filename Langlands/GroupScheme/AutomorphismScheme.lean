import Langlands.GroupScheme.IsomorphismScheme

/-! # Supplied schemes representing group-scheme automorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The natural local automorphism defined by an arbitrary acting point. -/
def localIso (a : AutomorphicAction H G) {T : Over S} (h : T ⟶ H.X) :
    LocalGroupIso G G T where
  toFun t := a.pointAut _ (t ≫ h)
  naturality t b g := by
    change a.act ((t ≫ b) ≫ h) (t ≫ g) = t ≫ a.act (b ≫ h) g
    rw [Category.assoc]
    exact (a.naturality t (b ≫ h) g).symm

end AutomorphicAction

/-- An actual group scheme representing every natural local automorphism of a
supplied group scheme, with its universal automorphic action. -/
structure GroupAutomorphismScheme {S : Scheme.{u}} (G : GroupScheme S) where
  group : GroupScheme S
  action : AutomorphicAction group G
  bijective : ∀ (T : Over S),
    Function.Bijective (fun x : T ⟶ group.X => action.localIso x)

namespace GroupAutomorphismScheme

variable {S : Scheme.{u}} {G H K : GroupScheme S}
  (I : GroupAutomorphismScheme G)

/-- The point classifying a natural local automorphism. -/
def classifyPoint {T : Over S} (e : LocalGroupIso G G T) : T ⟶ I.group.X :=
  (Equiv.ofBijective _ (I.bijective T)).symm e

@[simp]
theorem localIso_classifyPoint {T : Over S} (e : LocalGroupIso G G T) :
    I.action.localIso (I.classifyPoint e) = e :=
  (Equiv.ofBijective _ (I.bijective T)).apply_symm_apply e

/-- Evaluation of the point classifying a local automorphism. -/
theorem classifyPoint_eval {T W : Over S} (e : LocalGroupIso G G T)
    (t : W ⟶ T) (g : W ⟶ G.X) :
    I.action.act (t ≫ I.classifyPoint e) g = e.toFun t g :=
  congrArg (fun f : LocalGroupIso G G T => f.toFun t g)
    (I.localIso_classifyPoint e)

/-- An action gives a homomorphism on the point groups of its parameter. -/
def classifyPoints (a : AutomorphicAction H G) (T : Over S) :
    (T ⟶ H.X) →* (T ⟶ I.group.X) where
  toFun x := I.classifyPoint (a.localIso x)
  map_one' := by
    apply (I.bijective T).1
    apply LocalGroupIso.ext_toFun
    intro W t g
    change I.action.act (t ≫ I.classifyPoint (a.localIso 1)) g =
      I.action.act (t ≫ 1) g
    rw [I.classifyPoint_eval, MonObj.comp_one, I.action.act_one_left]
    change a.act (t ≫ 1) g = g
    rw [MonObj.comp_one, a.act_one_left]
  map_mul' x y := by
    apply (I.bijective T).1
    apply LocalGroupIso.ext_toFun
    intro W t g
    change I.action.act (t ≫ I.classifyPoint (a.localIso (x * y))) g =
      I.action.act (t ≫ (I.classifyPoint (a.localIso x) *
        I.classifyPoint (a.localIso y))) g
    rw [I.classifyPoint_eval, MonObj.comp_mul, I.action.act_mul_left,
      I.classifyPoint_eval, I.classifyPoint_eval]
    change a.act (t ≫ (x * y)) g = a.act (t ≫ x) (a.act (t ≫ y) g)
    rw [MonObj.comp_mul, a.act_mul_left]

/-- Classification of an action commutes with every test refinement. -/
theorem classifyPoints_naturality (a : AutomorphicAction H G)
    {T W : Over S} (t : W ⟶ T) (x : T ⟶ H.X) :
    I.classifyPoints a W (t ≫ x) = t ≫ I.classifyPoints a T x := by
  apply (I.bijective W).1
  apply LocalGroupIso.ext_toFun
  intro V r g
  change I.action.act (r ≫ I.classifyPoint (a.localIso (t ≫ x))) g =
    I.action.act (r ≫ (t ≫ I.classifyPoint (a.localIso x))) g
  rw [I.classifyPoint_eval, ← Category.assoc, I.classifyPoint_eval]
  rfl

/-- The actual group-scheme homomorphism classifying an automorphic action. -/
def classifyAction (a : AutomorphicAction H G) : H ⟶ I.group :=
  homOfPoints (I.classifyPoints a) (I.classifyPoints_naturality a)

@[simp]
theorem comp_classifyAction (a : AutomorphicAction H G) {T : Over S}
    (x : T ⟶ H.X) :
    x ≫ (I.classifyAction a).hom.hom = I.classifyPoint (a.localIso x) :=
  comp_homOfPoints (I.classifyPoints a) (I.classifyPoints_naturality a) T x

/-- The classified homomorphism induces exactly the supplied action. -/
@[simp]
theorem action_restrict_classifyAction (a : AutomorphicAction H G) :
    I.action.restrict (I.classifyAction a) = a := by
  apply AutomorphicAction.ext_act
  intro T x g
  rw [AutomorphicAction.restrict_act, I.comp_classifyAction]
  have he := I.classifyPoint_eval (a.localIso x) (𝟙 T) g
  change I.action.act ((𝟙 T) ≫ I.classifyPoint (a.localIso x)) g =
    a.act ((𝟙 T) ≫ x) g at he
  simpa only [Category.id_comp] using he

/-- The universal action detects equality of classifying homomorphisms. -/
theorem restrict_injective {f g : H ⟶ I.group}
    (h : I.action.restrict f = I.action.restrict g) : f = g := by
  apply hom_ext_points
  intro T x
  apply (I.bijective T).1
  apply LocalGroupIso.ext_toFun
  intro W t y
  change I.action.act (t ≫ (x ≫ f.hom.hom)) y =
    I.action.act (t ≫ (x ≫ g.hom.hom)) y
  simpa only [AutomorphicAction.restrict_act, Category.assoc] using
    congrArg (fun a : AutomorphicAction H G => a.act (t ≫ x) y) h

/-- Classifying a restricted action is composition of its classifying map. -/
@[simp]
theorem classifyAction_restrict (a : AutomorphicAction H G) (f : K ⟶ H) :
    I.classifyAction (a.restrict f) = f ≫ I.classifyAction a := by
  apply I.restrict_injective
  rw [I.action_restrict_classifyAction]
  apply AutomorphicAction.ext_act
  intro T x y
  have h := congrArg (fun b : AutomorphicAction H G => b.act (x ≫ f.hom.hom) y)
    (I.action_restrict_classifyAction a)
  simpa only [AutomorphicAction.restrict_act, Grp.comp_hom_hom, Category.assoc]
    using h.symm

/-- Equality of induced actions is exactly equality of maps to the represented
full automorphism group. -/
theorem classifyAction_eq_iff (a b : AutomorphicAction H G) :
    I.classifyAction a = I.classifyAction b ↔ a = b := by
  constructor
  · intro h
    calc
      a = I.action.restrict (I.classifyAction a) :=
        (I.action_restrict_classifyAction a).symm
      _ = I.action.restrict (I.classifyAction b) := congrArg I.action.restrict h
      _ = b := I.action_restrict_classifyAction b
  · exact congrArg I.classifyAction

end GroupAutomorphismScheme

end Langlands.GroupScheme
