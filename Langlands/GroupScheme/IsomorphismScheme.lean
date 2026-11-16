import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.GroupScheme.LocalGroupIsoRefinement
import Langlands.GroupScheme.SchemeActionOfPointLaws

/-! # Supplied schemes representing group-scheme isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An actual relative scheme representing isomorphisms on every scheme test.
The universal family is natural on every refinement of a test. -/
structure GroupIsomorphismScheme {S : Scheme.{u}} (G H : GroupScheme S) where
  parameter : Over S
  universalIso : LocalGroupIso G H parameter
  bijective : ∀ (T : Over S),
    Function.Bijective (fun p : T ⟶ parameter => universalIso.refine p)

namespace GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H)

/-- Points of a representing scheme classify all natural local isomorphisms. -/
def pointsEquiv (T : Over S) : (T ⟶ I.parameter) ≃ LocalGroupIso G H T :=
  Equiv.ofBijective _ (I.bijective T)

@[simp] theorem pointsEquiv_apply (T : Over S) (p : T ⟶ I.parameter) :
    I.pointsEquiv T p = I.universalIso.refine p := rfl

/-- The point classifying a specified natural family of actual isomorphisms. -/
def classify {T : Over S} (e : LocalGroupIso G H T) : T ⟶ I.parameter :=
  (I.pointsEquiv T).symm e

@[simp] theorem refine_classify {T : Over S} (e : LocalGroupIso G H T) :
    I.universalIso.refine (I.classify e) = e :=
  (I.pointsEquiv T).apply_symm_apply e

@[simp] theorem classify_refine {T : Over S} (p : T ⟶ I.parameter) :
    I.classify (I.universalIso.refine p) = p :=
  (I.pointsEquiv T).symm_apply_apply p

/-- All-refinement equality of evaluated isomorphisms detects equality of points. -/
theorem hom_ext {T : Over S} {p q : T ⟶ I.parameter}
    (h : ∀ (W : Over S) (t : W ⟶ T) (g : W ⟶ G.X),
      I.universalIso.toFun (t ≫ p) g = I.universalIso.toFun (t ≫ q) g) :
    p = q := by
  apply (I.bijective T).1
  exact LocalGroupIso.ext_toFun h

/-- The classification bijection is natural in its test scheme. -/
theorem comp_classify {T W : Over S} (t : W ⟶ T) (e : LocalGroupIso G H T) :
    t ≫ I.classify e = I.classify (e.refine t) := by
  apply (I.bijective W).1
  change I.universalIso.refine (t ≫ I.classify e) =
    I.universalIso.refine (I.classify (e.refine t))
  rw [I.refine_classify]
  have he := I.refine_classify e
  have h := congrArg (fun a => a.refine t) he
  simpa only [LocalGroupIso.refine, Category.assoc] using h

/-- Actual isomorphisms of base-changed groups classify points of the scheme. -/
def baseChangeIsoEquiv (T : Over S) :
    ((baseChange T.hom).obj G ≅ (baseChange T.hom).obj H) ≃
      (T ⟶ I.parameter) :=
  LocalGroupIso.baseChangeIsoEquiv.trans (I.pointsEquiv T).symm

variable (a : AutomorphicAction A G)

/-- Inverse precomposition of the universal isomorphism by an automorphic action. -/
def actionHom : A.X ⊗ I.parameter ⟶ I.parameter :=
  I.classify ((I.universalIso.refine (snd A.X I.parameter)).twist a
    (fst A.X I.parameter)⁻¹)

/-- Evaluation of inverse precomposition on every relative test. -/
theorem actionHom_eval {T : Over S} (d : T ⟶ A.X) (p : T ⟶ I.parameter)
    (g : T ⟶ G.X) :
    I.universalIso.toFun (lift d p ≫ I.actionHom a) g =
      I.universalIso.toFun p (a.act d⁻¹ g) := by
  have h := congrArg
    (fun e : LocalGroupIso G H (A.X ⊗ I.parameter) => e.toFun (lift d p) g)
    (I.refine_classify
      ((I.universalIso.refine (snd A.X I.parameter)).twist a
        (fst A.X I.parameter)⁻¹))
  change I.universalIso.toFun (lift d p ≫ I.actionHom a) g =
    I.universalIso.toFun (lift d p ≫ snd A.X I.parameter)
      (a.act (lift d p ≫ (fst A.X I.parameter)⁻¹) g) at h
  simpa only [GrpObj.comp_inv, lift_fst, lift_snd] using h

/-- The canonical left action on isomorphisms is inverse precomposition. -/
@[instance_reducible]
def modObj : ModObj A.X I.parameter :=
  schemeActionOfPointLaws (I.actionHom a)
    (fun p => by
      apply I.hom_ext
      intro W t g
      simp only [← Category.assoc, comp_lift, MonObj.comp_one,
        I.actionHom_eval, inv_one, a.act_one_left])
    (fun d d' p => by
      apply I.hom_ext
      intro W t g
      simp only [← Category.assoc, comp_lift, MonObj.comp_mul,
        I.actionHom_eval, mul_inv_rev, a.act_mul_left])

/-- The categorical action has the required all-test correction equation. -/
theorem smul_eval {T : Over S} (d : T ⟶ A.X) (p : T ⟶ I.parameter)
    (g : T ⟶ G.X) :
    letI := I.modObj a
    I.universalIso.toFun (d • p) g =
      I.universalIso.toFun p (a.act d⁻¹ g) :=
  I.actionHom_eval a d p g

end GroupIsomorphismScheme

end Langlands.GroupScheme
