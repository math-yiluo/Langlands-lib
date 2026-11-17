import Langlands.GroupScheme.Reductive.RelativeTorusConjugationRigidity

/-! # Generator comparisons with a torus conjugate over algebras -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R]
  {G H K : GroupScheme (Spec (CommRingCat.of R))}
  {T : CommGroupScheme (Spec (CommRingCat.of R))}
  {V : Over (Spec (CommRingCat.of R))}

/-- Conjugation on all points of one supplied additive-group map, on every
test scheme refining the parameter scheme. -/
def TorusConjugatesOnRoot (j : T.toGrp ⟶ H) (f F : G ⟶ H)
    (t : V ⟶ T.X) (u : Ga R ⟶ G) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R))) (d : Z ⟶ V) (x : Γ(Z.left, ⊤)),
    rootPoint u Z x ≫ f.hom.hom =
      (d ≫ t ≫ j.hom.hom) * (rootPoint u Z x ≫ F.hom.hom) *
        (d ≫ t ≫ j.hom.hom)⁻¹

/-- An all-refinement root-point conjugation equation gives equality of the
actual base-changed root restrictions over each algebra point. -/
theorem torusConjugateAlgebraHom_root
    (j : T.toGrp ⟶ H) (f F : G ⟶ H) (t : V ⟶ T.X) (u : Ga R ⟶ G)
    (h : TorusConjugatesOnRoot j f F t u)
    (A : Type u) [CommRing A] [Algebra R A] (a : fieldPoint R A ⟶ V) :
    baseChangeRoot A u ≫ (baseChange (algebraBaseMap R A)).map f =
      baseChangeRoot A u ≫ torusConjugateAlgebraHom A j F t a := by
  apply hom_ext_rootPoint
  intro Z x
  rw [rootPoint_comp, rootPoint_comp]
  apply (baseChangePointsEquiv (algebraBaseMap R A) H Z).injective
  rw [baseChangePointsEquiv_comp, torusConjugateAlgebraHom_apply,
    baseChangePointsEquiv_rootPoint]
  exact h _ ((Over.map (algebraBaseMap R A)).map (toUnit Z) ≫ a) x

/-- Conjugation by the commutative target group fixes any restriction factoring
through that group, after arbitrary algebra base change. -/
theorem torusConjugateAlgebraHom_comp
    (j : T.toGrp ⟶ H) (F : G ⟶ H) (t : V ⟶ T.X)
    (i : K ⟶ G) (tau : K ⟶ T.toGrp) (hF : i ≫ F = tau ≫ j)
    (A : Type u) [CommRing A] [Algebra R A] (a : fieldPoint R A ⟶ V) :
    (baseChange (algebraBaseMap R A)).map i ≫ torusConjugateAlgebraHom A j F t a =
      (baseChange (algebraBaseMap R A)).map i ≫
        (baseChange (algebraBaseMap R A)).map F := by
  apply hom_ext_points
  intro Z x
  change (x ≫ ((baseChange (algebraBaseMap R A)).map i).hom.hom) ≫
      (torusConjugateAlgebraHom A j F t a).hom.hom =
    (x ≫ ((baseChange (algebraBaseMap R A)).map i).hom.hom) ≫
      ((baseChange (algebraBaseMap R A)).map F).hom.hom
  apply (baseChangePointsEquiv (algebraBaseMap R A) H Z).injective
  rw [torusConjugateAlgebraHom_apply]
  simp only [baseChangePointsEquiv_comp]
  have hpoint (z : (Over.map (algebraBaseMap R A)).obj Z ⟶ K.X) :
      (z ≫ i.hom.hom) ≫ F.hom.hom = (z ≫ tau.hom.hom) ≫ j.hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun v : K ⟶ H => z ≫ v.hom.hom) hF
  simp only [hpoint]
  let p := (Over.map (algebraBaseMap R A)).map (toUnit Z) ≫ a ≫ t
  let q := baseChangePointsEquiv (algebraBaseMap R A) K Z x ≫ tau.hom.hom
  have hc : (p ≫ j.hom.hom) * (q ≫ j.hom.hom) * (p ≫ j.hom.hom)⁻¹ =
      q ≫ j.hom.hom := by
    calc
      _ = (p * q * p⁻¹) ≫ j.hom.hom := by
        rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
      _ = q ≫ j.hom.hom := by
        congr 1
        rw [mul_comm p q, mul_inv_cancel_right]
  simpa only [p, q, Category.assoc] using hc

/-- The conjugated map has the original torus restriction in the standard
coordinate-torus model over every algebra. -/
theorem torusConjugateAlgebraHom_torus
    {I : Type u} [Fintype I]
    (j : T.toGrp ⟶ H) (F : G ⟶ H) (t : V ⟶ T.X)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (tau : splitTorus (Spec (CommRingCat.of R)) I ⟶ T.toGrp)
    (hF : i ≫ F = tau ≫ j)
    (A : Type u) [CommRing A] [Algebra R A] (a : fieldPoint R A ⟶ V) :
    splitTorus.baseChangeHom (K := A) G I i ≫ torusConjugateAlgebraHom A j F t a =
      splitTorus.baseChangeHom (K := A) G I i ≫
        (baseChange (algebraBaseMap R A)).map F := by
  change ((splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
    (baseChange (algebraBaseMap R A)).map i) ≫ _ =
    ((splitTorus.baseChangeIso (algebraBaseMap R A) I).inv ≫
      (baseChange (algebraBaseMap R A)).map i) ≫ _
  rw [Category.assoc, Category.assoc,
    torusConjugateAlgebraHom_comp j F t i tau hF A a]

end Langlands.GroupScheme
