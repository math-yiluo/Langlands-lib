import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.CorepresentedAffineComparison
import Mathlib.Topology.Algebra.Ring.Basic

/-! # The actual split-torus coordinates are a homeomorphism -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.GroupScheme.splitTorus

variable (I : Type u) [Fintype I] (R : CommRingCat.{u}) (A : CommAlgCat.{u} R)

theorem algHomEquiv_symm_single (x : I → Aˣ) (m : I →₀ ℤ) (r : R) :
    (algHomEquiv I R A).symm x (AddMonoidAlgebra.single m r) =
      algebraMap R A r * (↑(∏ i, x i ^ m i) : A) := by
  simp [algHomEquiv, AddMonoidAlgebra.lift_single, Finsupp.sum_fintype,
    Algebra.smul_def]

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_laurentClassify (a : LaurentAlgebra I R) :
    Continuous (fun x : I → Aˣ => (algHomEquiv I R A).symm x a) := by
  induction a using AddMonoidAlgebra.induction_on with
  | of m =>
      change Continuous (fun x : I → Aˣ =>
        (algHomEquiv I R A).symm x (AddMonoidAlgebra.single m 1))
      simp_rw [algHomEquiv_symm_single, map_one, one_mul]
      exact Units.continuous_val.comp
        (continuous_finsetProd _ fun i _ => (continuous_apply i).zpow _)
  | add a b ha hb => simpa only [map_add] using ha.fun_add hb
  | smul r a ha =>
      have h : (fun x : I → Aˣ => (algHomEquiv I R A).symm x (r • a)) =
          (fun x => algebraMap R A r * (algHomEquiv I R A).symm x a) := by
        funext x
        rw [Algebra.smul_def, map_mul, AlgHom.commutes]
      rw [h]
      exact continuous_const.fun_mul ha

/-- The affine Laurent point comparison, on actual coefficient points. -/
def laurentAffinePointsEquiv :
    (laurentGroupScheme I R).affinePoints A ≃* (I → Aˣ) :=
  Corepresented.affinePointsEquiv (unitsFunctor I R) (corepresentableBy I R) A

omit [Fintype I] [TopologicalSpace A] [IsTopologicalRing A] in
/-- Its inverse is the spectrum map of the Laurent classifying algebra map. -/
theorem laurentAffinePointsEquiv_symm_apply (x : I → Aˣ) :
    (laurentAffinePointsEquiv I R A).symm x =
      (algSpec R).map (CommAlgCat.ofHom ((algHomEquiv I R A).symm x)).op := by
  apply (laurentAffinePointsEquiv I R A).injective
  rw [MulEquiv.apply_symm_apply]
  change x = Corepresented.affinePointsEquiv (unitsFunctor I R)
    (corepresentableBy I R) A
      ((algSpec R).map (CommAlgCat.ofHom ((algHomEquiv I R A).symm x)).op)
  rw [Corepresented.affinePointsEquiv_map]
  exact ((algHomEquiv I R A).apply_symm_apply x).symm

omit [Fintype I] [TopologicalSpace A] [IsTopologicalRing A] in
/-- Spectrum evaluation is ordinary evaluation of the classifying Laurent algebra map. -/
theorem affinePointEvaluation_map_laurentClassify (x : I → Aˣ)
    (a : Γ((laurentGroupScheme I R).X.left, ⊤)) :
    (laurentGroupScheme I R).affinePointEvaluation A
      ((algSpec R).map (CommAlgCat.ofHom ((algHomEquiv I R A).symm x)).op) a =
        (algHomEquiv I R A).symm x
          ((Scheme.ΓSpecIso (CommRingCat.of (LaurentAlgebra I R))).hom a) := by
  change (((Spec.map (CommRingCat.ofHom
    ((algHomEquiv I R A).symm x).toRingHom)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom) a) = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- The Laurent classifier is continuous into the existing regular-evaluation topology. -/
theorem continuous_laurentAffinePointsEquiv_symm :
    Continuous (laurentAffinePointsEquiv I R A).symm := by
  apply ((laurentGroupScheme I R).continuous_affinePoints_iff A _).mpr
  intro a
  simp_rw [laurentAffinePointsEquiv_symm_apply, affinePointEvaluation_map_laurentClassify]
  exact continuous_laurentClassify I R A _

/-- The existing affine split-torus equivalence, on the actual coefficient-point carrier. -/
def affineUnitsEquiv : (splitTorus (Spec R) I).affinePoints A ≃* (I → Aˣ) :=
  affinePointsEquiv I ((algSpec R).obj (op A)).hom

omit [IsTopologicalRing A] in
/-- The existing split-torus coordinates are continuous, coordinate by coordinate. -/
theorem continuous_affinePointsEquiv :
    Continuous (affineUnitsEquiv I R A) := by
  apply continuous_pi
  intro i
  exact (Gm.continuous_affineUnitsEquiv R A).comp
    (GroupScheme.continuous_affinePointsTarget (splitTorus (Spec R) I) A
      (CategoryTheory.Limits.Pi.π (fun _ : I => (GroupScheme.Gm (Spec R)).toGrp) i))

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- The published Laurent isomorphism gives precisely the existing affine coordinates. -/
theorem laurentAffinePointsEquiv_laurentIso
    (x : (splitTorus (Spec R) I).affinePoints A) :
    laurentAffinePointsEquiv I R A (x ≫ (laurentIso I R).hom.hom.hom) =
      affineUnitsEquiv I R A x := by
  have hglobal := isoOfPointModels_hom
    (fun T : Over (Spec R) => I → (Γ(T.left, ⊤))ˣ)
    (fun a => unitsRestrict I a) (pointsEquiv I) (laurentPointsEquiv I R)
    (fun a x => pointsEquiv_naturality I a x)
    (fun a y => laurentPointsEquiv_naturality I R a y)
    ((algSpec R).obj (op A)) x
  change Corepresented.pointsEquiv (unitsFunctor I R) (corepresentableBy I R)
    ((algSpec R).obj (op A)) (x ≫ (laurentIso I R).hom.hom.hom) = _ at hglobal
  rw [Corepresented.pointsEquiv_eq_affinePointsEquiv] at hglobal
  funext i
  apply Units.ext
  have h := congrArg (fun y : I → (Γ(Spec (CommRingCat.of A), ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (y i).val) hglobal
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      ((laurentAffinePointsEquiv I R A (x ≫ (laurentIso I R).hom.hom.hom) i) : A)) =
        (affineUnitsEquiv I R A x i : A) at h
  exact (congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of A =>
    f.hom ((laurentAffinePointsEquiv I R A (x ≫ (laurentIso I R).hom.hom.hom) i) : A))
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id).symm.trans h

/-- Inverse split-torus coordinates are continuous for the existing point topology. -/
theorem continuous_affinePointsEquiv_symm :
    Continuous (affineUnitsEquiv I R A).symm := by
  have h : (affineUnitsEquiv I R A).symm =
      (fun x => (laurentAffinePointsEquiv I R A).symm x ≫
        (laurentIso I R).inv.hom.hom) := by
    funext x
    apply (affineUnitsEquiv I R A).injective
    rw [MulEquiv.apply_symm_apply, ← laurentAffinePointsEquiv_laurentIso]
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id, MulEquiv.apply_symm_apply]
  rw [h]
  exact (GroupScheme.continuous_affinePointPostcomp (laurentGroupScheme I R) A
    (laurentIso I R).inv.hom.hom).comp
      (continuous_laurentAffinePointsEquiv_symm I R A)

/-- The actual finite split torus is homeomorphic, multiplicatively, to coefficient units. -/
def affinePointsHomeomorph :
    (splitTorus (Spec R) I).affinePoints A ≃ₜ* (I → Aˣ) where
  toMulEquiv := affineUnitsEquiv I R A
  continuous_toFun := continuous_affinePointsEquiv I R A
  continuous_invFun := continuous_affinePointsEquiv_symm I R A

@[simp] theorem affinePointsHomeomorph_apply
    (x : (splitTorus (Spec R) I).affinePoints A) :
    affinePointsHomeomorph I R A x =
      affineUnitsEquiv I R A x := rfl

end Langlands.GroupScheme.splitTorus
