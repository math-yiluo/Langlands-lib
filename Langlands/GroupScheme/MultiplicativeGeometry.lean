import Langlands.GroupScheme.MultiplicativeLaurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.FiniteType

/-! # Geometry and scalar points of the actual multiplicative group -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm

universe u

instance relativeLaurent_locallyOfFiniteType (R : CommRingCat.{u}) :
    LocallyOfFiniteType (relativeLaurent R).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := R))))
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  change (algebraMap R (LaurentPolynomial R)).FiniteType
  rw [RingHom.finiteType_algebraMap]
  infer_instance

/-- The structural morphism of the actual Gm over an affine base is locally of finite type. -/
instance locallyOfFiniteType (R : CommRingCat.{u}) :
    LocallyOfFiniteType (GroupScheme.Gm (Spec R)).X.hom := by
  rw [← Over.w (relativeLaurentIso R).hom]
  infer_instance

/-- Over a field, the actual Gm is a reduced scheme. -/
instance isReduced_field (k : Type u) [Field k] :
    IsReduced (GroupScheme.Gm (Spec (CommRingCat.of k))).X.left := by
  have : IsReduced (relativeLaurent (CommRingCat.of k)).left := by
    change IsReduced (Spec (CommRingCat.of (LaurentPolynomial k)))
    infer_instance
  exact isReduced_of_isOpenImmersion (relativeLaurentIso (CommRingCat.of k)).hom.left

/-- The actual Gm point corresponding to a scalar unit by the published affine equivalence. -/
def scalarPoint (R : CommRingCat.{u}) (a : Rˣ) :
    Over.mk (𝟙 (Spec R)) ⟶ (GroupScheme.Gm (Spec R)).X :=
  (affinePointsEquiv (𝟙 (Spec R))).symm a

@[simp]
lemma affinePointsEquiv_scalarPoint (R : CommRingCat.{u}) (a : Rˣ) :
    affinePointsEquiv (𝟙 (Spec R)) (scalarPoint R a) = a :=
  (affinePointsEquiv (𝟙 (Spec R))).apply_symm_apply a

@[simp]
lemma scalarPoint_affinePointsEquiv (R : CommRingCat.{u})
    (x : Over.mk (𝟙 (Spec R)) ⟶ (GroupScheme.Gm (Spec R)).X) :
    scalarPoint R (affinePointsEquiv (𝟙 (Spec R)) x) = x :=
  (affinePointsEquiv (𝟙 (Spec R))).symm_apply_apply x

/-- Into a separated k-scheme, morphisms from the actual Gm are determined by k-points. -/
lemma hom_ext_kpoints {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
    {f g : (GroupScheme.Gm (Spec (CommRingCat.of k))).X ⟶ Y}
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (GroupScheme.Gm (Spec (CommRingCat.of k))).X, x ≫ f = x ≫ g) : f = g := by
  let X := (GroupScheme.Gm (Spec (CommRingCat.of k))).X
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq f.left g.left Y.hom (closedPoints X.left) ?_ ?_ ?_
  · rw [dense_iff_closure_eq]
    exact closure_closedPoints
  · intro x hx
    let p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
    have hp := congrArg (fun q => q.left) (h p)
    change (Spec.map (residueFieldIsoBase X.hom x hx).hom ≫ X.left.fromSpecResidueField x) ≫
        f.left =
      (Spec.map (residueFieldIsoBase X.hom x hx).hom ≫ X.left.fromSpecResidueField x) ≫
        g.left at hp
    apply (cancel_epi (Spec.map (residueFieldIsoBase X.hom x hx).hom)).mp
    simpa only [Category.assoc] using hp
  · exact (Over.w f).trans (Over.w g).symm

/-- Equality of morphisms from Gm can be checked on the published scalar-unit points. -/
lemma hom_ext_scalarUnits {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Over (Spec (CommRingCat.of k))} [IsSeparated Y.hom]
    {f g : (GroupScheme.Gm (Spec (CommRingCat.of k))).X ⟶ Y}
    (h : ∀ a : kˣ, scalarPoint (CommRingCat.of k) a ≫ f =
      scalarPoint (CommRingCat.of k) a ≫ g) : f = g := by
  apply hom_ext_kpoints
  intro x
  have hx := scalarPoint_affinePointsEquiv (CommRingCat.of k) x
  rw [← hx]
  exact h _

/-- Actual cocharacters into a separated group scheme agree if all scalar evaluations agree. -/
lemma cocharacter_ext_scalarUnits {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated G.X.hom]
    {f g : (GroupScheme.Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
    (h : ∀ a : kˣ, scalarPoint (CommRingCat.of k) a ≫ f.hom.hom =
      scalarPoint (CommRingCat.of k) a ≫ g.hom.hom) : f = g := by
  apply Grp.hom_ext
  exact hom_ext_scalarUnits h

end Langlands.GroupScheme.Gm
