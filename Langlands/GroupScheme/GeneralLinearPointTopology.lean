import Langlands.GroupScheme.AffinePointTopology
import Langlands.GroupScheme.GeneralLinear
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Actual general linear points and the matrix-units topology -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

set_option backward.isDefEq.respectTransparency false

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u})
  (S : CommAlgCat.{u} R)

/-- Actual regular-function evaluation gives the corresponding matrix entry. -/
theorem affinePointsEquiv_entry_evaluation
    (x : (groupScheme n R).affinePoints S) (i j : n) :
    affinePointsEquiv n R S x i j =
      (groupScheme n R).affinePointEvaluation S x (entrySection n R i j) := by
  have h := congrArg (fun g : GL n Γ(Spec (CommRingCat.of S), ⊤) =>
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (g i j))
    (pointsEquiv_eq_affinePointsEquiv S x)
  rw [pointsEquiv_apply_apply, Matrix.GeneralLinearGroup.map_apply,
    Corepresented.affineSectionsIso_inv_ringHom] at h
  exact (h.trans (congrArg (fun f : CommRingCat.of S ⟶ CommRingCat.of S =>
    f.hom (affinePointsEquiv n R S x i j))
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv_hom_id)).symm

/-- The inverse regular coordinate gives the corresponding inverse-matrix entry. -/
theorem affinePointsEquiv_inverseEntry_evaluation
    (x : (groupScheme n R).affinePoints S) (i j : n) :
    (affinePointsEquiv n R S x)⁻¹ i j =
      (groupScheme n R).affinePointEvaluation S x (inverseEntrySection n R i j) := by
  have h := congrArg (fun g : GL n Γ(Spec (CommRingCat.of S), ⊤) =>
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (g⁻¹ i j))
    (pointsEquiv_eq_affinePointsEquiv S x)
  rw [pointsEquiv_inv_apply] at h
  change (groupScheme n R).affinePointEvaluation S x (inverseEntrySection n R i j) =
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
        ((affinePointsEquiv n R S x)⁻¹ i j)) at h
  exact (h.trans (congrArg (fun f : CommRingCat.of S ⟶ CommRingCat.of S =>
    f.hom ((affinePointsEquiv n R S x)⁻¹ i j))
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv_hom_id)).symm

variable [TopologicalSpace S]

/-- The affine point comparison is continuous for the actual matrix-units topology. -/
theorem continuous_affinePointsEquiv : Continuous (affinePointsEquiv n R S) := by
  rw [Units.continuous_iff]
  constructor
  · apply continuous_matrix
    intro i j
    change Continuous (fun x : (groupScheme n R).affinePoints S =>
      affinePointsEquiv n R S x i j)
    simp_rw [affinePointsEquiv_entry_evaluation]
    exact (groupScheme n R).continuous_affinePointEvaluation S _
  · apply continuous_matrix
    intro i j
    change Continuous (fun x : (groupScheme n R).affinePoints S =>
      (affinePointsEquiv n R S x)⁻¹ i j)
    simp_rw [affinePointsEquiv_inverseEntry_evaluation]
    exact (groupScheme n R).continuous_affinePointEvaluation S _

variable [IsTopologicalRing S]

/-- Every fixed coordinate-algebra element is a continuous function of an invertible matrix. -/
theorem continuous_classify (a : CoordinateRing n R) :
    Continuous (fun g : GL n S => classify (R := R) g a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Continuous (fun g : GL n S => classify g (quotient n R p))
  simp_rw [classify_quotient]
  induction p using MvPolynomial.induction_on with
  | C r =>
      simpa only [aeval_C] using
        (continuous_const : Continuous (fun _ : GL n S => algebraMap R S r))
  | add p q hp hq =>
      simpa only [map_add] using hp.fun_add hq
  | mul_X p i hp =>
      rw [show (fun g : GL n S => aeval (values g) (p * X i)) =
        (fun g => aeval (values g) p * values g i) by funext g; rw [map_mul, aeval_X]]
      apply hp.fun_mul
      cases i with
      | entry i j =>
          exact (continuous_apply j).comp
            (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id i)
      | inverseEntry i j =>
          exact (continuous_apply j).comp
            (Matrix.GeneralLinearGroup.continuous_apply _ continuous_inv i)

omit [TopologicalSpace S] [IsTopologicalRing S] in
/-- Evaluating a spectrum point applies its algebra map to the global coordinate. -/
theorem affinePointEvaluation_map_classify (g : GL n S)
    (a : Γ((groupScheme n R).X.left, ⊤)) :
    (groupScheme n R).affinePointEvaluation S
      ((algSpec R).map (CommAlgCat.ofHom (classify (R := R) g)).op) a =
        classify g ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing n R))).hom a) := by
  change (((Spec.map (CommRingCat.ofHom (classify (R := R) g).toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom) a) = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- The inverse point comparison is continuous by polynomial evaluation in entries
and inverse entries. -/
theorem continuous_affinePointsEquiv_symm :
    Continuous (affinePointsEquiv n R S).symm := by
  apply ((groupScheme n R).continuous_affinePoints_iff S _).mpr
  intro a
  change Continuous (fun g : GL n S =>
    (groupScheme n R).affinePointEvaluation S ((affinePointsEquiv n R S).symm g) a)
  simp_rw [affinePointsEquiv_symm_apply, affinePointEvaluation_map_classify]
  exact continuous_classify n R S _

/-- The actual affine points of GL are the existing matrix unit group, with its topology. -/
def affinePointsHomeomorph : (groupScheme n R).affinePoints S ≃ₜ* GL n S where
  toMulEquiv := affinePointsEquiv n R S
  continuous_toFun := continuous_affinePointsEquiv n R S
  continuous_invFun := continuous_affinePointsEquiv_symm n R S

@[simp] theorem affinePointsHomeomorph_apply (x : (groupScheme n R).affinePoints S) :
    affinePointsHomeomorph n R S x = affinePointsEquiv n R S x := rfl

end Langlands.GroupScheme.GeneralLinear
