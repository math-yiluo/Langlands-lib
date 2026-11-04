import Langlands.GroupScheme.Dynamic.UnipotentGradedCoordinates
import Langlands.GroupScheme.AffinePointTopology
import Langlands.GroupScheme.Rational.PointTopology

/-! # The canonical topology on rational points in graded unipotent coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- On the corepresented model, evaluating a global section transported from the coordinate
algebra is evaluation of the coordinate. -/
theorem affinePointEvaluation_eq_coord {A : CommAlgCat.{u} R}
    (y : (groupScheme F e).affinePoints A) (b : B) :
    (groupScheme F e).affinePointEvaluation A y ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) =
      coord e (affinePointsEquiv F e A y) b := by
  obtain ⟨φ, rfl⟩ : ∃ φ : B ⟶ A, (algSpec R).map φ.op = y :=
    ⟨(algSpec.fullyFaithful.preimage y).unop, algSpec.fullyFaithful.map_preimage y⟩
  rw [affinePointsEquiv_map]
  change (((Spec.map (CommRingCat.ofHom φ.hom.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) = _
  rw [Scheme.ΓSpecIso_naturality]
  simp [coord]

/-- On the corepresented model, evaluating a global section is evaluating the corresponding
element of the coordinate algebra. -/
theorem affinePointEvaluation_eq_coord' {A : CommAlgCat.{u} R}
    (y : (groupScheme F e).affinePoints A) (c : Γ((groupScheme F e).X.left, ⊤)) :
    (groupScheme F e).affinePointEvaluation A y c =
      coord e (affinePointsEquiv F e A y) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom c) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : B ⟶ A, (algSpec R).map φ.op = y :=
    ⟨(algSpec.fullyFaithful.preimage y).unop, algSpec.fullyFaithful.map_preimage y⟩
  rw [affinePointsEquiv_map]
  change (((Spec.map (CommRingCat.ofHom φ.hom.toRingHom)).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom) c) = _
  rw [Scheme.ΓSpecIso_naturality]
  simp [coord]
  rfl

end Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme.Dynamic.GradedCoordinates

open Corepresented

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- Model points as a multiplicative equivalence. -/
def modelPointEquiv (A : CommAlgCat.{u} (CommRingCat.of k)) :
    G.affinePoints A ≃* (AffineCoordinates.functor G).obj A :=
  MulEquiv.ofBijective (modelPoint G A) ⟨modelPoint_injective G A, modelPoint_surjective G A⟩

@[simp] theorem modelPointEquiv_apply (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : G.affinePoints A) : modelPointEquiv G A x = modelPoint G A x := rfl

theorem modelPoint_modelPointEquiv_symm (A : CommAlgCat.{u} (CommRingCat.of k))
    (y : (AffineCoordinates.functor G).obj A) : modelPoint G A ((modelPointEquiv G A).symm y) = y :=
  (modelPointEquiv G A).apply_symm_apply y

theorem modelPointEquiv_symm_eq (A : CommAlgCat.{u} (CommRingCat.of k))
    (y : (AffineCoordinates.functor G).obj A) :
    (modelPointEquiv G A).symm y =
      (affinePointsEquiv _ _ A).symm y ≫ (AffineCoordinates.groupSchemeIso G).hom.hom.hom := by
  apply (modelPointEquiv G A).injective
  rw [MulEquiv.apply_symm_apply, modelPointEquiv_apply, modelPoint_apply, Category.assoc,
    iso_hom_inv_hom, Category.comp_id, MulEquiv.apply_symm_apply]

variable (A : CommAlgCat.{u} (CommRingCat.of k)) [TopologicalSpace A]

/-- Coordinates of model points are continuous on the points of `G`. -/
theorem continuous_coord_modelPoint (b : AffineCoordinates.algebra G) :
    letI := G.affinePointsTopologicalSpace A
    Continuous fun x : G.affinePoints A =>
      coord (AffineCoordinates.corepresentation G) (modelPoint G A x) b := by
  let _ := G.affinePointsTopologicalSpace A
  have h : ∀ x : G.affinePoints A,
      coord (AffineCoordinates.corepresentation G) (modelPoint G A x) b =
        G.affinePointEvaluation A x
          ((AffineCoordinates.groupSchemeIso G).inv.hom.hom.left.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of (AffineCoordinates.algebra G))).inv b)) := fun x => by
    rw [modelPoint_apply]
    exact (affinePointEvaluation_eq_coord _ _ b).symm
  exact (G.continuous_affinePointEvaluation A _).congr fun x => (h x).symm

/-- A map into model points with continuous coordinates gives a continuous map into the
points of `G`. -/
theorem continuous_modelPointEquiv_symm {T : Type*} [TopologicalSpace T]
    {f : T → (AffineCoordinates.functor G).obj A}
    (hf : ∀ b, Continuous fun t => coord (AffineCoordinates.corepresentation G) (f t) b) :
    letI := G.affinePointsTopologicalSpace A
    Continuous fun t => (modelPointEquiv G A).symm (f t) := by
  let _ := G.affinePointsTopologicalSpace A
  apply (G.continuous_affinePoints_iff A _).mpr
  intro a
  have h : ∀ t, G.affinePointEvaluation A ((modelPointEquiv G A).symm (f t)) a =
      coord (AffineCoordinates.corepresentation G) (f t)
        ((Scheme.ΓSpecIso (CommRingCat.of (AffineCoordinates.algebra G))).hom
          ((AffineCoordinates.groupSchemeIso G).hom.hom.hom.left.appTop a)) := fun t => by
    rw [modelPointEquiv_symm_eq]
    have := affinePointEvaluation_eq_coord' (AffineCoordinates.corepresentation G)
      ((affinePointsEquiv _ _ A).symm (f t))
      ((AffineCoordinates.groupSchemeIso G).hom.hom.hom.left.appTop a)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  exact (hf _).congr fun t => (h t).symm

end Langlands.GroupScheme.Dynamic.GradedCoordinates
