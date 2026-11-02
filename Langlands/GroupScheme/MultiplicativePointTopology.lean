import Langlands.GroupScheme.Multiplicative
import Langlands.GroupScheme.AffinePointTopology
import Mathlib.Topology.Algebra.Constructions

/-! # Actual multiplicative coefficient points and their units topology -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm

variable (R : CommRingCat.{u})

/-- The global unit represented by the identity point of the actual multiplicative group. -/
def universalUnit : (Γ((GroupScheme.Gm (Spec R)).X.left, ⊤))ˣ :=
  pointsEquiv (Spec R) (GroupScheme.Gm (Spec R)).X (𝟙 _)

/-- The existing affine Gm equivalence on the actual coefficient-point carrier. -/
def affineUnitsEquiv (A : CommAlgCat.{u} R) :
    GroupScheme.affinePoints (GroupScheme.Gm (Spec R)).toGrp A ≃* Aˣ :=
  affinePointsEquiv ((algSpec R).obj (op A)).hom

/-- Every coefficient point pulls the universal unit back to its associated coefficient unit. -/
theorem affineUnitsEquiv_eq_map (A : CommAlgCat.{u} R)
    (x : GroupScheme.affinePoints (GroupScheme.Gm (Spec R)).toGrp A) :
    affineUnitsEquiv R A x = Units.map
      (GroupScheme.affinePointEvaluation (GroupScheme.Gm (Spec R)).toGrp A x).toMonoidHom
        (universalUnit R) := by
  apply Units.ext
  have h := pointsEquiv_naturality (Spec R) x (𝟙 (GroupScheme.Gm (Spec R)).X)
  simp only [Category.comp_id] at h
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (pointsEquiv (Spec R) ((algSpec R).obj (op A)) x).val = _
  erw [h]
  rfl

/-- Coefficient extension is the ordinary map on coefficient units. -/
theorem affineUnitsEquiv_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (x : GroupScheme.affinePoints (GroupScheme.Gm (Spec R)).toGrp A) :
    affineUnitsEquiv R B (GroupScheme.affinePointMap (GroupScheme.Gm (Spec R)).toGrp f x) =
      Units.map f.hom.toRingHom.toMonoidHom (affineUnitsEquiv R A x) := by
  apply Units.ext
  simp only [affineUnitsEquiv_eq_map, Units.coe_map]
  exact GroupScheme.affinePointEvaluation_map (GroupScheme.Gm (Spec R)).toGrp f x (universalUnit R).val

variable (A : CommAlgCat.{u} R) [TopologicalSpace A]

/-- Both a unit and its inverse are regular functions, so the actual Gm point equivalence
is continuous into the units topology. -/
theorem continuous_affineUnitsEquiv : Continuous (affineUnitsEquiv R A) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun x => (affineUnitsEquiv R A x : A))
    simp_rw [affineUnitsEquiv_eq_map]
    exact GroupScheme.continuous_affinePointEvaluation (GroupScheme.Gm (Spec R)).toGrp
      A (universalUnit R).val
  · simp_rw [affineUnitsEquiv_eq_map, ← map_inv]
    exact GroupScheme.continuous_affinePointEvaluation (GroupScheme.Gm (Spec R)).toGrp
      A (universalUnit R).inv

/-- Actual coefficient Gm points map continuously and multiplicatively to coefficient units. -/
def affineUnits : GroupScheme.affinePoints (GroupScheme.Gm (Spec R)).toGrp A →ₜ* Aˣ where
  toMonoidHom := (affineUnitsEquiv R A).toMonoidHom
  continuous_toFun := continuous_affineUnitsEquiv R A

end Langlands.GroupScheme.Gm
