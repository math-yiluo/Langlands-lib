import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle
import Langlands.AlgebraicGeometry.Picard.PoincareDiagonalClasses
import Langlands.AbelianScheme.Multiplication

/-! # Symmetry of the canonical cubic bundle under inversion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (IsoClasses isoClass pullbackHom)

section Poincare

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)
variable (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (stability : PicardZeroPullbackStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- The Poincaré class at the identity point of the dual is trivial. -/
lemma familyPointClass_poincareFamily_one_left {Z : Over S} (x : Z ⟶ A.X) :
    familyPointClass preservation A (poincareFamily A hA) (1 : Z ⟶ (DA).X) x = 1 := by
  have h := familyPointClass_poincareFamily_mul_left preservation A hA geometryA MA evaluationA
    stability composition unitCoherence associativity comparison symmetry
    (1 : Z ⟶ (DA).X) 1 x
  rw [mul_one] at h
  exact left_eq_mul.mp h

/-- Poincaré classes invert when the point of the dual is inverted. -/
lemma familyPointClass_poincareFamily_inv_left {Z : Over S} (u : Z ⟶ (DA).X)
    (x : Z ⟶ A.X) :
    familyPointClass preservation A (poincareFamily A hA) (u⁻¹ : Z ⟶ (DA).X) x =
      (familyPointClass preservation A (poincareFamily A hA) u x)⁻¹ := by
  have h := familyPointClass_poincareFamily_mul_left preservation A hA geometryA MA evaluationA
    stability composition unitCoherence associativity comparison symmetry
    (u⁻¹ : Z ⟶ (DA).X) u x
  rw [inv_mul_cancel, familyPointClass_poincareFamily_one_left preservation A hA geometryA MA
    evaluationA stability composition unitCoherence associativity comparison symmetry] at h
  exact eq_inv_of_mul_eq_one_left h.symm

include stability in
/-- The Poincaré class at the identity point of `A` is trivial. -/
lemma familyPointClass_poincareFamily_one_right {Z : Over S} (z : Z ⟶ dualScheme A hA) :
    familyPointClass preservation A (poincareFamily A hA) z (1 : Z ⟶ A.X) = 1 := by
  have h := familyPointClass_poincareFamily_mul_right preservation A hA stability z
    (1 : Z ⟶ A.X) 1
  rw [mul_one] at h
  exact left_eq_mul.mp h

include stability in
/-- Poincaré classes invert when the point of `A` is inverted. -/
lemma familyPointClass_poincareFamily_inv_right {Z : Over S} (z : Z ⟶ dualScheme A hA)
    (x : Z ⟶ A.X) :
    familyPointClass preservation A (poincareFamily A hA) z x⁻¹ =
      (familyPointClass preservation A (poincareFamily A hA) z x)⁻¹ := by
  have h := familyPointClass_poincareFamily_mul_right preservation A hA stability z x⁻¹ x
  rw [inv_mul_cancel, familyPointClass_poincareFamily_one_right preservation A hA stability]
    at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- Poincaré classes are unchanged when both points are inverted. -/
lemma familyPointClass_poincareFamily_inv_inv {Z : Over S} (u : Z ⟶ (DA).X)
    (x : Z ⟶ A.X) :
    familyPointClass preservation A (poincareFamily A hA) (u⁻¹ : Z ⟶ (DA).X) x⁻¹ =
      familyPointClass preservation A (poincareFamily A hA) u x :=
  calc familyPointClass preservation A (poincareFamily A hA) (u⁻¹ : Z ⟶ (DA).X) x⁻¹
      = (familyPointClass preservation A (poincareFamily A hA) (u⁻¹ : Z ⟶ (DA).X) x)⁻¹ :=
        familyPointClass_poincareFamily_inv_right preservation A hA stability _ x
    _ = ((familyPointClass preservation A (poincareFamily A hA) u x)⁻¹)⁻¹ :=
        congrArg (·⁻¹) (familyPointClass_poincareFamily_inv_left preservation A hA geometryA MA
          evaluationA stability composition unitCoherence associativity comparison symmetry u x)
    _ = familyPointClass preservation A (poincareFamily A hA) u x := inv_inv _

/-- For a homomorphism `λ : A → A^∨`, the diagonal Poincaré bundle `(1, λ)^* P` has the same
isomorphism class as its pullback by multiplication by `-1`. -/
theorem isoClass_pullback_neg_poincareDiagonalBundle (lam : A.toGrp ⟶ (DA).toGrp) :
    isoClass preservation ((LineBundle.pullback
        (GroupScheme.multiplication A.toGrp (-1)).hom.hom.left).obj
          (poincareDiagonalBundle A hA lam.hom.hom)) =
      isoClass preservation (poincareDiagonalBundle A hA lam.hom.hom) := by
  have h1 := isoClass_pullback_poincareDiagonalBundle preservation A hA lam.hom.hom
    (GroupScheme.multiplication A.toGrp (-1)).hom.hom
  have h2 := isoClass_pullback_poincareDiagonalBundle preservation A hA lam.hom.hom (𝟙 A.X)
  rw [Over.id_left, ← LineBundle.pullbackHom_isoClass, LineBundle.pullbackHom_id] at h2
  have hm : (GroupScheme.multiplication A.toGrp (-1)).hom.hom = (𝟙 A.X)⁻¹ := by
    rw [GroupScheme.multiplication_hom, zpow_neg_one]
  have hl : (𝟙 A.X)⁻¹ ≫ lam.hom.hom = ((𝟙 A.X ≫ lam.hom.hom)⁻¹ : A.X ⟶ (DA).X) :=
    GrpObj.inv_comp _ _
  rw [h1, h2]
  refine Eq.trans ?_ (familyPointClass_poincareFamily_inv_inv preservation A hA geometryA MA
    evaluationA stability composition unitCoherence associativity comparison symmetry
    (𝟙 A.X ≫ lam.hom.hom) (𝟙 A.X))
  exact congrArg₂ (fun z x => familyPointClass preservation A (poincareFamily A hA) z x)
    (by rw [hm]; exact hl) hm

end Poincare

namespace PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- The canonical bundle of a datum has the same isomorphism class as its pullback by
multiplication by `-1`. -/
theorem Datum.isoClass_pullback_neg_canonicalBundle (a : Datum P S g d n) :
    isoClass P.preservation ((LineBundle.pullback
        (GroupScheme.multiplication a.abelian.toGrp (-1)).hom.hom.left).obj
          a.canonicalBundle) =
      isoClass P.preservation a.canonicalBundle :=
  isoClass_pullback_neg_poincareDiagonalBundle P.preservation a.abelian a.dualWitness.hasDual
    a.dualWitness.geometry a.dualWitness.inverseBundle a.dualWitness.evaluation P.stability
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    (groupHom a.polarization)

/-- **The cubic bundle is symmetric.** An isomorphism from the pullback of the cubic bundle
of a datum by multiplication by `-1` to the cubic bundle: the cube of a chosen isomorphism
`[-1]^*L ≅ L` for the canonical bundle `L`, composed with the comparison of the pullback
of a cube with the cube of the pullback. -/
def Datum.pullbackNegCubicBundleIso (a : Datum P S g d n) :
    (Scheme.Modules.pullback
        (GroupScheme.multiplication a.abelian.toGrp (-1)).hom.hom.left).obj
          a.cubicBundle.obj ≅ a.cubicBundle.obj :=
  actualPullbackTensorPowIso _ a.canonicalBundle.obj 3 ≪≫
    tensorPowIso ((LineBundle.forget _).mapIso
      (LineBundle.isoClass_eq_iff.mp a.isoClass_pullback_neg_canonicalBundle).some) 3

/-- Pulling the cubic bundle of a datum back by multiplication by `-1` gives a sheaf
isomorphic to the cubic bundle. -/
theorem Datum.nonempty_pullback_neg_cubicBundle_iso (a : Datum P S g d n) :
    Nonempty ((Scheme.Modules.pullback
        (GroupScheme.multiplication a.abelian.toGrp (-1)).hom.hom.left).obj
          a.cubicBundle.obj ≅ a.cubicBundle.obj) :=
  ⟨a.pullbackNegCubicBundleIso⟩

end PolarizedFiniteLevel

end Langlands.AbelianScheme
