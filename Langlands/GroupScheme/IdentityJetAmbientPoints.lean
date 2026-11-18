import Langlands.GroupScheme.IdentityJetAffinePoint
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Dynamic.Representability

/-! # Actual ambient point coordinates and conjugation -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityJet

open AffineCoordinates Corepresented

variable {R : CommRingCat.{u}} {S : Scheme.{u}}
  (G : GroupScheme (Spec R)) [IsAffine G.X.left]
  (b : S ⟶ Spec R) {H : GroupScheme S}
  (h : H ⟶ (GroupScheme.baseChange b).obj G)

/-- An actual subgroup point, in the fixed ambient functor on its actual global sections. -/
def ambientFunctorPoint (T : Over S) (x : T ⟶ H.X) :
    (functor G).obj ((algΓ R).obj ((Over.map b).obj T)).unop :=
  pointsEquiv (functor G) (corepresentation G) ((Over.map b).obj T)
    (baseChangePointsEquiv b G T (x ≫ h.hom.hom) ≫ (groupSchemeIso G).inv.hom.hom)

/-- Test-scheme restriction is the actual map on the test's relative global sections. -/
theorem ambientFunctorPoint_naturality {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ H.X) :
    ambientFunctorPoint G b h T' (a ≫ x) =
      (functor G).map ((algΓ R).map ((Over.map b).map a)).unop
        (ambientFunctorPoint G b h T x) := by
  unfold ambientFunctorPoint
  rw [Category.assoc, baseChangePointsEquiv_naturality, Category.assoc,
    pointsEquiv_naturality]

/-- Its classifying algebra map is actual pullback of the fixed ambient functions. -/
theorem ambientFunctorPoint_coordinates (T : Over S) (x : T ⟶ H.X) (c : algebra G) :
    ((corepresentation G).homEquiv.symm (ambientFunctorPoint G b h T x)).hom c =
      (x.left ≫ ambientProjection G b h).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (algebra G))).inv c) := by
  rw [ambientFunctorPoint, homEquiv_symm_pointsEquiv_apply]
  change ((baseChangePointsEquiv b G T (x ≫ h.hom.hom)).left ≫
    (groupSchemeIso G).inv.hom.hom.left).appTop _ = _
  rw [baseChangePointsEquiv_left]
  simp only [Over.comp_left, ambientProjection, Category.assoc]
  rfl

/-- Actual inner conjugation becomes literal conjugation of the supplied functor points. -/
theorem ambientFunctorPoint_inner
    (g : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj G).X)
    (T : Over S) (x : T ⟶ H.X) :
    ambientFunctorPoint G b
        (h ≫ (((GroupScheme.baseChange b).obj G).innerIso g).hom) T x =
      ambientFunctorPoint G b (𝟙 ((GroupScheme.baseChange b).obj G)) T
          (((GroupScheme.baseChange b).obj G).constantPoint g T) *
        ambientFunctorPoint G b h T x *
          (ambientFunctorPoint G b (𝟙 ((GroupScheme.baseChange b).obj G)) T
            (((GroupScheme.baseChange b).obj G).constantPoint g T))⁻¹ := by
  unfold ambientFunctorPoint
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  simp only [map_mul, map_inv, MonObj.mul_comp, GrpObj.inv_comp,
    Grp.id_hom_hom, Category.comp_id]

end Langlands.GroupScheme.IdentityJet
