import Langlands.GroupScheme.RelativeUnipotent.FreeBundleMatrices
import Langlands.GroupScheme.VectorWeightLinearity

/-! # Actual module isomorphisms from positive-weight vector-group isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.LinearFreeBundleIso

open VectorGroup FreeBundleMatrices

/-- The rectangular matrices of a linear equivalence and its actual inverse multiply to one. -/
lemma inverse_matrices {R : Type u} [CommRing R] {n m : ℕ}
    (L : (Fin n → R) ≃ₗ[R] (Fin m → R)) :
    LinearMap.toMatrix' L.symm.toLinearMap * LinearMap.toMatrix' L.toLinearMap = 1 ∧
      LinearMap.toMatrix' L.toLinearMap * LinearMap.toMatrix' L.symm.toLinearMap = 1 := by
  constructor
  · rw [← LinearMap.toMatrix'_comp]
    have he : L.symm.toLinearMap.comp L.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact L.symm_apply_apply x
    rw [he, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    have he : L.toLinearMap.comp L.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact L.apply_symm_apply x
    rw [he, LinearMap.toMatrix'_id]

variable {R : CommRingCat.{u}} {n m d : ℕ}
  (e : VectorGroup.groupScheme R n ≅ VectorGroup.groupScheme R m)
  (hd : 0 < d) (he : HasScalarWeight (pointTransformation e.hom) d)

/-- The original weight matrix is exactly the matrix of the derived actual
base-ring linear equivalence. -/
lemma weightMatrix_eq_linearEquiv :
    weightMatrix (pointTransformation e.hom) =
      LinearMap.toMatrix'
        (linearEquivOfWeight e hd he (CommAlgCat.of R R)).toLinearMap := by
  ext i j
  rfl

/-- A positive common scalar weight on an actual vector-group isomorphism
constructs an actual isomorphism of the original free module sheaves. -/
def moduleIso : freeBundle (Spec R) n ≅ freeBundle (Spec R) m := by
  let L := linearEquivOfWeight e hd he (CommAlgCat.of R R)
  let M := LinearMap.toMatrix' L.toLinearMap
  let N := LinearMap.toMatrix' L.symm.toLinearMap
  let φ := (Scheme.ΓSpecIso R).inv.hom
  exact isoOfMatrices (M.map φ) (N.map φ)
    (by rw [← Matrix.map_mul, (inverse_matrices L).1,
      Matrix.map_one φ (map_zero φ) (map_one φ)])
    (by rw [← Matrix.map_mul, (inverse_matrices L).2,
      Matrix.map_one φ (map_zero φ) (map_one φ)])

/-- The constructed forward module map uses the original quotient map's
matrix, with the actual Spec/global-section coefficient comparison. -/
lemma moduleIso_hom :
    (moduleIso e hd he).hom =
      homOfMatrix ((weightMatrix (pointTransformation e.hom)).map
        (Scheme.ΓSpecIso R).inv.hom) := by
  change homOfMatrix _ = homOfMatrix _
  rw [weightMatrix_eq_linearEquiv e hd he]

/-- The actual original group isomorphism and the constructed module
isomorphism have identical canonical section coordinates on all scheme tests. -/
lemma moduleIso_sections (T : Over (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R n).X) :
    (freeVectorBundlePoints R m T (x ≫ e.hom.hom.hom)).toAdd =
      ((Scheme.Modules.pullback T.hom).map (moduleIso e hd he).hom).app ⊤
        (freeVectorBundlePoints R n T x).toAdd := by
  rw [moduleIso_hom]
  conv_lhs => rw [VectorGroup.eq_matrixHom_of_hasScalarWeight e.hom hd he]
  exact vectorGroup_matrixHom_sections _ T x

end Langlands.GroupScheme.RelativeUnipotent.LinearFreeBundleIso
