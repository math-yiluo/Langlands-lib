import Langlands.GroupScheme.OddOrthogonalMatrix.TangentEquivalence

/-! # Exact affine formulas for the odd subgroup constructions -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution Quaternionic.ScalarMatrixCoordinates

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

/-- The affine coefficient matrix is the all-test matrix transported along
the canonical global-sections isomorphism of the affine test. -/
theorem affineMatrix_val_eq_ambientMatrix_map (A : CommAlgCat.{u} (CommRingCat.of K))
    (z : (algSpec (CommRingCat.of K)).obj (op A) ⟶ (groupScheme l K).X) :
    (affineMatrix K A z : Matrix (Index l) (Index l) A) =
      (ambientMatrix K ((algSpec (CommRingCat.of K)).obj (op A))
        (z ≫ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom)).map
          (Corepresented.affineSectionsIso A).hom.hom := by
  rw [affineMatrix_val]
  have h := Corepresented.map_affineSectionsIso_pointsEquiv
    (FiniteAlgebraUnits.functor K (Matrix (Index l) (Index l) K))
    (FiniteAlgebraUnits.corepresentableBy (Module.finBasis K (Matrix (Index l) (Index l) K))) A
    (z ≫ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom)
  change Units.map (Algebra.TensorProduct.map (Corepresented.affineSectionsIso A).hom.hom
    (AlgHom.id K (Matrix (Index l) (Index l) K))).toMonoidHom
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix (Index l) (Index l) K))
        ((algSpec (CommRingCat.of K)).obj (op A))
          (z ≫ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom)) =
    FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix (Index l) (Index l) K)) A
      (z ≫ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom) at h
  rw [← h]
  exact matrixEquiv_naturality K _ _

/-- The actual affine additive point with the sole coordinate equal to `c`. -/
def additiveAffinePoint (A : CommAlgCat.{u} (CommRingCat.of K)) (c : A) :
    (algSpec (CommRingCat.of K)).obj (op A) ⟶
      (VectorGroup.groupScheme (CommRingCat.of K) 1).X :=
  (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of K) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of K) 1) A).symm
      (Multiplicative.ofAdd (fun _ : Fin 1 => c))

/-- The global coordinate of the affine additive point transports to `c`. -/
theorem additiveAffinePoint_coordinate (A : CommAlgCat.{u} (CommRingCat.of K)) (c : A) :
    (Corepresented.affineSectionsIso A).hom.hom
      ((VectorGroup.coordinates (CommRingCat.of K) 1
        ((algSpec (CommRingCat.of K)).obj (op A)) (additiveAffinePoint K A c)).toAdd 0) = c := by
  have h := Corepresented.map_affineSectionsIso_pointsEquiv
    (VectorGroup.functor (CommRingCat.of K) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of K) 1) A (additiveAffinePoint K A c)
  rw [additiveAffinePoint, MulEquiv.apply_symm_apply] at h
  exact congrArg (fun v : Multiplicative (Fin 1 → A) => v.toAdd 0) h

/-- The short subgroup has its original parameter matrix over every affine
coefficient algebra. -/
theorem affineMatrix_shortMap (A : CommAlgCat.{u} (CommRingCat.of K)) (a : l ⊕ l) (c : A) :
    affineMatrix K A (additiveAffinePoint K A c ≫ (shortMap K a).hom.hom) =
      shortUnits a (Multiplicative.ofAdd c) := by
  apply Units.ext
  rw [affineMatrix_val_eq_ambientMatrix_map, Category.assoc, ← Grp.comp_hom_hom,
    shortMap_comp, ambientMatrix_ambientShortMap]
  change (shortMatrix a ((VectorGroup.coordinates (CommRingCat.of K) 1
    ((algSpec (CommRingCat.of K)).obj (op A)) (additiveAffinePoint K A c)).toAdd 0)).map
      (Corepresented.affineSectionsIso A).hom.hom.toRingHom = shortMatrix a c
  erw [shortMatrix_map, additiveAffinePoint_coordinate]

/-- The even points comparison agrees with its original affine coefficient algebra. -/
theorem evenAffinePoints_sections (A : CommAlgCat.{u} (CommRingCat.of K))
    (z : (algSpec (CommRingCat.of K)).obj (op A) ⟶
      (OrthogonalMatrix.groupScheme l (CommRingCat.of K)).X) :
    OrthogonalMatrix.map l (Corepresented.affineSectionsIso A).hom.hom.toRingHom
      (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K)
        ((algSpec (CommRingCat.of K)).obj (op A)) z) =
      OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K) A z :=
  Corepresented.map_affineSectionsIso_pointsEquiv (OrthogonalMatrix.functor l (CommRingCat.of K))
    (OrthogonalMatrix.corepresentableBy l (CommRingCat.of K)) A z

/-- The determinant-corrected even inclusion has its prescribed block matrix
over the original affine coefficient algebra. -/
theorem affineMatrix_evenMap (A : CommAlgCat.{u} (CommRingCat.of K))
    (z : (algSpec (CommRingCat.of K)).obj (op A) ⟶
      (OrthogonalMatrix.groupScheme l (CommRingCat.of K)).X) :
    affineMatrix K A (z ≫ (evenMap (l := l) K).hom.hom) =
      evenUnits (OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K) A z) := by
  apply Units.ext
  rw [affineMatrix_val_eq_ambientMatrix_map, Category.assoc, ← Grp.comp_hom_hom,
    evenMap_comp, ambientMatrix_ambientEvenMap]
  change (evenBlock (OrthogonalMatrix.pointsEquiv l (CommRingCat.of K)
    ((algSpec (CommRingCat.of K)).obj (op A)) z)).map
      (Corepresented.affineSectionsIso A).hom.hom.toRingHom = _
  erw [evenBlock_map, evenAffinePoints_sections]
  rfl

end Langlands.GroupScheme.OddOrthogonalMatrix
