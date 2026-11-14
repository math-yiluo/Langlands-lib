import Langlands.Global.AdelicGaloisBoundedRootCompact
import Langlands.Global.AdelicOrbitHeightMinimum
import Langlands.Global.PrimitiveAdelicHeightInclusion
import Langlands.GroupScheme.Lie.PrimePowerFieldExtension

/-! # Representation matrices and orbit heights under Galois scalar extension

See the paired Markdown file for statements, provenance and proofs. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The scalar-extension map on norm-one points is coefficient extension `a ↦ 1 ⊗ a`,
followed by the canonical adelic tensor map. -/
theorem scalarExtensionNormOneMap_val_eq_tensor (g : normOneSubgroup F G) :
    (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) =
      (AffineWeil.unitBaseChange F L G).affinePointMap
        (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L))
        (affinePointsBaseChangeMulEquiv F L (L ⊗[F] Adeles F) G
          (G.affinePointMap (CommAlgCat.ofHom
            (Algebra.TensorProduct.includeRight : Adeles F →ₐ[F] L ⊗[F] Adeles F))
            (g : AdelicGroupPoints F G))) :=
  congrArg ((AffineWeil.unitBaseChange F L G).affinePointMap
      (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L)))
    (AffineWeil.unit_affinePoints F L G (CommAlgCat.of F (Adeles F)) (g : AdelicGroupPoints F G))

omit [NumberField F] [NumberField L] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The two base-change comparisons of affine points are inverse to each other. -/
theorem affineBaseChangeEquiv_affinePointsBaseChangeMulEquiv
    (A : Type u) [CommRing A] [Algebra F A] [Algebra L A] [IsScalarTower F L A]
    (p : G.affinePoints (CommAlgCat.of F A)) :
    Lie.affineBaseChangeEquiv F L G A (affinePointsBaseChangeMulEquiv F L A G p) = p := by
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left]
  exact (affinePointsBaseChangeMulEquiv_symm_left F L A G
    (affinePointsBaseChangeMulEquiv F L A G p)).symm.trans
      (congrArg (fun q => q.left) ((affinePointsBaseChangeMulEquiv F L A G).symm_apply_apply p))

variable {n : ℕ}

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The matrix of the base-changed representation at the tensor extension of an adelic
point is the entrywise adelic inclusion of the original matrix. -/
theorem affineMatrix_baseChange_tensor (ρ : MatrixRepresentation G (Fin n))
    (x : G.affinePoints (CommAlgCat.of F (Adeles F))) :
    (((ρ.baseChange (Spec.algebraMap F L)).affineMatrix (CommAlgCat.of L (Adeles L))
        ((AffineWeil.unitBaseChange F L G).affinePointMap
          (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L))
          (affinePointsBaseChangeMulEquiv F L (L ⊗[F] Adeles F) G
            (G.affinePointMap (CommAlgCat.ofHom
              (Algebra.TensorProduct.includeRight : Adeles F →ₐ[F] L ⊗[F] Adeles F)) x))) :
          GL (Fin n) (Adeles L)) : Matrix (Fin n) (Fin n) (Adeles L)) =
      ((ρ.affineMatrix (CommAlgCat.of F (Adeles F)) x : GL (Fin n) (Adeles F)) :
        Matrix (Fin n) (Fin n) (Adeles F)).map AdelicFunctoriality.adeleInclusion := by
  set y := affinePointsBaseChangeMulEquiv F L (L ⊗[F] Adeles F) G
    (G.affinePointMap (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight : Adeles F →ₐ[F] L ⊗[F] Adeles F)) x) with hy
  have h3 := (ρ.baseChange (Spec.algebraMap F L)).affineMatrix_naturality
    (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L)) y
  have h1 := MatrixRepresentation.affineMatrix_baseChange (k := F) (K := L) ρ
    (L ⊗[F] Adeles F) y
  rw [hy, affineBaseChangeEquiv_affinePointsBaseChangeMulEquiv] at h1
  have h2 := ρ.affineMatrix_naturality (CommAlgCat.ofHom
    (Algebra.TensorProduct.includeRight : Adeles F →ₐ[F] L ⊗[F] Adeles F)) x
  rw [affinePointMap_apply, h3]
  ext i j
  rw [Matrix.map_apply]
  change numberFieldAdeleTensorMap F L
    ((((ρ.baseChange (Spec.algebraMap F L)).affineMatrix
      (CommAlgCat.of L (L ⊗[F] Adeles F)) y : GL (Fin n) (L ⊗[F] Adeles F)) :
        Matrix (Fin n) (Fin n) (L ⊗[F] Adeles F)) i j) = _
  have h2' : ρ.affineMatrix (CommAlgCat.of F (L ⊗[F] Adeles F))
      (G.affinePointMap (CommAlgCat.ofHom
        (Algebra.TensorProduct.includeRight : Adeles F →ₐ[F] L ⊗[F] Adeles F)) x) =
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeRight : Adeles F →ₐ[F] L ⊗[F] Adeles F).toRingHom
        (ρ.affineMatrix (CommAlgCat.of F (Adeles F)) x) := h2
  rw [h1, h2', Matrix.GeneralLinearGroup.map_apply]
  change numberFieldAdeleTensorMap F L (1 ⊗ₜ[F] _) = _
  rw [numberFieldAdeleTensorMap_tmul, map_one, one_mul]

/-- The adelic representation matrix of the scalar extension of a norm-one point is the
entrywise adelic inclusion of the original adelic representation matrix. -/
theorem adelicMatrix_scalarExtensionNormOneMap (ρ : MatrixRepresentation G (Fin n))
    (g : normOneSubgroup F G) :
    ((adelicMatrix L (AffineWeil.unitBaseChange F L G) (ρ.baseChange (Spec.algebraMap F L))
        (scalarExtensionNormOneMap F L G g :
          AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) : AdelicGL L n) :
        Matrix (Fin n) (Fin n) (Adeles L)) =
      ((adelicMatrix F G ρ (g : AdelicGroupPoints F G) : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)).map AdelicFunctoriality.adeleInclusion := by
  rw [scalarExtensionNormOneMap_val_eq_tensor]
  exact affineMatrix_baseChange_tensor F L G ρ (g : AdelicGroupPoints F G)

/-- **Orbit heights under scalar extension.** For a nonzero rational vector `v`, the orbit
height over `L` of the scalar extension of a norm-one point, at the image of `v`, is the
`[L : F]`-th power of the orbit height over `F`. -/
theorem orbitHeight_scalarExtensionNormOneMap (ρ : MatrixRepresentation G (Fin n))
    {v : Fin n → F} (hv : v ≠ 0) (g : normOneSubgroup F G) :
    orbitHeight L (AffineWeil.unitBaseChange F L G) (ρ.baseChange (Spec.algebraMap F L))
        (fun i => algebraMap F L (v i))
        (scalarExtensionNormOneMap F L G g :
          AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) =
      orbitHeight F G ρ v (g : AdelicGroupPoints F G) ^ Module.finrank F L := by
  set M := ((adelicMatrix F G ρ (g : AdelicGroupPoints F G) : AdelicGL F n) :
    Matrix (Fin n) (Fin n) (Adeles F)) with hM
  set x : PrimitiveAdelicHeight.Vector F n := M *ᵥ PrimitiveAdelicHeight.rational F n v with hx
  have hprim : PrimitiveAdelicHeight.IsPrimitive F n x :=
    ⟨adelicMatrix F G ρ (g : AdelicGroupPoints F G), v, hv, rfl⟩
  have hvec : ((adelicMatrix L (AffineWeil.unitBaseChange F L G)
        (ρ.baseChange (Spec.algebraMap F L))
        (scalarExtensionNormOneMap F L G g :
          AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) : AdelicGL L n) :
        Matrix (Fin n) (Fin n) (Adeles L)) *ᵥ
        PrimitiveAdelicHeight.rational L n (fun i => algebraMap F L (v i)) =
      fun i => AdelicFunctoriality.adeleInclusion (x i) := by
    rw [adelicMatrix_scalarExtensionNormOneMap]
    funext i
    rw [hx, RingHom.map_mulVec]
    congr 1
    funext j
    exact (AdelicFunctoriality.adeleInclusion_diagonal (K := F) (L := L) (v j)).symm
  change PrimitiveAdelicHeight.height L n _ = PrimitiveAdelicHeight.height F n x ^ _
  rw [hvec]
  exact AdelicFunctoriality.height_adeleInclusion x
    (PrimitiveAdelicHeight.IsPrimitive.hasFiniteMulSupport F n hprim)

end Langlands.Global.AdelicGaloisUnit
