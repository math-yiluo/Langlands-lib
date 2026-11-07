import Langlands.GroupScheme.BinaryTensorNorm
import Langlands.GroupScheme.FiniteAlgebraBinaryDynamic
import Langlands.GroupScheme.CentralSimpleNormOne

/-! # Actual binary elementary maps in the canonical reduced-norm-one group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits.BinaryRoot

open FiniteAlgebraUnits

variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
  [FiniteDimensional k D] [Algebra.IsCentral k D] [IsSimpleRing D]

/-- The canonical basis used to represent the actual binary matrix-unit scheme. -/
abbrev matrixBasis := Module.finBasis k (Matrix (Fin 2) (Fin 2) D)

/-- The actual canonical binary reduced-norm-one group scheme. -/
abbrev groupScheme := normOne k (Matrix (Fin 2) (Fin 2) D)

instance inclusion_mono : Mono (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom :=
  inferInstanceAs (Mono (kernelι (reducedNormHom k (Matrix (Fin 2) (Fin 2) D))).hom.hom)

/-- On every relative test the actual norm character is the canonical binary tensor norm. -/
theorem reducedNormHom_matrix_points (T : Over (base k))
    (x : T ⟶ (CentralSimpleUnits.groupScheme k (Matrix (Fin 2) (Fin 2) D)).X) :
    Gm.pointsEquiv (base k) T
        (x ≫ (reducedNormHom k (Matrix (Fin 2) (Fin 2) D)).hom.hom) =
      FiniteAlgebraUnits.BinaryNorm.tensorNorm k D ((algΓ (CommRingCat.of k)).obj T).unop
        (MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) T x) := by
  rw [reducedNormHom_points]
  change _ = Langlands.CentralSimple.reducedNormUnits k (Matrix (Fin 2) (Fin 2) D) _
    ((Units.mapEquiv (MatrixPoints.coefficientEquiv (m := Fin 2) k D _).symm.toMulEquiv)
      ((Units.mapEquiv (MatrixPoints.coefficientEquiv (m := Fin 2) k D _).toMulEquiv)
        (pointsEquiv (matrixBasis k D) T x)))
  congr 1
  apply Units.ext
  exact ((MatrixPoints.coefficientEquiv (m := Fin 2) k D
    ((algΓ (CommRingCat.of k)).obj T).unop).symm_apply_apply _).symm

/-- A point whose actual binary tensor norm is one lifts to the actual kernel. -/
def liftPoint {T : Over (base k)}
    (x : T ⟶ (CentralSimpleUnits.groupScheme k (Matrix (Fin 2) (Fin 2) D)).X)
    (hx : FiniteAlgebraUnits.BinaryNorm.tensorNorm k D
      ((algΓ (CommRingCat.of k)).obj T).unop
      (MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) T x) = 1) :
    T ⟶ (groupScheme k D).X :=
  (kernel_isPullback (reducedNormHom k (Matrix (Fin 2) (Fin 2) D))).lift x (toUnit T) (by
    change x ≫ (reducedNormHom k (Matrix (Fin 2) (Fin 2) D)).hom.hom = 1
    apply (Gm.pointsEquiv (base k) T).injective
    rw [map_one]
    exact (reducedNormHom_matrix_points k D T x).trans hx)

/-- The lift has precisely its original matrix-unit point as image. -/
@[simp] theorem liftPoint_ι {T : Over (base k)}
    (x : T ⟶ (CentralSimpleUnits.groupScheme k (Matrix (Fin 2) (Fin 2) D)).X) (hx) :
    liftPoint k D x hx ≫ (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom = x :=
  (kernel_isPullback (reducedNormHom k (Matrix (Fin 2) (Fin 2) D))).lift_fst _ _ _

section LiftHom

variable {H : GroupScheme (base k)}
    (f : H ⟶ CentralSimpleUnits.groupScheme k (Matrix (Fin 2) (Fin 2) D))
    (hf : ∀ (T : Over (base k)) (x : T ⟶ H.X),
      FiniteAlgebraUnits.BinaryNorm.tensorNorm k D ((algΓ (CommRingCat.of k)).obj T).unop
        (MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) T (x ≫ f.hom.hom)) = 1)

/-- The kernel lift on the group of points of each actual relative test. -/
def liftPoints (T : Over (base k)) : (T ⟶ H.X) →* (T ⟶ (groupScheme k D).X) where
  toFun x := liftPoint k D (x ≫ f.hom.hom) (hf T x)
  map_one' := by
    apply (cancel_mono (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom).mp
    rw [liftPoint_ι, MonObj.one_comp, MonObj.one_comp]
  map_mul' x y := by
    apply (cancel_mono (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom).mp
    simp only [liftPoint_ι, MonObj.mul_comp]

/-- The kernel point lifts commute with every change of relative test. -/
theorem liftPoints_naturality {T T' : Over (base k)} (a : T' ⟶ T) (x : T ⟶ H.X) :
    liftPoints k D f hf T' (a ≫ x) = a ≫ liftPoints k D f hf T x := by
  apply (cancel_mono (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom).mp
  change liftPoint k D ((a ≫ x) ≫ f.hom.hom) (hf T' (a ≫ x)) ≫
      (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom =
    (a ≫ liftPoint k D (x ≫ f.hom.hom) (hf T x)) ≫
      (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom
  simp only [Category.assoc, liftPoint_ι]

/-- Lift an actual group homomorphism when its tensor norm is one on every test. -/
def liftHom : H ⟶ groupScheme k D :=
  homOfPoints (liftPoints k D f hf) (liftPoints_naturality k D f hf)

/-- The lifted actual group map factors its original map through the kernel inclusion. -/
@[simp] theorem liftHom_ι :
    liftHom k D f hf ≫ normOneι k (Matrix (Fin 2) (Fin 2) D) = f := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, liftHom,
    comp_homOfPoints _ (liftPoints_naturality k D f hf)]
  exact liftPoint_ι k D (x ≫ f.hom.hom) (hf T x)

end LiftHom

variable {d : ℕ} (bD : Module.Basis (Fin d) k D)

/-- The entire actual elementary family has canonical reduced norm one on every test. -/
theorem elementaryMap_tensorNorm (neg : Bool) (T : Over (base k))
    (x : T ⟶ (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)).X) :
    FiniteAlgebraUnits.BinaryNorm.tensorNorm k D ((algΓ (CommRingCat.of k)).obj T).unop
      (MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) T
        (x ≫ (FiniteAlgebraUnits.BinaryRoot.elementaryMap k D bD (matrixBasis k D) neg).hom.hom)) = 1 := by
  rw [FiniteAlgebraUnits.BinaryRoot.tensorMatrixEquiv_elementaryMap]
  cases neg
  · exact FiniteAlgebraUnits.BinaryNorm.tensorNorm_upper k D _ _
  · exact FiniteAlgebraUnits.BinaryNorm.tensorNorm_lower k D _ _

/-- The actual upper or lower elementary map into the canonical reduced-norm-one group. -/
def elementaryMap (neg : Bool) :
    FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d) ⟶ groupScheme k D :=
  liftHom k D (FiniteAlgebraUnits.BinaryRoot.elementaryMap k D bD (matrixBasis k D) neg)
    (elementaryMap_tensorNorm k D bD neg)

/-- The lifted root is the original elementary map under the actual kernel inclusion. -/
@[simp] theorem elementaryMap_ι (neg : Bool) :
    elementaryMap k D bD neg ≫ normOneι k (Matrix (Fin 2) (Fin 2) D) =
      FiniteAlgebraUnits.BinaryRoot.elementaryMap k D bD (matrixBasis k D) neg :=
  liftHom_ι k D _ _

/-- The actual norm-one root has precisely its elementary tensor matrix on every test. -/
theorem tensorMatrixEquiv_elementaryMap (neg : Bool) (T : Over (base k))
    (x : T ⟶ (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)).X) :
    MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) T
      ((x ≫ (elementaryMap k D bD neg).hom.hom) ≫
        (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom) =
      FiniteAlgebraUnits.BinaryRoot.elementaryMatrix neg
        (FiniteAlgebraUnits.BinaryRoot.tensorCoordinates k D bD T x).toAdd := by
  rw [Category.assoc, ← Grp.comp_hom_hom, elementaryMap_ι]
  exact FiniteAlgebraUnits.BinaryRoot.tensorMatrixEquiv_elementaryMap k D bD (matrixBasis k D) neg T x

/-- Every elementary tensor matrix occurs in the included actual norm-one root image. -/
theorem exists_elementaryPoint (neg : Bool) (T : Over (base k))
    (a : ((algΓ (CommRingCat.of k)).obj T).unop ⊗[k] D) :
    ∃ x : T ⟶ (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)).X,
      MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) T
        ((x ≫ (elementaryMap k D bD neg).hom.hom) ≫
          (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom) =
        FiniteAlgebraUnits.BinaryRoot.elementaryMatrix neg a := by
  obtain ⟨x, hx⟩ := FiniteAlgebraUnits.BinaryRoot.tensorCoordinates_surjective k D bD T
    (Multiplicative.ofAdd a)
  refine ⟨x, ?_⟩
  rw [tensorMatrixEquiv_elementaryMap, hx]
  rfl

end Langlands.GroupScheme.CentralSimpleUnits.BinaryRoot
