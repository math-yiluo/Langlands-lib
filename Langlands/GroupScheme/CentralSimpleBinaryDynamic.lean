import Langlands.GroupScheme.CentralSimpleBinaryRoots
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Actual contracting cocharacters in the canonical binary norm-one group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits.BinaryRoot

open FiniteAlgebraUnits

variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
  [FiniteDimensional k D] [Algebra.IsCentral k D] [IsSimpleRing D]

/-- Both scalar diagonal orientations have tensor norm one on every coefficient algebra. -/
theorem contractingMatrix_tensorNorm (R : Type u) [CommRing R] [Algebra k R]
    (neg : Bool) (t : Rˣ) :
    BinaryNorm.tensorNorm k D R
      (FiniteAlgebraUnits.BinaryRoot.contractingMatrixHom (S := R ⊗[k] D) neg t) = 1 := by
  cases neg
  · simpa only [FiniteAlgebraUnits.BinaryRoot.contractingMatrixHom,
      Bool.false_eq_true, ↓reduceIte, MonoidHom.coe_mk, OneHom.coe_mk, map_inv] using
      BinaryNorm.tensorNorm_diagonal_inverse k D R
        (Units.map (algebraMap R (R ⊗[k] D)).toMonoidHom t)
  · simpa only [FiniteAlgebraUnits.BinaryRoot.contractingMatrixHom,
      ↓reduceIte, MonoidHom.coe_mk, OneHom.coe_mk, map_inv, inv_inv] using
      BinaryNorm.tensorNorm_diagonal_inverse k D R
        (Units.map (algebraMap R (R ⊗[k] D)).toMonoidHom t⁻¹)

/-- The actual full-unit cocharacter has tensor norm one on every relative test. -/
theorem cocharacter_tensorNorm (neg : Bool) (T : Over (base k))
    (x : T ⟶ (Gm (base k)).X) :
    BinaryNorm.tensorNorm k D ((algΓ (CommRingCat.of k)).obj T).unop
      (MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) T
        (x ≫ (FiniteAlgebraUnits.BinaryRoot.cocharacter k D (matrixBasis k D) neg).hom.hom)) = 1 := by
  rw [FiniteAlgebraUnits.BinaryRoot.tensorMatrixEquiv_cocharacter]
  exact contractingMatrix_tensorNorm k D _ neg _

/-- The actual ground-field cocharacter of the canonical binary reduced-norm-one group. -/
def cocharacter (neg : Bool) : (Gm (base k)).toGrp ⟶ groupScheme k D :=
  liftHom k D (FiniteAlgebraUnits.BinaryRoot.cocharacter k D (matrixBasis k D) neg)
    (cocharacter_tensorNorm k D neg)

/-- The included norm-one cocharacter is precisely the published scalar diagonal cocharacter. -/
@[simp] theorem cocharacter_ι (neg : Bool) :
    cocharacter k D neg ≫ normOneι k (Matrix (Fin 2) (Fin 2) D) =
      FiniteAlgebraUnits.BinaryRoot.cocharacter k D (matrixBasis k D) neg :=
  liftHom_ι k D _ _

variable {d : ℕ} (bD : Module.Basis (Fin d) k D)

/-- The entire actual polynomial elementary curve has tensor norm one. -/
theorem contraction_tensorNorm (neg : Bool) {T : Over (base k)}
    (x : T ⟶ (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)).X) :
    BinaryNorm.tensorNorm k D ((algΓ (CommRingCat.of k)).obj
      (T ⊗ AffineLine.scheme (base k))).unop
      (MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) _
        (FiniteAlgebraUnits.BinaryRoot.contraction k D bD (matrixBasis k D) neg x)) = 1 := by
  simp only [FiniteAlgebraUnits.BinaryRoot.contraction, MulEquiv.apply_symm_apply]
  cases neg
  · exact BinaryNorm.tensorNorm_upper k D _ _
  · exact BinaryNorm.tensorNorm_lower k D _ _

/-- The actual polynomial elementary curve lifted into the canonical norm-one group. -/
def contraction (neg : Bool) {T : Over (base k)}
    (x : T ⟶ (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)).X) :
    T ⊗ AffineLine.scheme (base k) ⟶ (groupScheme k D).X :=
  liftPoint k D (FiniteAlgebraUnits.BinaryRoot.contraction k D bD (matrixBasis k D) neg x)
    (contraction_tensorNorm k D bD neg x)

/-- The included curve is exactly the published polynomial elementary curve. -/
@[simp] theorem contraction_ι (neg : Bool) {T : Over (base k)}
    (x : T ⟶ (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)).X) :
    contraction k D bD neg x ≫ (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom =
      FiniteAlgebraUnits.BinaryRoot.contraction k D bD (matrixBasis k D) neg x :=
  liftPoint_ι k D _ _

/-- The actual norm-one curve extends the cocharacter conjugation orbit of each elementary point. -/
theorem contraction_isOrbitExtension (neg : Bool) {T : Over (base k)}
    (x : T ⟶ (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)).X) :
    Dynamic.IsOrbitExtension (cocharacter k D neg)
      (x ≫ (elementaryMap k D bD neg).hom.hom) (contraction k D bD neg x) := by
  rw [Dynamic.IsOrbitExtension]
  apply (cancel_mono (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom).mp
  rw [Category.assoc, contraction_ι, ← Dynamic.orbit_comp_hom,
    cocharacter_ι, Category.assoc, ← Grp.comp_hom_hom, elementaryMap_ι]
  exact FiniteAlgebraUnits.BinaryRoot.contraction_isOrbitExtension
    k D bD (matrixBasis k D) neg x

/-- The lifted actual elementary curve has value the identity at zero. -/
theorem contraction_evalZero (neg : Bool) {T : Over (base k)}
    (x : T ⟶ (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)).X) :
    Dynamic.evalZero (contraction k D bD neg x) = 1 := by
  apply (cancel_mono (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom).mp
  rw [← Dynamic.evalZero_comp, contraction_ι, MonObj.one_comp]
  exact FiniteAlgebraUnits.BinaryRoot.contraction_evalZero
    k D bD (matrixBasis k D) neg x

/-- The whole actual elementary image lies in the corresponding norm-one dynamic unipotent. -/
theorem elementary_range_le_dynamicUnipotent (neg : Bool) :
    SubgroupFunctor.range (elementaryMap k D bD neg) ≤
      Dynamic.unipotent (cocharacter k D neg) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  exact ⟨contraction k D bD neg x, contraction_isOrbitExtension k D bD neg x,
    contraction_evalZero k D bD neg x⟩

end Langlands.GroupScheme.CentralSimpleUnits.BinaryRoot
