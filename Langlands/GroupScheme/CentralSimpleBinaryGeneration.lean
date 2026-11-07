import Langlands.GroupScheme.CentralSimpleBinaryRoots
import Langlands.Algebra.BinaryReducedNorm
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Actual rational binary norm-one points and elementary generation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits.BinaryRoot

open FiniteAlgebraUnits

variable (k D : Type u) [Field k] [Ring D] [Algebra k D]

/-- The base-field tensor-unit equivalence for the binary matrix algebra. -/
def baseTensorEquiv : (k ⊗[k] Matrix (Fin 2) (Fin 2) D)ˣ ≃*
    Langlands.BinaryElementary.GL₂ D :=
  Units.mapEquiv (Algebra.TensorProduct.lid k (Matrix (Fin 2) (Fin 2) D)).toMulEquiv

/-- The inverse tensor-unit map is the actual right tensor inclusion. -/
theorem baseTensorEquiv_symm (g : Langlands.BinaryElementary.GL₂ D) :
    (baseTensorEquiv k D).symm g =
      Units.map Algebra.TensorProduct.includeRight.toMonoidHom g := by
  apply Units.ext
  rfl

variable [FiniteDimensional k D] [Algebra.IsCentral k D] [IsSimpleRing D]

/-- The canonical reduced-norm-one tensor group is the original binary norm kernel. -/
def baseNormKernelEquiv :
    Langlands.CentralSimple.reducedNormOne k (Matrix (Fin 2) (Fin 2) D) k ≃*
      (Langlands.BinaryElementary.Reduced.binaryNorm k D).ker where
  toFun x := ⟨baseTensorEquiv k D x.val, by
    change Langlands.CentralSimple.reducedNormUnits k (Matrix (Fin 2) (Fin 2) D) k
      (Units.map Algebra.TensorProduct.includeRight.toMonoidHom
        (baseTensorEquiv k D x.val)) = 1
    rw [← baseTensorEquiv_symm, MulEquiv.symm_apply_apply]
    exact x.property⟩
  invFun x := ⟨(baseTensorEquiv k D).symm x.val, by
    change Langlands.CentralSimple.reducedNormUnits k (Matrix (Fin 2) (Fin 2) D) k
      ((baseTensorEquiv k D).symm x.val) = 1
    rw [baseTensorEquiv_symm]
    exact x.property⟩
  left_inv x := Subtype.ext ((baseTensorEquiv k D).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((baseTensorEquiv k D).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((baseTensorEquiv k D).map_mul x.val y.val)

/-- Actual rational norm-one points are precisely the canonical binary norm kernel. -/
def rationalMatrixEquiv : rationalPoints (groupScheme k D) ≃*
    (Langlands.BinaryElementary.Reduced.binaryNorm k D).ker :=
  (normOneRationalPointsEquiv k (Matrix (Fin 2) (Fin 2) D)).trans
    (baseNormKernelEquiv k D)

/-- The rational comparison is exactly the actual inclusion followed by unit coordinates. -/
theorem rationalMatrixEquiv_val (x : rationalPoints (groupScheme k D)) :
    (rationalMatrixEquiv k D x).val =
      FiniteAlgebraUnits.rationalPointsEquiv (matrixBasis k D)
        (rationalPoints.map (normOneι k (Matrix (Fin 2) (Fin 2) D)) x) := by
  change baseTensorEquiv k D
      (normOneRationalPointsEquiv k (Matrix (Fin 2) (Fin 2) D) x).val = _
  rw [normOneRationalPointsEquiv_val]
  rfl

/-- The affine test for the base coefficient algebra. -/
abbrev baseAffineTest : Over (base k) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k))

/-- Actual affine sections followed by the base-field tensor comparison. -/
def baseSectionsTensorEquiv :
    ((algΓ (CommRingCat.of k)).obj (baseAffineTest k)).unop ⊗[k] D ≃ₐ[k] D :=
  (Algebra.TensorProduct.congr
    (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of k) k))
    (AlgEquiv.refl : D ≃ₐ[k] D)).trans (Algebra.TensorProduct.lid k D)

omit [Algebra.IsCentral k D] in
/-- The base affine unit coordinates agree with the actual section matrix coordinates. -/
theorem affine_base_matrix (y : baseAffineTest k ⟶
    (CentralSimpleUnits.groupScheme k (Matrix (Fin 2) (Fin 2) D)).X) :
    Units.map (Algebra.TensorProduct.lid k (Matrix (Fin 2) (Fin 2) D)).toMonoidHom
        (affinePointsEquiv (matrixBasis k D)
          (CommAlgCat.of (CommRingCat.of k) k) y) =
      Units.map (RingHom.mapMatrix (baseSectionsTensorEquiv k D).toRingHom).toMonoidHom
        (MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) (baseAffineTest k) y) := by
  let S := CommAlgCat.of (CommRingCat.of k) k
  let f := (Corepresented.affineSectionsIso S).hom.hom
  have hp := Corepresented.map_affineSectionsIso_pointsEquiv
    (FiniteAlgebraUnits.functor k (Matrix (Fin 2) (Fin 2) D))
    (corepresentableBy (matrixBasis k D)) S y
  apply Units.ext
  have hpv := congrArg Units.val hp
  change Algebra.TensorProduct.map f (AlgHom.id k (Matrix (Fin 2) (Fin 2) D))
      (pointsEquiv (matrixBasis k D) (baseAffineTest k) y :
        ((algΓ (CommRingCat.of k)).obj (baseAffineTest k)).unop ⊗[k]
          Matrix (Fin 2) (Fin 2) D) =
    (affinePointsEquiv (matrixBasis k D) S y : k ⊗[k] Matrix (Fin 2) (Fin 2) D) at hpv
  change Algebra.TensorProduct.lid k (Matrix (Fin 2) (Fin 2) D)
      (affinePointsEquiv (matrixBasis k D) S y : k ⊗[k] Matrix (Fin 2) (Fin 2) D) =
    (MatrixPoints.coefficientEquiv k D _
      (pointsEquiv (matrixBasis k D) (baseAffineTest k) y :
        ((algΓ (CommRingCat.of k)).obj (baseAffineTest k)).unop ⊗[k]
          Matrix (Fin 2) (Fin 2) D)).map (baseSectionsTensorEquiv k D)
  rw [← hpv, ← MatrixPoints.coefficientEquiv_lid,
    MatrixPoints.coefficientEquiv_naturality]
  rfl

/-- The included rational matrix is the base-section matrix of its actual affine point. -/
theorem rationalMatrixEquiv_tensor (x : rationalPoints (groupScheme k D)) :
    (rationalMatrixEquiv k D x).val =
      Units.map (RingHom.mapMatrix (baseSectionsTensorEquiv k D).toRingHom).toMonoidHom
        (MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) (baseAffineTest k)
          (GaloisPointComparison.rationalCoeffEquiv k
            (CentralSimpleUnits.groupScheme k (Matrix (Fin 2) (Fin 2) D))
            (rationalPoints.map (normOneι k (Matrix (Fin 2) (Fin 2) D)) x))) := by
  rw [rationalMatrixEquiv_val]
  exact affine_base_matrix k D _

variable {d : ℕ} (bD : Module.Basis (Fin d) k D)

/-- The coefficient of an actual rational additive point, recovered from its actual sections. -/
def rationalParameter (x : rationalPoints
    (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d))) : D :=
  baseSectionsTensorEquiv k D
    (FiniteAlgebraUnits.BinaryRoot.tensorCoordinates k D bD (baseAffineTest k)
      (GaloisPointComparison.rationalCoeffEquiv k
        (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)) x)).toAdd

omit [FiniteDimensional k D] [Algebra.IsCentral k D] [IsSimpleRing D] in
/-- Every coefficient occurs in the actual rational elementary parameter map. -/
theorem rationalParameter_surjective : Function.Surjective (rationalParameter k D bD) := by
  intro a
  obtain ⟨y, hy⟩ := FiniteAlgebraUnits.BinaryRoot.tensorCoordinates_surjective k D bD
    (baseAffineTest k) (Multiplicative.ofAdd ((baseSectionsTensorEquiv k D).symm a))
  refine ⟨(GaloisPointComparison.rationalCoeffEquiv k
    (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d))).symm y, ?_⟩
  simp only [rationalParameter, MulEquiv.apply_symm_apply, hy]
  exact (baseSectionsTensorEquiv k D).apply_symm_apply a

/-- The rational comparison sends the actual elementary morphism to its elementary matrix. -/
theorem rationalMatrixEquiv_elementaryMap (neg : Bool)
    (x : rationalPoints (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d))) :
    (rationalMatrixEquiv k D (rationalPoints.map (elementaryMap k D bD neg) x)).val =
      FiniteAlgebraUnits.BinaryRoot.elementaryMatrix neg (rationalParameter k D bD x) := by
  rw [rationalMatrixEquiv_tensor, GaloisPointComparison.rationalCoeffEquiv_map,
    GaloisPointComparison.rationalCoeffEquiv_map]
  change Units.map (RingHom.mapMatrix (baseSectionsTensorEquiv k D).toRingHom).toMonoidHom
    (MatrixPoints.tensorMatrixEquiv k D (matrixBasis k D) (baseAffineTest k)
      (((GaloisPointComparison.rationalCoeffEquiv k
        (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)) x) ≫
        (elementaryMap k D bD neg).hom.hom) ≫
        (normOneι k (Matrix (Fin 2) (Fin 2) D)).hom.hom)) = _
  rw [tensorMatrixEquiv_elementaryMap]
  cases neg
  · exact FiniteAlgebraUnits.BinaryRoot.map_upper _ _
  · exact FiniteAlgebraUnits.BinaryRoot.map_lower _ _

/-- Every original elementary matrix is the image of an actual rational elementary point. -/
theorem exists_rational_elementaryPoint (neg : Bool) (a : D) :
    ∃ x : rationalPoints (FiniteAlgebraUnits.BinaryRoot.additiveScheme k (d := d)),
      (rationalMatrixEquiv k D (rationalPoints.map (elementaryMap k D bD neg) x)).val =
        FiniteAlgebraUnits.BinaryRoot.elementaryMatrix neg a := by
  obtain ⟨x, hx⟩ := rationalParameter_surjective k D bD a
  exact ⟨x, (rationalMatrixEquiv_elementaryMap k D bD neg x).trans (congrArg _ hx)⟩

/-- Actual rational matrix coordinates, including the canonical norm kernel in the full unit group. -/
def rationalMatrixHom : rationalPoints (groupScheme k D) →* Langlands.BinaryElementary.GL₂ D :=
  (Langlands.BinaryElementary.Reduced.binaryNorm k D).ker.subtype.comp
    (rationalMatrixEquiv k D).toMonoidHom

/-- The matrix coordinate homomorphism is injective. -/
theorem rationalMatrixHom_injective : Function.Injective (rationalMatrixHom k D) := by
  intro x y h
  apply (rationalMatrixEquiv k D).injective
  exact Subtype.ext h

/-- Its image is exactly the canonical binary reduced-norm kernel. -/
theorem range_rationalMatrixHom :
    (rationalMatrixHom k D).range = (Langlands.BinaryElementary.Reduced.binaryNorm k D).ker := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact (rationalMatrixEquiv k D x).property
  · intro g hg
    refine ⟨(rationalMatrixEquiv k D).symm ⟨g, hg⟩, ?_⟩
    change (rationalMatrixEquiv k D ((rationalMatrixEquiv k D).symm ⟨g, hg⟩)).val = g
    rw [MulEquiv.apply_symm_apply]

/-- The subgroup generated by both actual rational elementary images. -/
def rationalElementarySubgroup : Subgroup (rationalPoints (groupScheme k D)) :=
  (rationalPoints.map (elementaryMap k D bD false)).range ⊔
    (rationalPoints.map (elementaryMap k D bD true)).range

/-- Actual rational elementary generation has exactly the original elementary matrix image. -/
theorem map_rationalElementarySubgroup :
    (rationalElementarySubgroup k D bD).map (rationalMatrixHom k D) =
      Langlands.BinaryElementary.elementary D := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply sup_le
    · rintro _ ⟨x, rfl⟩
      change (rationalMatrixEquiv k D
        (rationalPoints.map (elementaryMap k D bD false) x)).val ∈
          Langlands.BinaryElementary.elementary D
      rw [rationalMatrixEquiv_elementaryMap]
      exact Langlands.BinaryElementary.upper_mem _
    · rintro _ ⟨x, rfl⟩
      change (rationalMatrixEquiv k D
        (rationalPoints.map (elementaryMap k D bD true) x)).val ∈
          Langlands.BinaryElementary.elementary D
      rw [rationalMatrixEquiv_elementaryMap]
      exact Langlands.BinaryElementary.lower_mem _
  · apply (Subgroup.closure_le _).mpr
    rintro g (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · obtain ⟨x, hx⟩ := exists_rational_elementaryPoint k D bD false a
      refine ⟨rationalPoints.map (elementaryMap k D bD false) x, ?_, hx⟩
      exact (show (rationalPoints.map (elementaryMap k D bD false)).range ≤
        rationalElementarySubgroup k D bD from le_sup_left) ⟨x, rfl⟩
    · obtain ⟨x, hx⟩ := exists_rational_elementaryPoint k D bD true a
      refine ⟨rationalPoints.map (elementaryMap k D bD true) x, ?_, hx⟩
      exact (show (rationalPoints.map (elementaryMap k D bD true)).range ≤
        rationalElementarySubgroup k D bD from le_sup_right) ⟨x, rfl⟩

/-- Rational elementary generation is equivalent to generation of the canonical binary norm kernel. -/
theorem rationalElementarySubgroup_eq_top_iff_binary :
    rationalElementarySubgroup k D bD = ⊤ ↔
      Langlands.BinaryElementary.elementary D =
        (Langlands.BinaryElementary.Reduced.binaryNorm k D).ker := by
  constructor
  · intro h
    rw [← map_rationalElementarySubgroup k D bD, h, Subgroup.map_top]
    exact range_rationalMatrixHom k D
  · intro h
    apply top_unique
    intro x _
    have hx : rationalMatrixHom k D x ∈
        (rationalElementarySubgroup k D bD).map (rationalMatrixHom k D) := by
      rw [map_rationalElementarySubgroup, h]
      exact (rationalMatrixEquiv k D x).property
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [rationalMatrixHom_injective k D hyx] at hy

section DivisionRing

variable {D : Type u} [DivisionRing D] [Algebra k D]
  [FiniteDimensional k D] [Algebra.IsCentral k D]
  {d : ℕ} (bD : Module.Basis (Fin d) k D)

/-- Actual binary rational elementary generation is exactly coefficient SK1 vanishing. -/
theorem rationalElementarySubgroup_eq_top_iff :
    rationalElementarySubgroup k D bD = ⊤ ↔
      (Langlands.BinaryElementary.Reduced.coefficientNorm k D).ker = commutator Dˣ :=
  (rationalElementarySubgroup_eq_top_iff_binary k D bD).trans
    (Langlands.BinaryElementary.Reduced.elementary_eq_ker_iff k)

end DivisionRing

end Langlands.GroupScheme.CentralSimpleUnits.BinaryRoot
