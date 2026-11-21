import Langlands.GroupScheme.CliffordSpin.AffineOrthogonalExtension
import Langlands.GroupScheme.CliffordSpin.AffineIsometryTransport
import Langlands.GroupScheme.CliffordSpin.ScalarIsometryProjection
import Langlands.GroupScheme.AffinePointComparison

/-! # Block embeddings in the scalar orthogonal and Clifford models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open Quaternionic Langlands.QuadraticForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {F : Type u} [Field F] [CharZero F] [Invertible (2 : F)]
  {m n : ℕ} [NeZero m] [NeZero (m + n)]

local notation "S" => CommRingCat.of F
local notation "basis[" k "]" => Pi.basisFun F (Fin k)

private abbrev scalarPolar {k : ℕ} (p : (FirstKindInvolution.scalar F).QuadraticForms (Fin k)) :
    Matrix (Fin k) (Fin k) F := (FirstKindInvolution.scalar F).polar p

private abbrev scalarQuadraticMap {k : ℕ} (p : (FirstKindInvolution.scalar F).QuadraticForms (Fin k)) :
    QuadraticForm F (Fin k → F) := Matrix.toQuadraticForm' (scalarPolar (k := k) p)

private abbrev scalarSpecialOrthogonal {k : ℕ} [NeZero k]
    (p : (FirstKindInvolution.scalar F).QuadraticForms (Fin k)) : GroupScheme (Spec (CommRingCat.of F)) :=
  (FirstKindInvolution.scalar F).normOneIsometryGroup p

private abbrev scalarCliffordGroup {k : ℕ} (p : (FirstKindInvolution.scalar F).QuadraticForms (Fin k)) :
    GroupScheme (Spec (CommRingCat.of F)) := groupScheme (scalarQuadraticMap (k := k) p) (Pi.basisFun F (Fin k))

variable (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin m)) (r : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

/-- The polar Gram matrix of the orthogonal sum in the concatenated basis. -/
def scalarBlockGram
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin m))
    (r : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)) : Matrix (Fin (m + n)) (Fin (m + n)) F :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks ((FirstKindInvolution.scalar F).polar q) 0 0 ((FirstKindInvolution.scalar F).polar r))

/-- The scalar quadratic form with the block polar matrix of the two summands. -/
def scalarBlockQuadratic
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin m))
    (r : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)) :
    (FirstKindInvolution.scalar F).QuadraticForms (Fin (m + n)) :=
  Submodule.Quotient.mk ((2 : F)⁻¹ • scalarBlockGram q r : Matrix (Fin (m + n)) (Fin (m + n)) F)

omit [CharZero F] [Invertible (2 : F)] [NeZero m] [NeZero (m + n)] in
private theorem scalarBlockGram_transpose : (scalarBlockGram q r)ᵀ = scalarBlockGram q r := by
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (scalarPolar (k := m) q) 0 0 (scalarPolar (k := n) r))ᵀ = _
  simp [scalarPolar, scalarBlockGram, Matrix.fromBlocks_transpose, OrthogonalMatrix.scalar_polar_transpose]

omit [Invertible (2 : F)] [NeZero m] [NeZero (m + n)] in
theorem polar_scalarBlockQuadratic : (scalarPolar (k := m + n) (scalarBlockQuadratic q r)) = scalarBlockGram q r := by
  change (2 : F)⁻¹ • scalarBlockGram q r + ((2 : F)⁻¹ • scalarBlockGram q r)ᵀ = scalarBlockGram q r
  rw [Matrix.transpose_smul, scalarBlockGram_transpose, ← add_smul, ← two_mul,
    mul_inv_cancel₀ two_ne_zero, one_smul]

omit [Invertible (2 : F)] [NeZero m] [NeZero (m + n)] in
theorem isNondegenerate_scalarBlockQuadratic
    (hq : (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q) (hr : (FirstKindInvolution.scalar F).IsNondegenerateQuadratic r) :
    (FirstKindInvolution.scalar F).IsNondegenerateQuadratic (scalarBlockQuadratic q r) := by
  change IsUnit (scalarPolar (k := m + n) (scalarBlockQuadratic q r))
  rw [polar_scalarBlockQuadratic, Matrix.isUnit_iff_isUnit_det, scalarBlockGram, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det (scalarPolar (k := m) q)).mp hq).mul
    ((Matrix.isUnit_iff_isUnit_det (scalarPolar (k := n) r)).mp hr)

omit [Invertible (2 : F)] [NeZero m] [NeZero (m + n)] in
private theorem preserves_scalarBlockQuadratic (A : CommAlgCat.{u} S) (g : GL (Fin m) A)
    (hg : (g : Matrix (Fin m) (Fin m) A)ᵀ * (scalarPolar (k := m) q).map (algebraMap F A) *
        (g : Matrix (Fin m) (Fin m) A) = (scalarPolar (k := m) q).map (algebraMap F A)) :
    let G := (orthogonalBlockMatrix n A g : Matrix (Fin (m + n)) (Fin (m + n)) A)
    Gᵀ * (scalarPolar (k := m + n) (scalarBlockQuadratic q r)).map (algebraMap F A) * G =
      (scalarPolar (k := m + n) (scalarBlockQuadratic q r)).map (algebraMap F A) := by
  intro G
  let E := Matrix.reindexRingEquiv A (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
  let Dq := (scalarPolar (k := m) q).map (algebraMap F A)
  let Dr := (scalarPolar (k := n) r).map (algebraMap F A)
  let B := Matrix.fromBlocks (g : Matrix (Fin m) (Fin m) A) 0 0 (1 : Matrix (Fin n) (Fin n) A)
  have hG : G = E B := rfl
  have hT : Gᵀ = E Bᵀ := rfl
  have hD : (scalarPolar (k := m + n) (scalarBlockQuadratic q r)).map (algebraMap F A) = E (Matrix.fromBlocks Dq 0 0 Dr) := by
    rw [polar_scalarBlockQuadratic, scalarBlockGram]
    change E ((Matrix.fromBlocks (scalarPolar (k := m) q) 0 0 (scalarPolar (k := n) r)).map (algebraMap F A)) =
      E (Matrix.fromBlocks Dq 0 0 Dr)
    rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
  rw [hT, hG, hD, ← map_mul, ← map_mul]
  congr 1
  simp only [B, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_one, zero_add, add_zero, hg, Dq]

local instance scalarNormOne_isAffine {k : ℕ} [NeZero k]
    (p : (FirstKindInvolution.scalar F).QuadraticForms (Fin k)) :
    IsAffine (scalarSpecialOrthogonal (F := F) (k := k) p).X.left := by
  let i := (FirstKindInvolution.scalar F).normOneIsometryAmbientι p
  let : IsClosedImmersion i.hom.hom.left :=
    (FirstKindInvolution.scalar F).isClosedSubgroup_normOneIsometryAmbientι p
  exact isAffine_of_isAffineHom i.hom.hom.left

private def actionRangeIso {k : ℕ} [NeZero k] (p : (FirstKindInvolution.scalar F).QuadraticForms (Fin k))
    (A : CommAlgCat.{u} S) :
    (scalarSpecialOrthogonal (F := F) (k := k) p).affinePoints A ≃* (actionMatrix p A).range :=
  MulEquiv.ofBijective (actionMatrix p A).rangeRestrict
    ⟨fun _ _ h => actionMatrix_injective p A (congrArg Subtype.val h),
      (actionMatrix p A).rangeRestrict_surjective⟩

private def blockIsometryPoints (A : CommAlgCat.{u} S) :
    (scalarSpecialOrthogonal (k := m) q).affinePoints A →* (scalarSpecialOrthogonal (k := m + n) (scalarBlockQuadratic q r)).affinePoints A :=
  (actionRangeIso (scalarBlockQuadratic q r) A).symm.toMonoidHom.comp
    (((orthogonalBlockMatrix n A).comp (actionMatrix q A)).codRestrict _ (by
      intro x
      let g := actionMatrix q A x
      obtain ⟨hp, hd⟩ := (mem_range_actionMatrix_iff q A g).mp ⟨x, rfl⟩
      refine (mem_range_actionMatrix_iff (scalarBlockQuadratic q r) A
        (orthogonalBlockMatrix n A g)).mpr ⟨?_, (det_orthogonalBlockMatrix n g).trans hd⟩
      apply (matrixAction_preserves_iff (scalarBlockQuadratic q r) A _).mpr
      exact preserves_scalarBlockQuadratic q r A g ((matrixAction_preserves_iff q A g).mp hp)))

private theorem actionMatrix_blockIsometryPoints (A : CommAlgCat.{u} S)
    (x : (scalarSpecialOrthogonal (k := m) q).affinePoints A) :
    actionMatrix (scalarBlockQuadratic q r) A (blockIsometryPoints q r A x) =
      orthogonalBlockMatrix n A (actionMatrix q A x) := by
  exact congrArg Subtype.val ((actionRangeIso (scalarBlockQuadratic q r) A).apply_symm_apply _)

private def blockIsometryNat :
    (scalarSpecialOrthogonal (k := m) q).affinePointFunctor ⟶ (scalarSpecialOrthogonal (k := m + n) (scalarBlockQuadratic q r)).affinePointFunctor where
  app A := GrpCat.ofHom (blockIsometryPoints q r A)
  naturality {A B} f := by
    ext x
    apply actionMatrix_injective (scalarBlockQuadratic q r) B
    change actionMatrix (scalarBlockQuadratic q r) B (blockIsometryPoints q r B
      ((scalarSpecialOrthogonal (k := m) q).affinePointMap f x)) =
      actionMatrix (scalarBlockQuadratic q r) B
        ((scalarSpecialOrthogonal (k := m + n) (scalarBlockQuadratic q r)).affinePointMap f (blockIsometryPoints q r A x))
    rw [actionMatrix_blockIsometryPoints, actionMatrix_naturality, actionMatrix_naturality,
      actionMatrix_blockIsometryPoints, orthogonalBlockMatrix_map]

private def affineMapWithProperty {R : CommRingCat.{u}}
    {G H : GroupScheme (Spec R)} [IsAffine G.X.left] [IsAffine H.X.left]
    (α : G.affinePointFunctor ⟶ H.affinePointFunctor)
    (P : ∀ A : CommAlgCat.{u} R, G.affinePoints A → H.affinePoints A → Prop)
    (h : ∀ (A : CommAlgCat.{u} R) (x : G.affinePoints A), P A x (α.app A x)) :
    {f : G ⟶ H // ∀ (A : CommAlgCat.{u} R) (x : G.affinePoints A), P A x (x ≫ f.hom.hom)} :=
  ⟨AffinePointComparison.map α, fun A x => by
    rw [AffinePointComparison.map_points]
    exact h A x⟩

/-- The block identity on the second summand is an actual morphism of special
orthogonal groups, with the given matrix formula. -/
def scalarBlockIsometryData :=
  affineMapWithProperty (blockIsometryNat q r)
    (fun A x y => actionMatrix (scalarBlockQuadratic q r) A y =
      orthogonalBlockMatrix n A (actionMatrix q A x))
    (actionMatrix_blockIsometryPoints q r)

private abbrev productBasis := orthogonalProductBasis (basis[m]) (basis[n])

omit [Invertible (2 : F)] [NeZero m] [NeZero (m + n)] in
private theorem blockQuadratic_apply (x : (Fin m → F) × (Fin n → F)) :
    (scalarQuadraticMap (k := m + n) (scalarBlockQuadratic q r)) ((productBasis (F := F) (m := m) (n := n)).equivFun x) =
      ((scalarQuadraticMap (k := m) q).prod (scalarQuadraticMap (k := n) r)) x := by
  let y := (productBasis (F := F) (m := m) (n := n)).equivFun x
  simp only [scalarQuadraticMap, Matrix.toQuadraticForm', QuadraticMap.prod_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  change y ⬝ᵥ (scalarPolar (k := m + n) (scalarBlockQuadratic q r)) *ᵥ y =
    x.1 ⬝ᵥ (scalarPolar (k := m) q) *ᵥ x.1 + x.2 ⬝ᵥ (scalarPolar (k := n) r) *ᵥ x.2
  rw [polar_scalarBlockQuadratic, scalarBlockGram]
  simp only [dotProduct, Matrix.mulVec]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    simp [y, Matrix.reindex_apply, Matrix.submatrix_apply, productBasis, orthogonalProductBasis]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    simp [y, Matrix.reindex_apply, Matrix.submatrix_apply, productBasis, orthogonalProductBasis]

/-- The product quadratic form in the concatenated standard coordinates. -/
def scalarBlockIsometryEquiv : ((scalarQuadraticMap (k := m) q).prod (scalarQuadraticMap (k := n) r)).IsometryEquiv
    (scalarQuadraticMap (k := m + n) (scalarBlockQuadratic q r)) :=
  ⟨(productBasis (F := F) (m := m) (n := n)).equivFun, blockQuadratic_apply q r⟩

omit [Invertible (2 : F)] [NeZero m] [NeZero (m + n)] in
theorem scalarBlockIsometryEquiv_basis (i : Fin (m + n)) :
    scalarBlockIsometryEquiv q r (productBasis i) = basis[m + n] i := by
  ext j
  change (productBasis (F := F) (m := m) (n := n)).equivFun (productBasis i) j = _
  simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]

/-- The block extension in the standard scalar models used by the central covers. -/
def scalarBlockSpin : scalarCliffordGroup (k := m) q ⟶
    scalarCliffordGroup (k := m + n) (scalarBlockQuadratic q r) :=
  orthogonalExtension (scalarQuadraticMap (k := m) q) (scalarQuadraticMap (k := n) r) (basis[m]) (basis[n]) ≫
    isometryTransport (scalarBlockIsometryEquiv q r) (scalarBlockIsometryEquiv_basis q r)

omit [NeZero m] [NeZero (m + n)] in
theorem scalarBlockSpin_action (A : CommAlgCat.{u} S)
    (x : (scalarCliffordGroup (k := m) q).affinePoints A) :
    (affinePairEquiv (scalarQuadraticMap (k := m + n) (scalarBlockQuadratic q r)) (basis[m + n]) A
      (x ≫ (scalarBlockSpin q r).hom.hom)).val.2 =
    orthogonalBlockMatrix n A (affinePairEquiv (scalarQuadraticMap (k := m) q) (basis[m]) A x).val.2 := by
  rw [scalarBlockSpin, Grp.comp_hom_hom, ← Category.assoc, affinePairEquiv_isometryTransport,
    affinePairEquiv_orthogonalExtension, orthogonalBlockPair_val]

end Langlands.GroupScheme.CliffordSpin
