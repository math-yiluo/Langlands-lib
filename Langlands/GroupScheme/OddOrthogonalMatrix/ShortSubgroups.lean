import Langlands.GroupScheme.OddOrthogonalMatrix.GroupScheme
import Langlands.GroupScheme.OddOrthogonalMatrix.ShortMatrices
import Langlands.GroupScheme.Quaternionic.ScalarMatrixCoordinates
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Actual additive short-parameter subgroups of the odd norm-one group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open Quaternionic.FirstKindInvolution Quaternionic.ScalarMatrixCoordinates

variable {l : Type} [Fintype l] [DecidableEq l]

private theorem isAlt_of_forall_quadratic_eq_zero {m : Type*} [Fintype m] [DecidableEq m]
    {R : Type*} [CommRing R] (M : Matrix m m R)
    (h : ∀ x : m → R, x ⬝ᵥ (M *ᵥ x) = 0) : OrthogonalMatrix.IsAlt M := by
  apply (OrthogonalMatrix.isAlt_iff M).2
  have hd : ∀ i, M i i = 0 := by
    intro i
    simpa using h (Pi.single i 1)
  refine ⟨?_, hd⟩
  ext i j
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add, hd] at hij
  simpa [Matrix.add_apply, Matrix.transpose_apply, add_comm] using hij

section Coefficients
variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R]

/-- Evaluation of the scalar-extended split odd representative. -/
theorem dotProduct_formMatrix (x : Index l → R) :
    x ⬝ᵥ ((formMatrix l K).map (algebraMap K R) *ᵥ x) = value x := by
  simp [formMatrix, OrthogonalMatrix.formMatrix, value, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

/-- The coefficient-ring short matrices satisfy the full alternating-defect
condition for the split odd form. -/
theorem isAlt_shortMatrix_defect (a : l ⊕ l) (t : R) :
    OrthogonalMatrix.IsAlt (shortMatrix a t * (formMatrix l K).map (algebraMap K R) *
      (shortMatrix a t).transpose - (formMatrix l K).map (algebraMap K R)) := by
  apply isAlt_of_forall_quadratic_eq_zero
  intro x
  rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_transpose, Matrix.dotProduct_mulVec,
    dotProduct_formMatrix, dotProduct_formMatrix, value_vecMul_shortMatrix, sub_self]

end Coefficients

variable {K : Type u} [Field K]
variable (K)

local notation "𝕌" => CentralSimpleUnits.groupScheme K (Matrix (Index l) (Index l) K)
local notation "𝔸" => VectorGroup.groupScheme (CommRingCat.of K) 1

/-- The actual coefficient matrix of a point of the ambient matrix-unit group. -/
def ambientMatrix (T : Over (Spec (CommRingCat.of K))) (z : T ⟶ (𝕌).X) :
    Matrix (Index l) (Index l) ((algΓ (CommRingCat.of K)).obj T).unop :=
  matrixEquiv K _ (FiniteAlgebraUnits.pointsEquiv
    (Module.finBasis K (Matrix (Index l) (Index l) K)) T z :
      ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix (Index l) (Index l) K)

/-- Pullback of a point applies the coefficient homomorphism entrywise. -/
theorem ambientMatrix_naturality {T T' : Over (Spec (CommRingCat.of K))} (b : T' ⟶ T)
    (z : T ⟶ (𝕌).X) :
    ambientMatrix K T' (b ≫ z) = (ambientMatrix K T z).map
      (((algΓ (CommRingCat.of K)).map b).unop.hom) := by
  rw [ambientMatrix, FiniteAlgebraUnits.pointsEquiv_naturality]
  exact matrixEquiv_naturality K _ _

/-- The polynomial short family as a homomorphism on every actual test scheme. -/
def shortPoints (a : l ⊕ l) (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (𝔸).X) →* (T ⟶ (𝕌).X) :=
  (FiniteAlgebraUnits.pointsEquiv
    (Module.finBasis K (Matrix (Index l) (Index l) K)) T).symm.toMonoidHom.comp
      ((Units.mapEquiv (matrixEquiv (n := Index l) K
        ((algΓ (CommRingCat.of K)).obj T).unop).symm.toMulEquiv).toMonoidHom.comp
        ((shortUnits a).comp
          ((Pi.evalAddMonoidHom (fun _ : Fin 1 =>
              ((algΓ (CommRingCat.of K)).obj T).unop) 0).toMultiplicative.comp
            (VectorGroup.coordinates (CommRingCat.of K) 1 T).toMonoidHom)))

/-- The matrix formula for the short family on every actual test. -/
theorem ambientMatrix_shortPoints (a : l ⊕ l) (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (𝔸).X) :
    ambientMatrix K T (shortPoints K a T x) = shortMatrix a
      ((VectorGroup.coordinates (CommRingCat.of K) 1 T x).toAdd 0) := by
  unfold ambientMatrix shortPoints
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  change matrixEquiv (n := Index l) K _ ((matrixEquiv (n := Index l) K _).symm _) = _
  exact (matrixEquiv (n := Index l) K _).apply_symm_apply _

/-- Ordinary ambient matrices determine actual matrix-unit points. -/
theorem ambientMatrix_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (ambientMatrix (l := l) K T) := by
  intro z w h
  apply (FiniteAlgebraUnits.pointsEquiv
    (Module.finBasis K (Matrix (Index l) (Index l) K)) T).injective
  apply Units.ext
  exact (matrixEquiv K _).injective h

/-- The short family commutes with every change of relative test scheme. -/
theorem shortPoints_naturality (a : l ⊕ l)
    {T T' : Over (Spec (CommRingCat.of K))} (b : T' ⟶ T) (x : T ⟶ (𝔸).X) :
    shortPoints K a T' (b ≫ x) = b ≫ shortPoints K a T x := by
  apply ambientMatrix_injective K T'
  rw [ambientMatrix_naturality, ambientMatrix_shortPoints, ambientMatrix_shortPoints]
  change shortMatrix a ((VectorGroup.coordinates (CommRingCat.of K) 1 T' (b ≫ x)).toAdd 0) =
    (shortMatrix a ((VectorGroup.coordinates (CommRingCat.of K) 1 T x).toAdd 0)).map
      b.left.appTop.hom
  rw [shortMatrix_map, VectorGroup.coordinates_comp]

/-- The actual additive short-parameter map into the ambient matrix-unit group. -/
def ambientShortMap (a : l ⊕ l) : 𝔸 ⟶ 𝕌 :=
  homOfPoints (shortPoints K a) (shortPoints_naturality K a)

/-- The matrix of the actual ambient additive map on every test scheme. -/
theorem ambientMatrix_ambientShortMap (a : l ⊕ l)
    {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ (𝔸).X) :
    ambientMatrix K T (x ≫ (ambientShortMap K a).hom.hom) = shortMatrix a
      ((VectorGroup.coordinates (CommRingCat.of K) 1 T x).toAdd 0) := by
  rw [ambientShortMap, comp_homOfPoints, ambientMatrix_shortPoints]

instance mono_ambientShortMap (a : l ⊕ l) : Mono (ambientShortMap K a).hom.hom := by
  constructor
  intro T x y h
  apply VectorGroup.points_ext
  intro i
  have hm := congrArg (ambientMatrix K T) h
  rw [ambientMatrix_ambientShortMap, ambientMatrix_ambientShortMap] at hm
  have hc := congrArg (fun M : Matrix (Index l) (Index l) Γ(T.left, ⊤) =>
    M (Sum.inr a.swap) (Sum.inl ())) hm
  simp only [shortMatrix_axis_entry] at hc
  fin_cases i
  exact hc

/-- The ambient short map factors through the actual norm-one isometry group. -/
theorem exists_shortMap (a : l ⊕ l) :
    ∃ f : 𝔸 ⟶ groupScheme l K,
      f ≫ (scalar K).normOneIsometryAmbientι (form l K) = ambientShortMap K a := by
  let j := ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom
  have hmem : (ambientShortMap K a).hom.hom ∈
      (SubgroupFunctor.range ((scalar K).normOneIsometryAmbientι (form l K))).carrier (𝔸).X := by
    rw [Quaternionic.ScalarMatrixCoordinates.mem_range_normOneIsometryAmbientι_iff K
      (form l K) (formMatrix l K) rfl]
    change OrthogonalMatrix.IsAlt (ambientMatrix K (𝔸).X (ambientShortMap K a).hom.hom *
      (formMatrix l K).map (algebraMap K _) *
      (ambientMatrix K (𝔸).X (ambientShortMap K a).hom.hom).transpose -
      (formMatrix l K).map (algebraMap K _)) ∧
      (ambientMatrix K (𝔸).X (ambientShortMap K a).hom.hom).det = 1
    have hm := ambientMatrix_ambientShortMap K a (𝟙 (𝔸).X)
    simp only [Category.id_comp] at hm
    rw [hm]
    exact ⟨isAlt_shortMatrix_defect _ _, det_shortMatrix _ _⟩
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.mp hmem
  let : IsMonHom f :=
    { one_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hf, IsMonHom.one_hom, IsMonHom.one_hom]
      mul_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hf, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
          CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc, hf] }
  exact ⟨Grp.homMk f, Grp.hom_ext _ _ hf⟩

/-- The actual additive short-parameter homomorphism into the odd norm-one group. -/
def shortMap (a : l ⊕ l) : 𝔸 ⟶ groupScheme l K :=
  Classical.choose (exists_shortMap K a)

@[reassoc (attr := simp)] theorem shortMap_comp (a : l ⊕ l) :
    shortMap K a ≫ (scalar K).normOneIsometryAmbientι (form l K) = ambientShortMap K a :=
  Classical.choose_spec (exists_shortMap K a)

instance mono_shortMap (a : l ⊕ l) : Mono (shortMap K a).hom.hom := by
  have hm : Mono (shortMap K a ≫
      (scalar K).normOneIsometryAmbientι (form l K)).hom.hom := by
    rw [shortMap_comp]
    infer_instance
  change Mono ((shortMap K a).hom.hom ≫
    ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom) at hm
  exact mono_of_mono _ ((scalar K).normOneIsometryAmbientι (form l K)).hom.hom

end Langlands.GroupScheme.OddOrthogonalMatrix
