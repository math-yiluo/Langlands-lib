import Langlands.GroupScheme.Examples.QuasiSplitUnitary
import Langlands.GroupScheme.Dynamic.GeneralLinear

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- The two opposite weights of a hyperbolic diagonal cocharacter. -/
def weights (m : ℤ) : Fin 2 → ℤ := ![m, -m]

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]

section Matrices
variable (R : Type u) [CommRing R] [Algebra F R]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The additive, R-linear trace-zero subspace of E tensor R. -/
def traceZero (c : E ≃ₐ[F] E) : Submodule R (E ⊗[F] R) :=
  LinearMap.ker (LinearMap.id + (scalarConjugation R c).toLinearMap)

omit [IsQuadraticExtension F E] in
@[simp] theorem mem_traceZero (c : E ≃ₐ[F] E) (x : E ⊗[F] R) :
    x ∈ traceZero R c ↔ x + scalarConjugation R c x = 0 := Iff.rfl

/-- Multiplication of a trace-zero parameter by an integral power of a scalar unit. -/
def scaleTraceZero (c : E ≃ₐ[F] E) (t : Rˣ) (m : ℤ) (x : traceZero R c) :
    traceZero R c :=
  ((t ^ m : Rˣ) : R) • x

/-- A diagonal unit with opposite integral weights, as a unitary matrix. -/
def diagonalUnitary (c : E ≃ₐ[F] E) (m : ℤ) : Rˣ →* matrixPoints R c where
  toFun t := ⟨GeneralLinear.diagonalUnits (E ⊗[F] R) (weights m)
      (Units.map (algebraMap R (E ⊗[F] R)).toMonoidHom t), by
    rw [matrixPoints, Langlands.Shimura.AlgebraInvolution.mem_unitary_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixInvolution, adjoint, GeneralLinear.coe_diagonalUnits, weights,
        Matrix.mul_apply, Fin.sum_univ_two, ← map_zpow] <;>
      rw [← map_mul, ← Units.val_mul] <;> simp⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' t s := Subtype.ext (map_mul
    ((GeneralLinear.diagonalUnits (E ⊗[F] R) (weights m)).comp
      (Units.map (algebraMap R (E ⊗[F] R)).toMonoidHom)) t s)

@[simp] theorem diagonalUnitary_val (c : E ≃ₐ[F] E) (m : ℤ) (t : Rˣ) :
    ((diagonalUnitary R c m t).val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) =
      Matrix.diagonal (fun i => algebraMap R (E ⊗[F] R) ((t ^ weights m i : Rˣ) : R)) := by
  ext i j
  simp [diagonalUnitary, GeneralLinear.coe_diagonalUnits, ← map_zpow]


omit [IsQuadraticExtension F E] in
/-- Scalar extension sends the coefficient scalars to the new coefficient scalars. -/
@[simp] theorem tensorCoefficientMap_algebraMap {S : Type u} [CommRing S] [Algebra F S]
    (f : R →ₐ[F] S) (r : R) :
    tensorCoefficientMap f (algebraMap R (E ⊗[F] R) r) =
      algebraMap S (E ⊗[F] S) (f r) := rfl

/-- The diagonal unitary matrices are natural in the coefficient algebra. -/
theorem diagonalUnitary_naturality {S : Type u} [CommRing S] [Algebra F S]
    (c : E ≃ₐ[F] E) (m : ℤ) (f : R →ₐ[F] S) (t : Rˣ) :
    Matrix.GeneralLinearGroup.map (tensorCoefficientMap f).toRingHom
        (diagonalUnitary R c m t).val =
      (diagonalUnitary S c m (Units.map f.toMonoidHom t)).val := by
  apply Units.ext
  change ((diagonalUnitary R c m t).val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)).map _ = _
  rw [diagonalUnitary_val, diagonalUnitary_val]
  ext i j
  simp only [Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs
  · rw [← map_zpow, Units.coe_map]
    exact tensorCoefficientMap_algebraMap R f _
  · exact map_zero _

/-- The invertible upper elementary matrix, with inverse given by negating its entry. -/
def upperRootMatrix (x : E ⊗[F] R) : GL (Fin 2) (E ⊗[F] R) where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The invertible lower elementary matrix. -/
def lowerRootMatrix (x : E ⊗[F] R) : GL (Fin 2) (E ⊗[F] R) where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The upper root homomorphism from the additive trace-zero group. -/
def upperRoot (c : E ≃ₐ[F] E) : Multiplicative (traceZero R c) →* matrixPoints R c where
  toFun x := ⟨upperRootMatrix R (Multiplicative.toAdd x).val, by
    rw [matrixPoints, Langlands.Shimura.AlgebraInvolution.mem_unitary_iff]
    have hx := (mem_traceZero R c _).mp (Multiplicative.toAdd x).property
    have hx' : scalarConjugation R c (Multiplicative.toAdd x).val +
        (Multiplicative.toAdd x).val = 0 := by simpa only [add_comm] using hx
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperRootMatrix, matrixInvolution, adjoint, Matrix.mul_apply,
        Fin.sum_univ_two, hx']⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperRootMatrix]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperRootMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The lower root homomorphism from the additive trace-zero group. -/
def lowerRoot (c : E ≃ₐ[F] E) : Multiplicative (traceZero R c) →* matrixPoints R c where
  toFun x := ⟨lowerRootMatrix R (Multiplicative.toAdd x).val, by
    rw [matrixPoints, Langlands.Shimura.AlgebraInvolution.mem_unitary_iff]
    have hx := (mem_traceZero R c _).mp (Multiplicative.toAdd x).property
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerRootMatrix, matrixInvolution, adjoint, Matrix.mul_apply,
        Fin.sum_univ_two, hx]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerRootMatrix]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerRootMatrix, Matrix.mul_apply, Fin.sum_univ_two]


/-- The negative weight gives the inverse of the positive-weight point. -/
theorem diagonalUnitary_neg_one (c : E ≃ₐ[F] E) (t : Rˣ) :
    diagonalUnitary R c (-1) t = (diagonalUnitary R c 1 t)⁻¹ := by
  rw [← map_inv]
  apply Subtype.ext
  apply Units.ext
  rw [diagonalUnitary_val, diagonalUnitary_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weights]

/-- Conjugation on the upper root group has weight two. -/
theorem diagonalUnitary_upperRoot (c : E ≃ₐ[F] E) (t : Rˣ) (x : traceZero R c) :
    diagonalUnitary R c 1 t * upperRoot R c (Multiplicative.ofAdd x) *
        (diagonalUnitary R c 1 t)⁻¹ =
      upperRoot R c (Multiplicative.ofAdd (scaleTraceZero R c t 2 x)) := by
  rw [← map_inv]
  apply Subtype.ext
  apply Units.ext
  change (diagonalUnitary R c 1 t).val.val *
      (upperRoot R c (Multiplicative.ofAdd x)).val.val *
      (diagonalUnitary R c 1 (t⁻¹)).val.val = _
  rw [diagonalUnitary_val, diagonalUnitary_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperRoot, upperRootMatrix, scaleTraceZero, weights, Matrix.mul_apply, Fin.sum_univ_two,
      Algebra.smul_def, pow_two] <;>
    first | (rw [← map_mul, ← Units.val_mul]; simp; done) | ring

/-- Conjugation on the lower root group has weight minus two. -/
theorem diagonalUnitary_lowerRoot (c : E ≃ₐ[F] E) (t : Rˣ) (x : traceZero R c) :
    diagonalUnitary R c 1 t * lowerRoot R c (Multiplicative.ofAdd x) *
        (diagonalUnitary R c 1 t)⁻¹ =
      lowerRoot R c (Multiplicative.ofAdd (scaleTraceZero R c t (-2) x)) := by
  rw [← map_inv]
  apply Subtype.ext
  apply Units.ext
  change (diagonalUnitary R c 1 t).val.val *
      (lowerRoot R c (Multiplicative.ofAdd x)).val.val *
      (diagonalUnitary R c 1 (t⁻¹)).val.val = _
  rw [diagonalUnitary_val, diagonalUnitary_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerRoot, lowerRootMatrix, scaleTraceZero, weights, Matrix.mul_apply, Fin.sum_univ_two,
      Algebra.smul_def, zpow_neg, pow_two] <;>
    first | (rw [← map_mul, ← Units.val_mul]; simp; done) | ring

end Matrices

section Schemes
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)

/-- Matrix coordinates as a homomorphism into the full general linear group. -/
def matrixCoordinates (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (groupScheme b c).X) →*
      GL (Fin 2) (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T).unop) :=
  (matrixPoints _ c).subtype.comp (pointsEquiv b c T).toMonoidHom

/-- Matrix coordinates restrict by entrywise change of coefficients. -/
theorem matrixCoordinates_naturality {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (x : T ⟶ (groupScheme b c).X) :
    matrixCoordinates b c T' (a ≫ x) =
      Matrix.GeneralLinearGroup.map
        (tensorCoefficientMap ((algΓ (CommRingCat.of F)).map a).unop.hom).toRingHom
          (matrixCoordinates b c T x) :=
  Units.ext (pointsEquiv_naturality b c a x)


/-- The natural family of point homomorphisms with opposite weights. -/
def weightCocharacterPoints (m : ℤ) (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (Gm (Spec (CommRingCat.of F))).X) →* (T ⟶ (groupScheme b c).X) :=
  (pointsEquiv b c T).symm.toMonoidHom.comp
    ((diagonalUnitary _ c m).comp (Gm.pointsEquiv _ T).toMonoidHom)

@[simp] theorem pointsEquiv_weightCocharacterPoints (m : ℤ)
    (T : Over (Spec (CommRingCat.of F))) (t : T ⟶ (Gm (Spec (CommRingCat.of F))).X) :
    pointsEquiv b c T (weightCocharacterPoints b c m T t) =
      diagonalUnitary ((algΓ (CommRingCat.of F)).obj T).unop c m (Gm.pointsEquiv _ T t) :=
  MulEquiv.apply_symm_apply _ _

/-- Naturality holds on all test schemes. -/
theorem weightCocharacterPoints_naturality (m : ℤ)
    {T T' : Over (Spec (CommRingCat.of F))} (a : T' ⟶ T)
    (t : T ⟶ (Gm (Spec (CommRingCat.of F))).X) :
    weightCocharacterPoints b c m T' (a ≫ t) = a ≫ weightCocharacterPoints b c m T t := by
  apply (pointsEquiv b c T').injective
  apply Subtype.ext
  rw [pointsEquiv_weightCocharacterPoints]
  apply Units.ext
  rw [pointsEquiv_naturality, pointsEquiv_weightCocharacterPoints,
    Gm.pointsEquiv_naturality]
  exact congrArg Units.val (diagonalUnitary_naturality _ c m
    ((algΓ (CommRingCat.of F)).map a).unop.hom (Gm.pointsEquiv _ T t)).symm

/-- The group-scheme cocharacter with weights m and -m. -/
def weightCocharacter (m : ℤ) : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ groupScheme b c :=
  homOfPoints (weightCocharacterPoints b c m) (weightCocharacterPoints_naturality b c m)

/-- The hyperbolic cocharacter t ↦ diag(t,t⁻¹). -/
abbrev cocharacter := weightCocharacter b c 1

/-- The opposite hyperbolic cocharacter t ↦ diag(t⁻¹,t). -/
abbrev inverseCocharacter := weightCocharacter b c (-1)

@[simp] theorem pointsEquiv_weightCocharacter (m : ℤ)
    (T : Over (Spec (CommRingCat.of F))) (t : T ⟶ (Gm (Spec (CommRingCat.of F))).X) :
    pointsEquiv b c T (t ≫ (weightCocharacter b c m).hom.hom) =
      diagonalUnitary ((algΓ (CommRingCat.of F)).obj T).unop c m (Gm.pointsEquiv _ T t) := by
  rw [weightCocharacter, comp_homOfPoints, pointsEquiv_weightCocharacterPoints]

/-- Pull back any coefficient-stable family of matrix subgroups to unitary points. -/
def ofMatrixSubgroups (H : ∀ A : CommRingCat.{u}, Subgroup (GL (Fin 2) A))
    (hH : ∀ {A B : CommRingCat.{u}} (f : A ⟶ B) {g : GL (Fin 2) A}, g ∈ H A →
      Matrix.GeneralLinearGroup.map f.hom g ∈ H B) :
    SubgroupFunctor (groupScheme b c) where
  carrier T := (H (CommRingCat.of (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T).unop))).comap
    (matrixCoordinates b c T)
  comp_mem := fun {T T'} a {x} hx => by
    change matrixCoordinates b c T' (a ≫ x) ∈
      H (CommRingCat.of (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T').unop))
    rw [matrixCoordinates_naturality]
    exact hH (CommRingCat.ofHom _) hx

/-- Upper triangular unitary matrices on every test scheme. -/
def upperTriangular : SubgroupFunctor (groupScheme b c) :=
  ofMatrixSubgroups b c (fun A => GeneralLinear.blockParabolicSubgroup A (weights 1))
    (fun f _ hg => GeneralLinear.map_mem_blockParabolicSubgroup _ f.hom hg)

/-- Lower triangular unitary matrices on every test scheme. -/
def lowerTriangular : SubgroupFunctor (groupScheme b c) :=
  ofMatrixSubgroups b c (fun A => GeneralLinear.blockParabolicSubgroup A (weights (-1)))
    (fun f _ hg => GeneralLinear.map_mem_blockParabolicSubgroup _ f.hom hg)

/-- Diagonal unitary matrices on every test scheme. -/
def diagonal : SubgroupFunctor (groupScheme b c) :=
  ofMatrixSubgroups b c (fun A => GeneralLinear.blockLeviSubgroup A (weights 1))
    (fun f _ hg => GeneralLinear.map_mem_blockLeviSubgroup _ f.hom hg)

/-- Upper triangular unitary matrices with both diagonal entries one. -/
def upperUnipotent : SubgroupFunctor (groupScheme b c) :=
  ofMatrixSubgroups b c (fun A => GeneralLinear.blockUnipotentSubgroup A (weights 1))
    (fun f _ hg => GeneralLinear.map_mem_blockUnipotentSubgroup _ f.hom hg)

/-- Lower triangular unitary matrices with both diagonal entries one. -/
def lowerUnipotent : SubgroupFunctor (groupScheme b c) :=
  ofMatrixSubgroups b c (fun A => GeneralLinear.blockUnipotentSubgroup A (weights (-1)))
    (fun f _ hg => GeneralLinear.map_mem_blockUnipotentSubgroup _ f.hom hg)


@[simp] theorem mem_upperTriangular {T : Over (Spec (CommRingCat.of F))}
    {x : T ⟶ (groupScheme b c).X} :
    x ∈ (upperTriangular b c).carrier T ↔ matrixCoordinates b c T x 1 0 = 0 := by
  change (∀ i j, weights 1 i < weights 1 j → matrixCoordinates b c T x i j = 0) ↔ _
  simp [Fin.forall_fin_two, weights]

@[simp] theorem mem_lowerTriangular {T : Over (Spec (CommRingCat.of F))}
    {x : T ⟶ (groupScheme b c).X} :
    x ∈ (lowerTriangular b c).carrier T ↔ matrixCoordinates b c T x 0 1 = 0 := by
  change (∀ i j, weights (-1) i < weights (-1) j → matrixCoordinates b c T x i j = 0) ↔ _
  simp [Fin.forall_fin_two, weights]

@[simp] theorem mem_diagonal {T : Over (Spec (CommRingCat.of F))}
    {x : T ⟶ (groupScheme b c).X} :
    x ∈ (diagonal b c).carrier T ↔
      matrixCoordinates b c T x 0 1 = 0 ∧ matrixCoordinates b c T x 1 0 = 0 := by
  change (∀ i j, weights 1 i ≠ weights 1 j → matrixCoordinates b c T x i j = 0) ↔ _
  simp [Fin.forall_fin_two, weights]

@[simp] theorem mem_upperUnipotent {T : Over (Spec (CommRingCat.of F))}
    {x : T ⟶ (groupScheme b c).X} :
    x ∈ (upperUnipotent b c).carrier T ↔
      matrixCoordinates b c T x 1 0 = 0 ∧ matrixCoordinates b c T x 0 0 = 1 ∧
        matrixCoordinates b c T x 1 1 = 1 := by
  change (∀ i j, weights 1 i ≤ weights 1 j → matrixCoordinates b c T x i j =
    (1 : Matrix (Fin 2) (Fin 2) (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T).unop)) i j) ↔ _
  simp [Fin.forall_fin_two, weights, and_comm, and_left_comm]

@[simp] theorem mem_lowerUnipotent {T : Over (Spec (CommRingCat.of F))}
    {x : T ⟶ (groupScheme b c).X} :
    x ∈ (lowerUnipotent b c).carrier T ↔
      matrixCoordinates b c T x 0 1 = 0 ∧ matrixCoordinates b c T x 0 0 = 1 ∧
        matrixCoordinates b c T x 1 1 = 1 := by
  change (∀ i j, weights (-1) i ≤ weights (-1) j → matrixCoordinates b c T x i j =
    (1 : Matrix (Fin 2) (Fin 2) (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T).unop)) i j) ↔ _
  simp [Fin.forall_fin_two, weights, and_assoc, and_comm, and_left_comm]

/-- Upper root points over an arbitrary test scheme. -/
def upperRootPoints (T : Over (Spec (CommRingCat.of F))) :
    Multiplicative (traceZero ((algΓ (CommRingCat.of F)).obj T).unop c) →*
      (T ⟶ (groupScheme b c).X) :=
  (pointsEquiv b c T).symm.toMonoidHom.comp (upperRoot _ c)

/-- Lower root points over an arbitrary test scheme. -/
def lowerRootPoints (T : Over (Spec (CommRingCat.of F))) :
    Multiplicative (traceZero ((algΓ (CommRingCat.of F)).obj T).unop c) →*
      (T ⟶ (groupScheme b c).X) :=
  (pointsEquiv b c T).symm.toMonoidHom.comp (lowerRoot _ c)


@[simp] theorem pointsEquiv_upperRootPoints (T : Over (Spec (CommRingCat.of F)))
    (x : Multiplicative (traceZero ((algΓ (CommRingCat.of F)).obj T).unop c)) :
    pointsEquiv b c T (upperRootPoints b c T x) = upperRoot _ c x :=
  MulEquiv.apply_symm_apply _ _

@[simp] theorem pointsEquiv_lowerRootPoints (T : Over (Spec (CommRingCat.of F)))
    (x : Multiplicative (traceZero ((algΓ (CommRingCat.of F)).obj T).unop c)) :
    pointsEquiv b c T (lowerRootPoints b c T x) = lowerRoot _ c x :=
  MulEquiv.apply_symm_apply _ _

/-- The opposite cocharacter is the pointwise inverse of the cocharacter. -/
theorem inverseCocharacter_points (T : Over (Spec (CommRingCat.of F)))
    (t : T ⟶ (Gm (Spec (CommRingCat.of F))).X) :
    t ≫ (inverseCocharacter b c).hom.hom = (t ≫ (cocharacter b c).hom.hom)⁻¹ := by
  apply (pointsEquiv b c T).injective
  simp only [cocharacter, inverseCocharacter, pointsEquiv_weightCocharacter, map_inv]
  exact diagonalUnitary_neg_one _ c _

/-- Conjugation of upper root points over every test scheme. -/
theorem cocharacter_upperRootPoints (T : Over (Spec (CommRingCat.of F)))
    (t : T ⟶ (Gm (Spec (CommRingCat.of F))).X)
    (x : traceZero ((algΓ (CommRingCat.of F)).obj T).unop c) :
    (t ≫ (cocharacter b c).hom.hom) * upperRootPoints b c T (Multiplicative.ofAdd x) *
        (t ≫ (cocharacter b c).hom.hom)⁻¹ =
      upperRootPoints b c T
        (Multiplicative.ofAdd (scaleTraceZero ((algΓ (CommRingCat.of F)).obj T).unop
          c (Gm.pointsEquiv _ T t) 2 x)) := by
  apply (pointsEquiv b c T).injective
  simp only [cocharacter, map_mul, map_inv, pointsEquiv_weightCocharacter,
    pointsEquiv_upperRootPoints]
  exact diagonalUnitary_upperRoot _ c _ x

/-- Conjugation of lower root points over every test scheme. -/
theorem cocharacter_lowerRootPoints (T : Over (Spec (CommRingCat.of F)))
    (t : T ⟶ (Gm (Spec (CommRingCat.of F))).X)
    (x : traceZero ((algΓ (CommRingCat.of F)).obj T).unop c) :
    (t ≫ (cocharacter b c).hom.hom) * lowerRootPoints b c T (Multiplicative.ofAdd x) *
        (t ≫ (cocharacter b c).hom.hom)⁻¹ =
      lowerRootPoints b c T
        (Multiplicative.ofAdd (scaleTraceZero ((algΓ (CommRingCat.of F)).obj T).unop
          c (Gm.pointsEquiv _ T t) (-2) x)) := by
  apply (pointsEquiv b c T).injective
  simp only [cocharacter, map_mul, map_inv, pointsEquiv_weightCocharacter,
    pointsEquiv_lowerRootPoints]
  exact diagonalUnitary_lowerRoot _ c _ x

end Schemes
end Langlands.GroupScheme.QuasiSplitUnitary
