import Langlands.GroupScheme.Quaternionic.HyperbolicGroupSchemeExtension

/-! # Extending isometries from a nondegenerate block of rows -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SubspaceScheme

open FirstKindInvolution

/-! ### Polar coordinates relative to a block of rows -/

section Algebra

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n k : Type} [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k]

/-- Changing both row arguments of the sesquilinear form by square matrices. -/
theorem sesqForm_vecMul_vecMul (H A C : Matrix n n D) (x y : n → D) :
    σ.sesqForm H (x ᵥ* A) (y ᵥ* C) = σ.sesqForm (A * H * σ.matrix n C) x y := by
  simp only [σ.sesqForm_eq_dotProduct, σ.map_vecMul, mulVec_mulVec,
    dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]

variable (q : σ.QuadraticForms n) (E : Matrix k n D)

/-- Polar coordinates relative to the rows of `E`: `R = B E* G⁻¹`, where `B` is the polar Gram
matrix of `q` and `G = E B E*` is the polar Gram matrix of the rows of `E`. -/
def retractionMatrix : Matrix n k D :=
  σ.polar q * σ.rectangularAdjoint E *
    Ring.inverse (E * σ.polar q * σ.rectangularAdjoint E)

/-- The projection onto the polar orthogonal complement of the rows of `E`. -/
def complement : Matrix n n D :=
  1 - retractionMatrix σ q E * E

variable {σ q E} (hE : IsUnit (E * σ.polar q * σ.rectangularAdjoint E))

include hE in
/-- Polar coordinates retract onto the row space of `E`. -/
theorem mul_retractionMatrix : E * retractionMatrix σ q E = 1 := by
  calc E * retractionMatrix σ q E =
        E * σ.polar q * σ.rectangularAdjoint E *
          Ring.inverse (E * σ.polar q * σ.rectangularAdjoint E) := by
        rw [retractionMatrix]
        simp only [Matrix.mul_assoc]
    _ = 1 := Ring.mul_inverse_cancel _ hE

include hE in
/-- The complementary projection is polar-orthogonal to the rows of `E`. -/
theorem complement_mul_polar_mul_adjoint :
    complement σ q E * σ.polar q * σ.rectangularAdjoint E = 0 := by
  have h : retractionMatrix σ q E * E * σ.polar q * σ.rectangularAdjoint E =
      σ.polar q * σ.rectangularAdjoint E := by
    calc retractionMatrix σ q E * E * σ.polar q * σ.rectangularAdjoint E =
          σ.polar q * σ.rectangularAdjoint E *
            (Ring.inverse (E * σ.polar q * σ.rectangularAdjoint E) *
              (E * σ.polar q * σ.rectangularAdjoint E)) := by
          rw [retractionMatrix]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [Ring.inverse_mul_cancel _ hE, Matrix.mul_one]
  rw [complement, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, h, sub_self]

include hE in
/-- The rows of `E` are polar-orthogonal to the complementary projection. -/
theorem mul_polar_mul_adjoint_complement :
    E * σ.polar q * σ.matrix n (complement σ q E) = 0 := by
  calc E * σ.polar q * σ.matrix n (complement σ q E) =
        σ.rectangularAdjoint (complement σ q E * σ.polar q * σ.rectangularAdjoint E) := by
        simp only [rectangularAdjoint_mul, rectangularAdjoint_rectangularAdjoint,
          rectangularAdjoint_square, matrix_polar, Matrix.mul_assoc]
    _ = 0 := by
        rw [complement_mul_polar_mul_adjoint hE]
        ext i j
        simp

include hE in
/-- A vector of the complement pairs to zero with every vector of the row space. -/
theorem sesqForm_complement_vecMul (v : n → D) (w : k → D) :
    σ.sesqForm (σ.polar q) (v ᵥ* complement σ q E) (w ᵥ* E) = 0 := by
  rw [σ.sesqForm_eq_dotProduct, show σ ∘ (w ᵥ* E) = σ.rectangularAdjoint E *ᵥ (σ ∘ w) from
    (σ.rectangularAdjoint_mulVec E w).symm, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc, complement_mul_polar_mul_adjoint hE, zero_mulVec, dotProduct_zero]

include hE in
/-- The row-space part and the complementary part are polar-orthogonal. -/
theorem sesqForm_projection_complement (v w : n → D) :
    σ.sesqForm (σ.polar q) (v ᵥ* (retractionMatrix σ q E * E)) (w ᵥ* complement σ q E) = 0 := by
  have h0 : retractionMatrix σ q E * E * σ.polar q * σ.matrix n (complement σ q E) = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc E,
      mul_polar_mul_adjoint_complement hE, Matrix.mul_zero]
  rw [sesqForm_vecMul_vecMul, h0]
  simp [sesqForm]

include hE in
/-- The actual quotient form is the sum of its pullbacks to the row space and to the
polar complement. -/
theorem quadratic_decomposition :
    σ.quadraticPullback (retractionMatrix σ q E) (σ.quadraticPullback E q) +
      σ.quadraticPullback (complement σ q E) q = q := by
  apply σ.quadraticValue_ext
  intro v
  rw [LinearMap.map_add, quadraticValue_quadraticPullback, quadraticValue_quadraticPullback,
    quadraticValue_quadraticPullback, vecMul_vecMul]
  conv_rhs => rw [show v = v ᵥ* (retractionMatrix σ q E * E) + v ᵥ* complement σ q E by
    rw [← vecMul_add, complement, add_sub_cancel, vecMul_one]]
  rw [quadraticValue_add, sesqForm_projection_complement hE, Submodule.Quotient.mk_zero,
    add_zero]

variable (σ q E) in
/-- A representative of `q` adapted to the polar direct sum of the row space of `E` and its
complement. -/
def splitRepresentative : Matrix n n D :=
  retractionMatrix σ q E * Quotient.out (σ.quadraticPullback E q) *
      σ.rectangularAdjoint (retractionMatrix σ q E) +
    complement σ q E * Quotient.out q * σ.matrix n (complement σ q E)

include hE in
theorem mk_splitRepresentative :
    (Submodule.Quotient.mk (splitRepresentative σ q E) : σ.QuadraticForms n) = q := by
  change σ.quadraticPullback (retractionMatrix σ q E)
      (Submodule.Quotient.mk (Quotient.out (σ.quadraticPullback E q))) +
    σ.quadraticPullback (complement σ q E) (Submodule.Quotient.mk (Quotient.out q)) = q
  rw [Submodule.Quotient.mk_out, Submodule.Quotient.mk_out]
  exact quadratic_decomposition hE

end Algebra

/-! ### The ambient group-scheme morphism -/

section Scheme

open HyperbolicScheme (scalarMatrix scalarMatrix_mul scalarMatrix_one scalarMatrix_sub
  scalarMatrix_naturality scalarMatrix_adjoint matrixPointsEquiv matrixPointsEquiv_naturality)

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n k : Type} [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k] (q : σ.QuadraticForms n) (E : Matrix k n D)

/-- The rows of `E` over an arbitrary coefficient algebra. -/
def inclusion (R : Type u) [CommRing R] [Algebra K R] : Matrix k n (R ⊗[K] D) :=
  scalarMatrix (K := K) R E

/-- The polar-coordinate retraction after scalar extension. -/
def retraction (R : Type u) [CommRing R] [Algebra K R] : Matrix n k (R ⊗[K] D) :=
  scalarMatrix (K := K) R (retractionMatrix σ q E)

variable {σ q E} (hE : IsUnit (E * σ.polar q * σ.rectangularAdjoint E))

include hE in
/-- The row space remains a split summand over every coefficient algebra. -/
theorem inclusion_mul_retraction (R : Type u) [CommRing R] [Algebra K R] :
    inclusion (K := K) E R * retraction σ q E R = 1 := by
  rw [inclusion, retraction, ← scalarMatrix_mul, mul_retractionMatrix hE, scalarMatrix_one]

/-- Extend every unit on the row space by the identity on the polar complement. -/
def extendUnits (R : Type u) [CommRing R] [Algebra K R] :
    (Matrix k k (R ⊗[K] D))ˣ →* (Matrix n n (R ⊗[K] D))ˣ :=
  SplitMatrixExtension.unitsHom _ _ (inclusion_mul_retraction hE R)

/-- Extension retains the entire unit, over rings with nilpotents as well. -/
theorem extendUnits_injective (R : Type u) [CommRing R] [Algebra K R] :
    Function.Injective (extendUnits hE R) :=
  SplitMatrixExtension.unitsHom_injective _ _ _

/-- The extended matrix is compatible with every coefficient-algebra morphism. -/
theorem extendUnits_naturality {R S : Type u} [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (a : R →ₐ[K] S)
    (g : (Matrix k k (R ⊗[K] D))ˣ) (g' : (Matrix k k (S ⊗[K] D))ˣ)
    (hg : (g' : Matrix k k (S ⊗[K] D)) =
      (g : Matrix k k (R ⊗[K] D)).map (Algebra.TensorProduct.map a (AlgHom.id K D))) :
    (extendUnits hE S g' : Matrix n n (S ⊗[K] D)) =
      (extendUnits hE R g : Matrix n n (R ⊗[K] D)).map
        (Algebra.TensorProduct.map a (AlgHom.id K D)) := by
  change SplitMatrixExtension.value _ _ _ = (SplitMatrixExtension.value _ _ _).map _
  have hm := SplitMatrixExtension.value_map
    (inclusion (K := K) E R) (retraction σ q E R)
    (Algebra.TensorProduct.map a (AlgHom.id K D)).toRingHom
    (g : Matrix k k (R ⊗[K] D))
  rw [hg]
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, inclusion, retraction,
    scalarMatrix_naturality] using hm.symm

variable (σ q E) in
/-- The chosen split representative remains split after base change. -/
theorem scalarMatrix_splitRepresentative (R : Type u) [CommRing R] [Algebra K R] :
    scalarMatrix (K := K) R (splitRepresentative σ q E) =
      retraction σ q E R * scalarMatrix (K := K) R (Quotient.out (σ.quadraticPullback E q)) *
          SplitQuadraticExtension.adjoint (σ.baseChange R) (retraction σ q E R) +
        (1 - retraction σ q E R * inclusion (K := K) E R) *
          scalarMatrix (K := K) R (Quotient.out q) *
          (σ.baseChange R).matrix n (1 - retraction σ q E R * inclusion (K := K) E R) := by
  have hadd {m l : Type} (M N : Matrix m l D) :
      scalarMatrix (K := K) R (M + N) =
        scalarMatrix (K := K) R M + scalarMatrix (K := K) R N := by
    ext i j
    simp [scalarMatrix, TensorProduct.tmul_add]
  have hadj (M : Matrix n n D) :
      scalarMatrix (K := K) R (σ.matrix n M) =
        (σ.baseChange R).matrix n (scalarMatrix (K := K) R M) := by
    ext i j
    rfl
  simp only [splitRepresentative, hadd, scalarMatrix_mul, scalarMatrix_adjoint, hadj, complement,
    scalarMatrix_sub, scalarMatrix_one, inclusion, retraction]

include hE in
/-- Extending an isometry of the row space preserves the ambient quadratic class over every
coefficient algebra. -/
theorem extendUnits_preserves (R : Type u) [CommRing R] [Algebra K R]
    (g : (Matrix k k (R ⊗[K] D))ˣ)
    (hg : (g : Matrix k k (R ⊗[K] D)) *
        scalarMatrix (K := K) R (Quotient.out (σ.quadraticPullback E q)) *
        (σ.baseChange R).matrix k g -
        scalarMatrix (K := K) R (Quotient.out (σ.quadraticPullback E q)) ∈
      ((σ.baseChange R).matrix k).alternatingSubspace) :
    let Q := scalarMatrix (K := K) R (splitRepresentative σ q E)
    (extendUnits hE R g : Matrix n n (R ⊗[K] D)) * Q *
      (σ.baseChange R).matrix n (extendUnits hE R g) - Q ∈
        ((σ.baseChange R).matrix n).alternatingSubspace := by
  dsimp only
  rw [scalarMatrix_splitRepresentative]
  exact SplitQuadraticExtension.defect_mem (σ.baseChange R)
    (inclusion (K := K) E R) (retraction σ q E R)
    (inclusion_mul_retraction hE R) _ _ (scalarMatrix (K := K) R (Quotient.out q)) hg

variable [FiniteDimensional K D]

/-- The ambient unit matrix attached to a relative unit point on the row space. -/
def pointMatrix (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix k k D))).X) →*
      (Matrix n n (BinaryScheme.coefficients T ⊗[K] D))ˣ :=
  (extendUnits hE (BinaryScheme.coefficients T)).comp (matrixPointsEquiv k T).toMonoidHom

/-- Extension is natural on every relative scheme, including non-affine tests. -/
theorem pointMatrix_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix k k D))).X) :
    (pointMatrix hE T' (a ≫ x) : Matrix n n (BinaryScheme.coefficients T' ⊗[K] D)) =
      (pointMatrix hE T x : Matrix n n (BinaryScheme.coefficients T ⊗[K] D)).map
        (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
          (AlgHom.id K D)) :=
  extendUnits_naturality hE _ _ _ (matrixPointsEquiv_naturality k a x)

/-- Natural all-test homomorphisms into the ambient matrix-unit group. -/
def unitPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix k k D))).X) →*
      (T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D))).X) :=
  (matrixPointsEquiv n T).symm.toMonoidHom.comp (pointMatrix hE T)

@[simp] theorem unitPoints_matrix (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix k k D))).X) :
    matrixPointsEquiv n T (unitPoints hE T x) = pointMatrix hE T x :=
  (matrixPointsEquiv n T).apply_symm_apply _

theorem unitPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix k k D))).X) :
    unitPoints hE T' (a ≫ x) = a ≫ unitPoints hE T x := by
  apply (matrixPointsEquiv n T').injective
  apply Units.ext
  rw [unitPoints_matrix, matrixPointsEquiv_naturality, unitPoints_matrix]
  exact pointMatrix_naturality hE a x

/-- The matrix-unit group-scheme morphism extending the row space by the identity on its
polar complement. -/
def unitHom :
    FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix k k D)) ⟶
      FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D)) :=
  homOfPoints (unitPoints hE) (unitPoints_naturality hE)

/-- The morphism recovers its prescribed matrix formula on every relative test. -/
@[simp] theorem unitHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix k k D))).X) :
    matrixPointsEquiv n T (x ≫ (unitHom hE).hom.hom) = pointMatrix hE T x := by
  rw [unitHom, comp_homOfPoints, unitPoints_matrix]

/-- Extend isometry points of the row space into the ambient matrix-unit group. -/
def isometryUnitHom : σ.isometryGroup (σ.quadraticPullback E q) ⟶
    FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D)) :=
  σ.isometryGroupι (σ.quadraticPullback E q) ≫ unitHom hE

set_option maxHeartbeats 1600000 in
/-- The all-test extension takes values in the ambient isometry group. -/
theorem isometryUnitHom_range_le :
    SubgroupFunctor.range (isometryUnitHom hE) ≤ SubgroupFunctor.range (σ.isometryGroupι q) := by
  intro T z hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  rw [σ.mem_range_isometryGroupι_iff q (splitRepresentative σ q E) (mk_splitRepresentative hE)]
  change IsometryCut.defect (σ.matrix n) _ _ ∈
    (σ.matrix n).alternatingSubspace.baseChange (BinaryScheme.coefficients T)
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    TensorMatrix.mem_alternating_iff]
  have hb : x ≫ (σ.isometryGroupι (σ.quadraticPullback E q)).hom.hom ∈
      (SubgroupFunctor.range (σ.isometryGroupι (σ.quadraticPullback E q))).carrier T :=
    SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  rw [σ.mem_range_isometryGroupι_iff (σ.quadraticPullback E q)
    (Quotient.out (σ.quadraticPullback E q)) (Submodule.Quotient.mk_out _)] at hb
  change IsometryCut.defect (σ.matrix k) _ _ ∈
    (σ.matrix k).alternatingSubspace.baseChange (BinaryScheme.coefficients T) at hb
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    TensorMatrix.mem_alternating_iff] at hb
  rw [IsometryCut.defect, _root_.map_sub, _root_.map_mul, _root_.map_mul,
    TensorMatrix.adjoint] at hb ⊢
  have hu := congrArg
    (fun v : (Matrix n n (BinaryScheme.coefficients T ⊗[K] D))ˣ =>
      (v : Matrix n n (BinaryScheme.coefficients T ⊗[K] D)))
    (unitHom_points hE T (x ≫ (σ.isometryGroupι (σ.quadraticPullback E q)).hom.hom))
  change TensorMatrix.equiv (BinaryScheme.coefficients T) n
    (FiniteAlgebraUnits.pointsEquiv _ T
      ((x ≫ (σ.isometryGroupι (σ.quadraticPullback E q)).hom.hom) ≫ (unitHom hE).hom.hom) :
        BinaryScheme.coefficients T ⊗[K] Matrix n n D) = _ at hu
  have hu' : TensorMatrix.equiv (BinaryScheme.coefficients T) n
      (FiniteAlgebraUnits.pointsEquiv _ T (x ≫ (isometryUnitHom hE).hom.hom) :
        BinaryScheme.coefficients T ⊗[K] Matrix n n D) =
      (pointMatrix hE T (x ≫ (σ.isometryGroupι (σ.quadraticPullback E q)).hom.hom) :
        Matrix n n (BinaryScheme.coefficients T ⊗[K] D)) := by
    simpa only [isometryUnitHom, Grp.comp_hom_hom, Category.assoc] using hu
  rw [hu']
  exact extendUnits_preserves hE (BinaryScheme.coefficients T)
    (matrixPointsEquiv k T
      (x ≫ (σ.isometryGroupι (σ.quadraticPullback E q)).hom.hom)) hb

private theorem isometry_represents (q : σ.QuadraticForms n) :
    (SubgroupFunctor.range (σ.isometryGroupι q)).IsRepresentedBy (σ.isometryGroupι q) :=
  ⟨(σ.isClosedSubgroup_isometryGroupι q).mono_overHom, rfl⟩

/-- The extension from the isometry group of the row space into the ambient isometry group,
by the identity on the polar complement. -/
def isometryHom : σ.isometryGroup (σ.quadraticPullback E q) ⟶ σ.isometryGroup q :=
  (isometry_represents (σ := σ) q).factorHom (isometryUnitHom hE) (isometryUnitHom_range_le hE)

/-- The isometry extension has its prescribed matrix-unit action. -/
@[reassoc] theorem isometryHom_comp :
    isometryHom hE ≫ σ.isometryGroupι q = isometryUnitHom hE :=
  (isometry_represents (σ := σ) q).factorHom_comp _ _

/-- The isometry morphism recovers the extension formula on every relative test. -/
theorem isometryHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (σ.isometryGroup (σ.quadraticPullback E q)).X) :
    matrixPointsEquiv n T ((x ≫ (isometryHom hE).hom.hom) ≫ (σ.isometryGroupι q).hom.hom) =
      extendUnits hE (BinaryScheme.coefficients T)
        (matrixPointsEquiv k T
          (x ≫ (σ.isometryGroupι (σ.quadraticPullback E q)).hom.hom)) := by
  rw [Category.assoc, ← Grp.comp_hom_hom, isometryHom_comp]
  change matrixPointsEquiv n T (x ≫
    (σ.isometryGroupι (σ.quadraticPullback E q) ≫ unitHom hE).hom.hom) = _
  rw [Grp.comp_hom_hom, ← Category.assoc, unitHom_points]
  rfl

/-- Extending by the identity loses no isometry point, over any relative test scheme. -/
theorem isometryHom_points_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (fun x => x ≫ (isometryHom hE).hom.hom :
      (T ⟶ (σ.isometryGroup (σ.quadraticPullback E q)).X) → (T ⟶ (σ.isometryGroup q).X)) := by
  intro x y hxy
  apply (isometry_represents (σ := σ) (σ.quadraticPullback E q)).1.right_cancellation
  apply (matrixPointsEquiv k T).injective
  apply extendUnits_injective hE (BinaryScheme.coefficients T)
  have hc := congrArg (fun z => matrixPointsEquiv n T (z ≫ (σ.isometryGroupι q).hom.hom)) hxy
  simpa only [isometryHom_points] using hc

end Scheme

/-! ### Compatibility with a hyperbolic plane inside the row space -/

section Plane

/-- Extending in two split steps is extending along the composite split inclusion. -/
theorem value_value {A : Type*} [Ring A] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (E : Matrix m n A) (R : Matrix n m A) (I : Matrix l m A) (S : Matrix m l A)
    (M : Matrix l l A) :
    SplitMatrixExtension.value E R (SplitMatrixExtension.value I S M) =
      SplitMatrixExtension.value (I * E) (R * S) M := by
  simp only [SplitMatrixExtension.value, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {σ : FirstKindInvolution K D} {n k : Type} [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k] {q : σ.QuadraticForms n} {E : Matrix k n D}
  {e f : n → D} {i₀ i₁ : k}

omit [Fintype n] [DecidableEq n] in
theorem single_one_vecMul_eq (i : k) : (Pi.single i 1 : k → D) ᵥ* E = E i := by
  rw [single_one_vecMul]
  rfl

/-- Polar coordinates of a hyperbolic plane, written as a matrix product. -/
theorem planeRetraction_eq_polar_mul (q : σ.QuadraticForms n) (e f : n → D) :
    planeRetraction σ q e f = σ.polar q * σ.rectangularAdjoint (planeInclusion f e) := by
  ext i j
  fin_cases j <;>
    simp [planeRetraction, planeInclusion, rectangularAdjoint, Matrix.mul_apply, Matrix.mulVec,
      dotProduct]

/-- The standard rows at `i₀` and `i₁` form a hyperbolic pair of the pulled-back form whenever
the corresponding rows of `E` form a hyperbolic pair of `q`. -/
theorem isHyperbolicPair_single (he : E i₀ = e) (hf : E i₁ = f)
    (h : σ.IsHyperbolicPair q e f) :
    σ.IsHyperbolicPair (σ.quadraticPullback E q) (Pi.single i₀ 1) (Pi.single i₁ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [quadraticValue_quadraticPullback, single_one_vecMul_eq, he]
    exact h.1
  · rw [quadraticValue_quadraticPullback, single_one_vecMul_eq, hf]
    exact h.2.1
  · rw [polar_quadraticPullback, sesqForm_gramPullback, single_one_vecMul_eq,
      single_one_vecMul_eq, he, hf]
    exact h.2.2

omit [Fintype n] [DecidableEq n] in
/-- The plane of standard rows maps onto the plane spanned by `e` and `f`. -/
theorem planeInclusion_single_mul (he : E i₀ = e) (hf : E i₁ = f) :
    planeInclusion (Pi.single i₀ (1 : D)) (Pi.single i₁ 1) * E = planeInclusion e f := by
  ext i j
  have h0 := congrFun (single_one_vecMul_eq (E := E) i₀) j
  have h1 := congrFun (single_one_vecMul_eq (E := E) i₁) j
  fin_cases i
  · simpa [planeInclusion, Matrix.mul_apply, Matrix.vecMul, dotProduct, ← he] using h0
  · simpa [planeInclusion, Matrix.mul_apply, Matrix.vecMul, dotProduct, ← hf] using h1

/-- Polar coordinates of the plane in the row space, followed by polar coordinates of the row
space, are polar coordinates of the plane in the ambient space. -/
theorem retractionMatrix_mul_planeRetraction
    (hE : IsUnit (E * σ.polar q * σ.rectangularAdjoint E)) (he : E i₀ = e) (hf : E i₁ = f) :
    retractionMatrix σ q E *
        planeRetraction σ (σ.quadraticPullback E q) (Pi.single i₀ 1) (Pi.single i₁ 1) =
      planeRetraction σ q e f := by
  rw [planeRetraction_eq_polar_mul, planeRetraction_eq_polar_mul, polar_quadraticPullback,
    gramPullback_apply, ← planeInclusion_single_mul hf he, rectangularAdjoint_mul,
    retractionMatrix]
  calc σ.polar q * σ.rectangularAdjoint E *
        Ring.inverse (E * σ.polar q * σ.rectangularAdjoint E) *
        (E * σ.polar q * σ.rectangularAdjoint E *
          σ.rectangularAdjoint (planeInclusion (Pi.single i₁ 1) (Pi.single i₀ 1))) =
      σ.polar q * σ.rectangularAdjoint E *
        (Ring.inverse (E * σ.polar q * σ.rectangularAdjoint E) *
          (E * σ.polar q * σ.rectangularAdjoint E)) *
        σ.rectangularAdjoint (planeInclusion (Pi.single i₁ 1) (Pi.single i₀ 1)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Ring.inverse_mul_cancel _ hE, Matrix.mul_one, Matrix.mul_assoc]

variable [FiniteDimensional K D]

open HyperbolicScheme (scalarMatrix scalarMatrix_mul matrixPointsEquiv)

omit [FiniteDimensional K D] in
/-- On unit matrices, extending from the plane to the row space and then to the ambient space is
extending directly from the plane to the ambient space. -/
theorem extendUnits_hyperbolic (hE : IsUnit (E * σ.polar q * σ.rectangularAdjoint E))
    (he : E i₀ = e) (hf : E i₁ = f) (h : σ.IsHyperbolicPair q e f)
    (R : Type u) [CommRing R] [Algebra K R] (g : (Matrix (Fin 2) (Fin 2) (R ⊗[K] D))ˣ) :
    extendUnits hE R (HyperbolicScheme.extendUnits (isHyperbolicPair_single he hf h) R g) =
      HyperbolicScheme.extendUnits h R g := by
  apply Units.ext
  simp only [extendUnits, HyperbolicScheme.extendUnits, SplitMatrixExtension.unitsHom_val]
  rw [value_value]
  congr 1
  · simp only [HyperbolicScheme.inclusion, inclusion]
    rw [← scalarMatrix_mul, planeInclusion_single_mul he hf]
  · simp only [HyperbolicScheme.retraction, retraction]
    rw [← scalarMatrix_mul, retractionMatrix_mul_planeRetraction hE he hf]

/-- The extension from the hyperbolic plane spanned by the rows `E i₀ = e` and `E i₁ = f` factors
through the extension from the row space of `E`: first extend from the plane of standard rows
`Pi.single i₀ 1`, `Pi.single i₁ 1` to the row space, then extend from the row space to the
ambient space. -/
theorem hyperbolic_isometryHom_comp (hE : IsUnit (E * σ.polar q * σ.rectangularAdjoint E))
    (he : E i₀ = e) (hf : E i₁ = f) (h : σ.IsHyperbolicPair q e f) :
    HyperbolicScheme.isometryHom (isHyperbolicPair_single he hf h) ≫ isometryHom hE =
      HyperbolicScheme.isometryHom h := by
  apply hom_ext_points
  intro T x
  apply (isometry_represents (σ := σ) q).1.right_cancellation
  apply (matrixPointsEquiv n T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, isometryHom_points, HyperbolicScheme.isometryHom_points,
    HyperbolicScheme.isometryHom_points]
  exact extendUnits_hyperbolic hE he hf h _ _

end Plane

end Langlands.GroupScheme.Quaternionic.SubspaceScheme
