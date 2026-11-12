import Langlands.GroupScheme.Quaternionic.HyperbolicIsometryExtension
import Langlands.GroupScheme.Quaternionic.TensorMatrixComparison

/-! # The ambient hyperbolic-plane isometry morphism -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.HyperbolicScheme

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]


/-- Scalar extension of a rectangular coefficient matrix. -/
def scalarMatrix (R : Type u) [CommRing R] [Algebra K R] {m n : Type}
    (M : Matrix m n D) : Matrix m n (R ⊗[K] D) :=
  M.map (Algebra.TensorProduct.includeRight : D →ₐ[K] R ⊗[K] D).toRingHom

@[simp] theorem scalarMatrix_mul (R : Type u) [CommRing R] [Algebra K R]
    {l m n : Type} [Fintype m] (M : Matrix l m D) (N : Matrix m n D) :
    scalarMatrix (K := K) R (M * N) = scalarMatrix (K := K) R M * scalarMatrix (K := K) R N := by
  exact Matrix.map_mul

@[simp] theorem scalarMatrix_one (R : Type u) [CommRing R] [Algebra K R]
    (n : Type) [DecidableEq n] : scalarMatrix (K := K) R (1 : Matrix n n D) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [scalarMatrix, Matrix.one_apply, hij, Algebra.TensorProduct.one_def]

@[simp] theorem scalarMatrix_sub (R : Type u) [CommRing R] [Algebra K R]
    {m n : Type} (M N : Matrix m n D) :
    scalarMatrix (K := K) R (M - N) = scalarMatrix (K := K) R M - scalarMatrix (K := K) R N := by
  ext i j
  simp [scalarMatrix, TensorProduct.tmul_sub]

theorem scalarMatrix_naturality {R S : Type u} [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (a : R →ₐ[K] S) {m n : Type} (M : Matrix m n D) :
    (scalarMatrix (K := K) R M).map (Algebra.TensorProduct.map a (AlgHom.id K D)) =
      scalarMatrix (K := K) S M := by
  ext i j
  simp [scalarMatrix]

variable [FiniteDimensional K D]

variable (n : Type) [Fintype n] [DecidableEq n]

/-- Actual relative test points of the matrix-unit group, in matrix coordinates. -/
def matrixPointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D))).X) ≃*
      (Matrix n n (BinaryScheme.coefficients T ⊗[K] D))ˣ :=
  (FiniteAlgebraUnits.pointsEquiv _ T).trans
    (Units.mapEquiv (TensorMatrix.equiv (BinaryScheme.coefficients T) n).toMulEquiv)

/-- Matrix coordinates commute with all relative test restrictions. -/
theorem matrixPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T)
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D))).X) :
    (matrixPointsEquiv n T' (a ≫ x) : Matrix n n (BinaryScheme.coefficients T' ⊗[K] D)) =
      (matrixPointsEquiv n T x : Matrix n n (BinaryScheme.coefficients T ⊗[K] D)).map
        (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
          (AlgHom.id K D)) := by
  change TensorMatrix.equiv (BinaryScheme.coefficients T') n
    (FiniteAlgebraUnits.pointsEquiv _ T' (a ≫ x) :
      BinaryScheme.coefficients T' ⊗[K] Matrix n n D) = _
  rw [FiniteAlgebraUnits.pointsEquiv_naturality]
  exact TensorMatrix.naturality _ _

variable (σ : FirstKindInvolution K D) (q : σ.QuadraticForms n) (e f : n → D)

/-- The hyperbolic plane inclusion over an arbitrary coefficient algebra. -/
def inclusion (R : Type u) [CommRing R] [Algebra K R] :
    Matrix (Fin 2) n (R ⊗[K] D) :=
  scalarMatrix (K := K) R (FirstKindInvolution.planeInclusion e f)

/-- The actual polar-coordinate retraction after scalar extension. -/
def retraction (R : Type u) [CommRing R] [Algebra K R] :
    Matrix n (Fin 2) (R ⊗[K] D) :=
  scalarMatrix (K := K) R (FirstKindInvolution.planeRetraction σ q e f)

variable {n σ q e f} (h : σ.IsHyperbolicPair q e f)

include h in
omit [FiniteDimensional K D] in
/-- The plane remains a split summand over every coefficient algebra. -/
theorem inclusion_mul_retraction (R : Type u) [CommRing R] [Algebra K R] :
    inclusion (K := K) n e f R * retraction n σ q e f R = 1 := by
  rw [inclusion, retraction, ← scalarMatrix_mul, h.planeInclusion_mul_retraction,
    scalarMatrix_one]

/-- Extend every binary unit by the identity on the actual complementary summand. -/
def extendUnits (R : Type u) [CommRing R] [Algebra K R] :
    (Matrix (Fin 2) (Fin 2) (R ⊗[K] D))ˣ →* (Matrix n n (R ⊗[K] D))ˣ :=
  SplitMatrixExtension.unitsHom _ _ (inclusion_mul_retraction h R)

omit [FiniteDimensional K D] in
/-- Extension retains the entire binary unit, over rings with nilpotents as well. -/
theorem extendUnits_injective (R : Type u) [CommRing R] [Algebra K R] :
    Function.Injective (extendUnits h R) :=
  SplitMatrixExtension.unitsHom_injective _ _ _

omit [FiniteDimensional K D] in
/-- The extended matrix is compatible with every coefficient-algebra morphism. -/
theorem extendUnits_naturality {R S : Type u} [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (a : R →ₐ[K] S)
    (g : (Matrix (Fin 2) (Fin 2) (R ⊗[K] D))ˣ)
    (g' : (Matrix (Fin 2) (Fin 2) (S ⊗[K] D))ˣ)
    (hg : (g' : Matrix (Fin 2) (Fin 2) (S ⊗[K] D)) =
      (g : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)).map
        (Algebra.TensorProduct.map a (AlgHom.id K D))) :
    (extendUnits h S g' : Matrix n n (S ⊗[K] D)) =
      (extendUnits h R g : Matrix n n (R ⊗[K] D)).map
        (Algebra.TensorProduct.map a (AlgHom.id K D)) := by
  change SplitMatrixExtension.value _ _ _ = (SplitMatrixExtension.value _ _ _).map _
  have hm := SplitMatrixExtension.value_map
    (inclusion (K := K) n e f R) (retraction n σ q e f R)
    (Algebra.TensorProduct.map a (AlgHom.id K D)).toRingHom
    (g : Matrix (Fin 2) (Fin 2) (R ⊗[K] D))
  rw [hg]
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, inclusion, retraction,
    scalarMatrix_naturality] using hm.symm

/-- The ambient unit matrix attached to a relative binary-unit point. -/
def pointMatrix (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) →*
      (Matrix n n (BinaryScheme.coefficients T ⊗[K] D))ˣ :=
  (extendUnits h (BinaryScheme.coefficients T)).comp (matrixPointsEquiv (Fin 2) T).toMonoidHom

/-- Extension is natural on every relative scheme, including non-affine tests. -/
theorem pointMatrix_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T)
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) :
    (pointMatrix h T' (a ≫ x) : Matrix n n (BinaryScheme.coefficients T' ⊗[K] D)) =
      (pointMatrix h T x : Matrix n n (BinaryScheme.coefficients T ⊗[K] D)).map
        (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
          (AlgHom.id K D)) :=
  extendUnits_naturality h _ _ _ (matrixPointsEquiv_naturality (Fin 2) a x)

/-- Natural all-test homomorphisms into the ambient matrix-unit group. -/
def unitPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) →*
      (T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D))).X) :=
  (matrixPointsEquiv n T).symm.toMonoidHom.comp (pointMatrix h T)

@[simp] theorem unitPoints_matrix (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) :
    matrixPointsEquiv n T (unitPoints h T x) = pointMatrix h T x :=
  (matrixPointsEquiv n T).apply_symm_apply _

theorem unitPoints_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (a : T' ⟶ T)
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) :
    unitPoints h T' (a ≫ x) = a ≫ unitPoints h T x := by
  apply (matrixPointsEquiv n T').injective
  apply Units.ext
  rw [unitPoints_matrix, matrixPointsEquiv_naturality, unitPoints_matrix]
  exact pointMatrix_naturality h a x

/-- The actual matrix-unit group-scheme morphism extending the hyperbolic plane. -/
def unitHom :
    FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix (Fin 2) (Fin 2) D)) ⟶
      FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D)) :=
  homOfPoints (unitPoints h) (unitPoints_naturality h)

/-- The morphism recovers its prescribed matrix formula on every relative test. -/
@[simp] theorem unitHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme
      (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) :
    matrixPointsEquiv n T (x ≫ (unitHom h).hom.hom) = pointMatrix h T x := by
  rw [unitHom, comp_homOfPoints, unitPoints_matrix]


omit [FiniteDimensional K D] in
/-- Scalar extension commutes with rectangular adjoints. -/
theorem scalarMatrix_adjoint (R : Type u) [CommRing R] [Algebra K R]
    {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    (M : Matrix m l D) :
    scalarMatrix (K := K) R (σ.rectangularAdjoint M) =
      SplitQuadraticExtension.adjoint (σ.baseChange R) (scalarMatrix (K := K) R M) := by
  ext i j
  rfl

omit [FiniteDimensional K D] in
/-- The chosen representative remains the actual split representative after base change. -/
theorem scalarMatrix_splitRepresentative (R : Type u) [CommRing R] [Algebra K R] :
    scalarMatrix (K := K) R
      (FirstKindInvolution.IsHyperbolicPair.splitRepresentative
        (σ := σ) (q := q) (e := e) (f := f)) =
      retraction n σ q e f R *
          scalarMatrix (K := K) R (BinaryAction.hyperbolicMatrix : Matrix (Fin 2) (Fin 2) D) *
          SplitQuadraticExtension.adjoint (σ.baseChange R) (retraction n σ q e f R) +
        (1 - retraction n σ q e f R * inclusion (K := K) n e f R) *
          scalarMatrix (K := K) R (Quotient.out q) *
          (σ.baseChange R).matrix n
            (1 - retraction n σ q e f R * inclusion (K := K) n e f R) := by
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
  simp only [FirstKindInvolution.IsHyperbolicPair.splitRepresentative, hadd,
    scalarMatrix_mul, scalarMatrix_adjoint, hadj, FirstKindInvolution.planeComplement,
    scalarMatrix_sub, scalarMatrix_one, inclusion, retraction]

include h in
omit [FiniteDimensional K D] in
/-- Extending a binary isometry preserves the actual ambient quadratic class over every ring. -/
theorem extendUnits_preserves (R : Type u) [CommRing R] [Algebra K R]
    (g : (Matrix (Fin 2) (Fin 2) (R ⊗[K] D))ˣ)
    (hg : (g : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) *
        scalarMatrix (K := K) R (BinaryAction.hyperbolicMatrix : Matrix (Fin 2) (Fin 2) D) *
        (σ.baseChange R).matrix (Fin 2) g -
        scalarMatrix (K := K) R (BinaryAction.hyperbolicMatrix : Matrix (Fin 2) (Fin 2) D) ∈
      ((σ.baseChange R).matrix (Fin 2)).alternatingSubspace) :
    let Q := scalarMatrix (K := K) R
      (FirstKindInvolution.IsHyperbolicPair.splitRepresentative
        (σ := σ) (q := q) (e := e) (f := f))
    (extendUnits h R g : Matrix n n (R ⊗[K] D)) * Q *
      (σ.baseChange R).matrix n (extendUnits h R g) - Q ∈
        ((σ.baseChange R).matrix n).alternatingSubspace := by
  dsimp only
  rw [scalarMatrix_splitRepresentative]
  exact SplitQuadraticExtension.defect_mem (σ.baseChange R)
    (inclusion (K := K) n e f R) (retraction n σ q e f R)
    (inclusion_mul_retraction h R) _ _ (scalarMatrix (K := K) R (Quotient.out q)) hg

/-- Extend actual binary isometry points into the ambient matrix-unit group. -/
def isometryUnitHom : σ.isometryGroup (BinaryScheme.hyperbolicForm σ) ⟶
    FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D)) :=
  σ.isometryGroupι (BinaryScheme.hyperbolicForm σ) ≫ unitHom h

set_option maxHeartbeats 1600000 in
/-- The represented all-test extension takes values in the actual ambient isometry group. -/
theorem isometryUnitHom_range_le :
    SubgroupFunctor.range (isometryUnitHom h) ≤ SubgroupFunctor.range (σ.isometryGroupι q) := by
  intro T z hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  rw [σ.mem_range_isometryGroupι_iff q
    (FirstKindInvolution.IsHyperbolicPair.splitRepresentative
      (σ := σ) (q := q) (e := e) (f := f)) h.mk_splitRepresentative]
  change IsometryCut.defect (σ.matrix n) _ _ ∈
    (σ.matrix n).alternatingSubspace.baseChange (BinaryScheme.coefficients T)
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    TensorMatrix.mem_alternating_iff]
  have hb : x ≫ (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ)).hom.hom ∈
      (SubgroupFunctor.range (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ))).carrier T :=
    SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  rw [σ.mem_range_isometryGroupι_iff (BinaryScheme.hyperbolicForm σ)
    BinaryAction.hyperbolicMatrix rfl] at hb
  change IsometryCut.defect (σ.matrix (Fin 2)) _ _ ∈
    (σ.matrix (Fin 2)).alternatingSubspace.baseChange (BinaryScheme.coefficients T) at hb
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    TensorMatrix.mem_alternating_iff] at hb
  rw [IsometryCut.defect, _root_.map_sub, _root_.map_mul, _root_.map_mul,
    TensorMatrix.adjoint] at hb ⊢
  have hu := congrArg
    (fun v : (Matrix n n (BinaryScheme.coefficients T ⊗[K] D))ˣ =>
      (v : Matrix n n (BinaryScheme.coefficients T ⊗[K] D)))
    (unitHom_points h T (x ≫ (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ)).hom.hom))
  change TensorMatrix.equiv (BinaryScheme.coefficients T) n
    (FiniteAlgebraUnits.pointsEquiv _ T
      ((x ≫ (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ)).hom.hom) ≫ (unitHom h).hom.hom) :
        BinaryScheme.coefficients T ⊗[K] Matrix n n D) = _ at hu
  have hu' : TensorMatrix.equiv (BinaryScheme.coefficients T) n
      (FiniteAlgebraUnits.pointsEquiv _ T (x ≫ (isometryUnitHom h).hom.hom) :
        BinaryScheme.coefficients T ⊗[K] Matrix n n D) =
      (pointMatrix h T (x ≫ (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ)).hom.hom) :
        Matrix n n (BinaryScheme.coefficients T ⊗[K] D)) := by
    simpa only [isometryUnitHom, Grp.comp_hom_hom, Category.assoc] using hu
  rw [hu']
  exact extendUnits_preserves h (BinaryScheme.coefficients T)
    (matrixPointsEquiv (Fin 2) T
      (x ≫ (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ)).hom.hom)) hb

private theorem isometry_represents :
    (SubgroupFunctor.range (σ.isometryGroupι q)).IsRepresentedBy (σ.isometryGroupι q) :=
  ⟨(σ.isClosedSubgroup_isometryGroupι q).mono_overHom, rfl⟩

/-- The actual hyperbolic-plane extension into the ambient isometry group. -/
def isometryHom : σ.isometryGroup (BinaryScheme.hyperbolicForm σ) ⟶ σ.isometryGroup q :=
  (isometry_represents (σ := σ) (q := q)).factorHom (isometryUnitHom h) (isometryUnitHom_range_le h)

/-- The isometry extension has its prescribed matrix-unit action. -/
@[reassoc] theorem isometryHom_comp :
    isometryHom h ≫ σ.isometryGroupι q = isometryUnitHom h :=
  (isometry_represents (σ := σ) (q := q)).factorHom_comp _ _


/-- The full matrix-unit extension is injective on every relative test scheme. -/
theorem unitHom_points_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (fun x => x ≫ (unitHom h).hom.hom :
      (T ⟶ (FiniteAlgebraUnits.groupScheme
        (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) →
        (T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D))).X)) := by
  intro x y hxy
  apply (matrixPointsEquiv (Fin 2) T).injective
  apply extendUnits_injective h (BinaryScheme.coefficients T)
  have hc := congrArg (matrixPointsEquiv n T) hxy
  simpa only [unitHom_points, pointMatrix, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hc

/-- The actual isometry morphism recovers the extension formula on every relative test. -/
theorem isometryHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (σ.isometryGroup (BinaryScheme.hyperbolicForm σ)).X) :
    matrixPointsEquiv n T ((x ≫ (isometryHom h).hom.hom) ≫ (σ.isometryGroupι q).hom.hom) =
      extendUnits h (BinaryScheme.coefficients T)
        (matrixPointsEquiv (Fin 2) T
          (x ≫ (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ)).hom.hom)) := by
  rw [Category.assoc, ← Grp.comp_hom_hom, isometryHom_comp]
  change matrixPointsEquiv n T (x ≫
    (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ) ≫ unitHom h).hom.hom) = _
  rw [Grp.comp_hom_hom, ← Category.assoc, unitHom_points]
  rfl

/-- Extending by the identity loses no isometry point, over any relative test scheme. -/
theorem isometryHom_points_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (fun x => x ≫ (isometryHom h).hom.hom :
      (T ⟶ (σ.isometryGroup (BinaryScheme.hyperbolicForm σ)).X) →
        (T ⟶ (σ.isometryGroup q).X)) := by
  intro x y hxy
  apply (isometry_represents (σ := σ) (q := BinaryScheme.hyperbolicForm σ)).1.right_cancellation
  apply (matrixPointsEquiv (Fin 2) T).injective
  apply extendUnits_injective h (BinaryScheme.coefficients T)
  have hc := congrArg (fun z => matrixPointsEquiv n T (z ≫ (σ.isometryGroupι q).hom.hom)) hxy
  simpa only [isometryHom_points] using hc

end Langlands.GroupScheme.Quaternionic.HyperbolicScheme
