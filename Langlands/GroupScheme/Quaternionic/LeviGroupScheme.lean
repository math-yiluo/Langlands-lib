import Langlands.GroupScheme.Quaternionic.AmbientBinaryQuaternion
import Langlands.GroupScheme.Quaternionic.SpinEichlerLift
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Quaternionic.SpinKernelDescent

/-!
# The Levi morphism of a hyperbolic pair

For a hyperbolic pair `(e, f)` of a `σ`-quadratic form `q` on `D^n`, the Levi morphism
`leviHom h : GL₁(D) ⟶ O(q)` sends a unit `a` (over any coefficient algebra) to the isometry
`e ↦ a e`, `f ↦ σ(a)⁻¹ f`, identity on `{e, f}^⊥`. It is the composite of the binary Levi
morphism `GL₁(D) ⟶ O(H)`, `a ↦ diag(a, σ(a⁻¹))`, with the extension
`HyperbolicScheme.isometryHom h : O(H) ⟶ O(q)` of the hyperbolic plane.

On rational points it is the Levi homomorphism `levi` of `HyperbolicLevi`
(`isometryRationalMatrix_leviHom`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.LeviScheme

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] (σ : FirstKindInvolution K D)

/-! ### The binary Levi matrix -/

/-- The base-changed involution commutes with every change of coefficients. -/
theorem baseChange_map {R S : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (x : R ⊗[K] D) :
    Algebra.TensorProduct.map f (AlgHom.id K D) (σ.baseChange R x) =
      σ.baseChange S (Algebra.TensorProduct.map f (AlgHom.id K D) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r d => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The binary Levi matrix `diag(a, σ(a⁻¹))` over a coefficient algebra `R`. -/
abbrev leviMatrix (R : Type u) [CommRing R] [Algebra K R] :
    (R ⊗[K] D)ˣ →* (Matrix (Fin 2) (Fin 2) (R ⊗[K] D))ˣ :=
  BinaryAction.hyperbolicLevi (σ.baseChange R)

theorem leviMatrix_naturality {R S : Type u} [CommRing R] [Algebra K R] [CommRing S]
    [Algebra K S] (f : R →ₐ[K] S) (a : (R ⊗[K] D)ˣ) :
    (leviMatrix σ S (Units.map (Algebra.TensorProduct.map f (AlgHom.id K D)).toMonoidHom a) :
        Matrix (Fin 2) (Fin 2) (S ⊗[K] D)) =
      (leviMatrix σ R a : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)).map
        (Algebra.TensorProduct.map f (AlgHom.id K D)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [BinaryAction.hyperbolicLevi, baseChange_map]

/-- The binary Levi matrix preserves the hyperbolic matrix exactly. -/
theorem leviMatrix_isometry (R : Type u) [CommRing R] [Algebra K R] (a : (R ⊗[K] D)ˣ) :
    (leviMatrix σ R a : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) * BinaryAction.hyperbolicMatrix *
        (σ.baseChange R).matrix (Fin 2) (leviMatrix σ R a) =
      BinaryAction.hyperbolicMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BinaryAction.hyperbolicLevi, BinaryAction.hyperbolicMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem equiv_one_tmul_hyperbolicMatrix (R : Type u) [CommRing R] [Algebra K R] :
    TensorMatrix.equiv R (Fin 2)
        ((1 : R) ⊗ₜ[K] (BinaryAction.hyperbolicMatrix : Matrix (Fin 2) (Fin 2) D)) =
      BinaryAction.hyperbolicMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BinaryAction.hyperbolicMatrix, Algebra.TensorProduct.one_def]

/-! ### The binary Levi morphism -/

variable [FiniteDimensional K D]

/-- The binary Levi matrix on the points of `GL₁(D)` over every test scheme. -/
def leviPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K D)).X) →*
      (T ⟶ (FiniteAlgebraUnits.groupScheme
        (Module.finBasis K (Matrix (Fin 2) (Fin 2) D))).X) :=
  (HyperbolicScheme.matrixPointsEquiv (Fin 2) T).symm.toMonoidHom.comp
    ((leviMatrix σ (BinaryScheme.coefficients T)).comp
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K D) T).toMonoidHom)

@[simp] theorem leviPoints_matrix (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K D)).X) :
    HyperbolicScheme.matrixPointsEquiv (Fin 2) T (leviPoints σ T x) =
      leviMatrix σ _ (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K D) T x) :=
  (HyperbolicScheme.matrixPointsEquiv (Fin 2) T).apply_symm_apply _

theorem leviPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K D)).X) :
    leviPoints σ T' (a ≫ x) = a ≫ leviPoints σ T x := by
  apply (HyperbolicScheme.matrixPointsEquiv (Fin 2) T').injective
  apply Units.ext
  rw [leviPoints_matrix, HyperbolicScheme.matrixPointsEquiv_naturality, leviPoints_matrix,
    FiniteAlgebraUnits.pointsEquiv_naturality, leviMatrix_naturality]

/-- The binary Levi morphism into the unit group of `M₂(D)`. -/
def leviUnitHom : FiniteAlgebraUnits.groupScheme (Module.finBasis K D) ⟶
    FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix (Fin 2) (Fin 2) D)) :=
  homOfPoints (leviPoints σ) (leviPoints_naturality σ)

@[simp] theorem leviUnitHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K D)).X) :
    HyperbolicScheme.matrixPointsEquiv (Fin 2) T (x ≫ (leviUnitHom σ).hom.hom) =
      leviMatrix σ _ (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K D) T x) := by
  rw [leviUnitHom, comp_homOfPoints, leviPoints_matrix]

/-- The binary Levi morphism lands in the isometry group of the hyperbolic plane. -/
theorem leviUnitHom_range_le :
    SubgroupFunctor.range (leviUnitHom σ) ≤
      SubgroupFunctor.range (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ)) := by
  intro T z hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  rw [σ.mem_range_isometryGroupι_iff (BinaryScheme.hyperbolicForm σ)
    BinaryAction.hyperbolicMatrix rfl]
  change IsometryCut.defect (σ.matrix (Fin 2)) _ _ ∈
    (σ.matrix (Fin 2)).alternatingSubspace.baseChange (BinaryScheme.coefficients T)
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    TensorMatrix.mem_alternating_iff, IsometryCut.defect, _root_.map_sub, _root_.map_mul,
    _root_.map_mul, TensorMatrix.adjoint]
  have hu := congrArg
    (fun v : (Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T ⊗[K] D))ˣ =>
      (v : Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T ⊗[K] D)))
    (leviUnitHom_points σ T x)
  change TensorMatrix.equiv (BinaryScheme.coefficients T) (Fin 2)
    (FiniteAlgebraUnits.pointsEquiv _ T (x ≫ (leviUnitHom σ).hom.hom) :
      BinaryScheme.coefficients T ⊗[K] Matrix (Fin 2) (Fin 2) D) = _ at hu
  rw [hu, equiv_one_tmul_hyperbolicMatrix, leviMatrix_isometry, sub_self]
  exact Submodule.zero_mem _

private theorem isometry_represents :
    (SubgroupFunctor.range (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ))).IsRepresentedBy
      (σ.isometryGroupι (BinaryScheme.hyperbolicForm σ)) :=
  ⟨(σ.isClosedSubgroup_isometryGroupι _).mono_overHom, rfl⟩

/-- The binary Levi morphism `GL₁(D) ⟶ O(H)`, `a ↦ diag(a, σ(a⁻¹))`. -/
def binaryLeviHom : FiniteAlgebraUnits.groupScheme (Module.finBasis K D) ⟶
    σ.isometryGroup (BinaryScheme.hyperbolicForm σ) :=
  (isometry_represents σ).factorHom (leviUnitHom σ) (leviUnitHom_range_le σ)

@[reassoc] theorem binaryLeviHom_comp :
    binaryLeviHom σ ≫ σ.isometryGroupι (BinaryScheme.hyperbolicForm σ) = leviUnitHom σ :=
  (isometry_represents σ).factorHom_comp _ _

/-! ### The Levi morphism of a hyperbolic pair -/

variable {σ} {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n} {e f : n → D}
  (h : σ.IsHyperbolicPair q e f)

/-- **The Levi morphism** `GL₁(D) ⟶ O(q)` of a hyperbolic pair. -/
def leviHom : FiniteAlgebraUnits.groupScheme (Module.finBasis K D) ⟶ σ.isometryGroup q :=
  binaryLeviHom σ ≫ HyperbolicScheme.isometryHom h

/-- On every test scheme the Levi morphism is the extension of `diag(a, σ(a⁻¹))`. -/
theorem leviHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K D)).X) :
    HyperbolicScheme.matrixPointsEquiv n T
        ((x ≫ (leviHom h).hom.hom) ≫ (σ.isometryGroupι q).hom.hom) =
      HyperbolicScheme.extendUnits h (BinaryScheme.coefficients T)
        (leviMatrix σ _ (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K D) T x)) := by
  rw [leviHom, Grp.comp_hom_hom, ← Category.assoc, HyperbolicScheme.isometryHom_points,
    Category.assoc, ← Grp.comp_hom_hom, binaryLeviHom_comp, leviUnitHom_points]

/-! ### Rational points -/

/-- At an affine test, the all-test coordinates of a unit group are the affine coordinates
transported along the inverse section isomorphism. -/
theorem pointsEquiv_affine {A : Type u} [Ring A] [Algebra K A] [FiniteDimensional K A]
    (S : CommAlgCat.{u} (CommRingCat.of K))
    (x : (algSpec (CommRingCat.of K)).obj (op S) ⟶
      (FiniteAlgebraUnits.groupScheme (Module.finBasis K A)).X) :
    FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) _ x =
      Units.map (Algebra.TensorProduct.map (Corepresented.affineSectionsIso S).inv.hom
        (AlgHom.id K A)).toMonoidHom
        (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K A) S x) :=
  Corepresented.pointsEquiv_eq_affinePointsEquiv _ _ S x


omit [FiniteDimensional K D] in
theorem scalarMatrix_add (R : Type u) [CommRing R] [Algebra K R] {l m : Type}
    (M N : Matrix l m D) :
    HyperbolicScheme.scalarMatrix (K := K) R (M + N) =
      HyperbolicScheme.scalarMatrix (K := K) R M + HyperbolicScheme.scalarMatrix (K := K) R N := by
  ext i j
  simp [HyperbolicScheme.scalarMatrix, TensorProduct.tmul_add]

omit [FiniteDimensional K D] in
/-- The split extension commutes with scalar extension of the coefficients. -/
theorem value_scalarMatrix (R : Type u) [CommRing R] [Algebra K R]
    (M : Matrix (Fin 2) (Fin 2) D) :
    SplitMatrixExtension.value (HyperbolicScheme.inclusion (K := K) n e f R)
        (HyperbolicScheme.retraction n σ q e f R) (HyperbolicScheme.scalarMatrix R M) =
      HyperbolicScheme.scalarMatrix R (SplitMatrixExtension.value
        (FirstKindInvolution.planeInclusion e f) (FirstKindInvolution.planeRetraction σ q e f)
        M) := by
  rw [SplitMatrixExtension.value, SplitMatrixExtension.value, scalarMatrix_add,
    HyperbolicScheme.scalarMatrix_sub, HyperbolicScheme.scalarMatrix_one,
    HyperbolicScheme.scalarMatrix_mul, HyperbolicScheme.scalarMatrix_mul,
    HyperbolicScheme.scalarMatrix_mul]
  rfl

omit [FiniteDimensional K D] in
theorem scalarMatrix_map_lid {l m : Type} (X : Matrix l m D) :
    (HyperbolicScheme.scalarMatrix (K := K) K X).map (Algebra.TensorProduct.lid K D) = X := by
  ext i j
  simp [HyperbolicScheme.scalarMatrix]

omit [FiniteDimensional K D] in
theorem lid_eq_map_equiv (X : K ⊗[K] Matrix n n D) :
    Algebra.TensorProduct.lid K (Matrix n n D) X =
      (TensorMatrix.equiv K n X).map (Algebra.TensorProduct.lid K D) := by
  induction X using TensorProduct.inductionOn with
  | tmul r M =>
    ext i j
    simp [TensorMatrix.equiv_tmul]
  | add x y hx hy =>
    rw [_root_.map_add, _root_.map_add, hx, hy]
    ext i j
    simp

omit [FiniteDimensional K D] in
/-- The binary Levi matrix of `1 ⊗ a` is the scalar extension of `diag(a, σ(a⁻¹))`. -/
theorem leviMatrix_of_val (a : Dˣ) (u : (K ⊗[K] D)ˣ) (hu : (u : K ⊗[K] D) = 1 ⊗ₜ[K] (a : D)) :
    (leviMatrix σ K u : Matrix (Fin 2) (Fin 2) (K ⊗[K] D)) =
      HyperbolicScheme.scalarMatrix K (BinaryAction.hyperbolicLevi σ a : Matrix (Fin 2) (Fin 2) D) := by
  have hmul : (u : K ⊗[K] D) * (1 ⊗ₜ[K] ((a⁻¹ : Dˣ) : D)) = 1 := by
    rw [hu, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.mul_inv,
      Algebra.TensorProduct.one_def]
  have hinv : ((u⁻¹ : (K ⊗[K] D)ˣ) : K ⊗[K] D) = 1 ⊗ₜ[K] ((a⁻¹ : Dˣ) : D) :=
    Units.inv_eq_of_mul_eq_one_right hmul
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BinaryAction.hyperbolicLevi, HyperbolicScheme.scalarMatrix, hu, hinv]

omit [FiniteDimensional K D] in
/-- The extension of `diag(a, σ(a⁻¹))` is the Levi element `ℓ(a)`. -/
theorem planeUnitsHom_hyperbolicLevi (a : Dˣ) :
    (h.planeUnitsHom (BinaryAction.hyperbolicLevi σ a) : Matrix n n D) =
      FirstKindInvolution.Eichler.levi σ q
        (FirstKindInvolution.Eichler.isHyperbolic_of_isHyperbolicPair h) a := by
  have hP := FirstKindInvolution.Eichler.isHyperbolic_of_isHyperbolicPair h
  apply hP.matrix_ext
  · rw [h.vecMul_planeUnitsHom, FirstKindInvolution.vecMul_planeRetraction,
      FirstKindInvolution.Eichler.vecMul_levi_left, hP.sesqForm_eq_one, hP.sesqForm_left_left,
      FirstKindInvolution.vecMul_planeInclusion, FirstKindInvolution.hyperbolicRemainder_apply,
      h.hyperbolicProjection_left, sub_self, add_zero]
    simp [BinaryAction.hyperbolicLevi, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · rw [h.vecMul_planeUnitsHom, FirstKindInvolution.vecMul_planeRetraction,
      FirstKindInvolution.Eichler.vecMul_levi_right, hP.sesqForm_right_right,
      hP.sesqForm_right_left, FirstKindInvolution.vecMul_planeInclusion,
      FirstKindInvolution.hyperbolicRemainder_apply, h.hyperbolicProjection_right, sub_self,
      add_zero]
    simp [BinaryAction.hyperbolicLevi, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · intro z hze hzf
    rw [h.vecMul_planeUnitsHom, FirstKindInvolution.vecMul_planeRetraction,
      FirstKindInvolution.Eichler.vecMul_levi_of_ortho hP a hze hzf, hze, hzf,
      FirstKindInvolution.vecMul_planeInclusion, FirstKindInvolution.hyperbolicRemainder_apply,
      FirstKindInvolution.hyperbolicProjection_apply, hze, hzf]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- **Rational points.** The Levi morphism sends the rational point `a ∈ Dˣ` of `GL₁(D)` to
the rational isometry with matrix `ℓ(a)`. -/
theorem isometryRationalMatrix_leviHom (a : Dˣ) :
    FirstKindInvolution.Eichler.isometryRationalMatrix σ q
        (rationalPoints.map (leviHom h)
          ((FiniteAlgebraUnits.rationalPointsEquiv (Module.finBasis K D)).symm a)) =
      FirstKindInvolution.Eichler.levi σ q
        (FirstKindInvolution.Eichler.isHyperbolic_of_isHyperbolicPair h) a := by
  let K0 : CommAlgCat.{u} (CommRingCat.of K) := CommAlgCat.of (CommRingCat.of K) K
  let T0 := (algSpec (CommRingCat.of K)).obj (op K0)
  let y : T0 ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K D)).X :=
    GaloisPointComparison.rationalCoeffEquiv K _
      ((FiniteAlgebraUnits.rationalPointsEquiv (Module.finBasis K D)).symm a)
  have hy : (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K D) K0 y : K ⊗[K] D) =
      1 ⊗ₜ[K] (a : D) := SpinKernel.affinePointsEquiv_rationalCoeffEquiv_symm a
  let φ := (Corepresented.affineSectionsIso K0).inv.hom
  let ψ := (Corepresented.affineSectionsIso K0).hom.hom
  have hψφ : ∀ x : K0 ⊗[K] D, Algebra.TensorProduct.map ψ (AlgHom.id K D)
      (Algebra.TensorProduct.map φ (AlgHom.id K D) x) = x := by
    intro x
    have hc : ψ.comp φ = AlgHom.id _ _ := by
      have := congrArg CommAlgCat.Hom.hom (Corepresented.affineSectionsIso K0).inv_hom_id
      simpa only [CommAlgCat.hom_comp, CommAlgCat.hom_id] using this
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hc, AlgHom.comp_id,
      Algebra.TensorProduct.map_id]
    rfl
  let z := (y ≫ (leviHom h).hom.hom) ≫ (σ.isometryGroupι q).hom.hom
  -- the matrix of `z` over the affine coordinates
  have hz : TensorMatrix.equiv K n
      (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) K0 z :
        K ⊗[K] Matrix n n D) =
      (HyperbolicScheme.extendUnits h K
        (leviMatrix σ K (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K D) K0 y)) :
          Matrix n n (K ⊗[K] D)) := by
    have hpts := congrArg (fun v : (Matrix n n (BinaryScheme.coefficients T0 ⊗[K] D))ˣ =>
      (v : Matrix n n (BinaryScheme.coefficients T0 ⊗[K] D))) (leviHom_points h T0 y)
    change TensorMatrix.equiv (BinaryScheme.coefficients T0) n
      (FiniteAlgebraUnits.pointsEquiv _ T0 z : BinaryScheme.coefficients T0 ⊗[K] Matrix n n D) =
        _ at hpts
    rw [pointsEquiv_affine] at hpts
    change TensorMatrix.equiv (BinaryScheme.coefficients T0) n
      (Algebra.TensorProduct.map φ (AlgHom.id K (Matrix n n D))
        (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) K0 z :
          K ⊗[K] Matrix n n D)) = _ at hpts
    rw [TensorMatrix.naturality, pointsEquiv_affine (A := D)] at hpts
    rw [HyperbolicScheme.extendUnits_naturality h φ
      (leviMatrix σ K (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K D) K0 y))
      _ (leviMatrix_naturality σ φ _)] at hpts
    ext i j
    have hij := congrArg (fun M => Algebra.TensorProduct.map ψ (AlgHom.id K D) (M i j)) hpts
    simp only [Matrix.map_apply, hψφ] at hij
    exact (hψφ _).symm.trans hij
  apply Units.ext
  rw [FirstKindInvolution.Eichler.isometryRationalMatrix_apply, Units.coe_map]
  change Algebra.TensorProduct.lid K (Matrix n n D)
    (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) K0
      (GaloisPointComparison.rationalCoeffEquiv K _ _ ≫ (σ.isometryGroupι q).hom.hom) :
        K ⊗[K] Matrix n n D) = _
  rw [GaloisPointComparison.rationalCoeffEquiv_map K (leviHom h),
    GroupScheme.affinePointsTarget_apply, lid_eq_map_equiv]
  change (TensorMatrix.equiv K n
    (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) K0 z :
      K ⊗[K] Matrix n n D)).map (Algebra.TensorProduct.lid K D) = _
  rw [hz]
  change (SplitMatrixExtension.value (HyperbolicScheme.inclusion (K := K) n e f K)
    (HyperbolicScheme.retraction n σ q e f K) _).map (Algebra.TensorProduct.lid K D) = _
  rw [leviMatrix_of_val (σ := σ) a _ hy, value_scalarMatrix, scalarMatrix_map_lid]
  exact planeUnitsHom_hyperbolicLevi h a

end Langlands.GroupScheme.Quaternionic.LeviScheme
