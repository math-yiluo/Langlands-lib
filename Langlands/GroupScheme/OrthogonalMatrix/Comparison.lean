import Langlands.GroupScheme.OrthogonalMatrix.Hyperbolic
import Langlands.GroupScheme.Quaternionic.ScalarInvolution
import Langlands.GroupScheme.Quaternionic.SymplecticReductive
import Mathlib.RingTheory.MatrixAlgebra

/-! # Split comparison of the orthogonal group of an ordinary quadratic form

Let `K` be a field, `q` the scalar quadratic form on `K^n` represented by `Q ∈ M_n(K)`, and
`L` a field extension of `K`. The points of the isometry group `O(q)` of
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution.isometryGroup` with values in a
commutative `K`-algebra `R` are units `u` of `R ⊗[K] M_n(K)`, which the matrix chart
`R ⊗[K] M_n(K) ≃ M_n(R)` (`chart`) turns into matrices `U` with `U Q Uᵀ - Q` alternating
(`chart_defect`, `mem_quadraticKernel_baseChange_iff`).

If `P : Matrix (Fin m ⊕ Fin m) n L` has a two-sided inverse `P'` and `P Q Pᵀ - formMatrix` is
alternating, then `U ↦ P U P'` identifies the base change of `O(q)` to `L` with the split
orthogonal group `OrthogonalMatrix.groupScheme (Fin m) L` (`splittingIso`). Over an
algebraically closed `L` such a `P` exists whenever `Q + Qᵀ` is invertible and `n` has
`2 m` elements (`exists_hyperbolic_matrix`), which gives `nonempty_splittingIso`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

open Langlands.GroupScheme.Quaternionic

section Conjugation

variable {R : Type*} [CommRing R] {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
  [DecidableEq β]

omit [DecidableEq α] in
/-- Congruence by a matrix with a left inverse reflects alternating matrices. -/
theorem isAlt_conj_iff {P : Matrix α β R} {P' : Matrix β α R} (h : P' * P = 1)
    (X : Matrix β β R) : IsAlt (P * X * Pᵀ) ↔ IsAlt X := by
  refine ⟨fun hX => ?_, fun hX => hX.conj P⟩
  have h2 := hX.conj P'
  have hT : Pᵀ * P'ᵀ = 1 := by rw [← Matrix.transpose_mul, h, Matrix.transpose_one]
  simp only [Matrix.mul_assoc] at h2
  rwa [hT, Matrix.mul_one, ← Matrix.mul_assoc, h, Matrix.one_mul] at h2

omit [DecidableEq α] in
/-- Let `P` have a left inverse `P'` and let `P Q Pᵀ - F` be alternating. Then
`g = P U P'` satisfies `g F gᵀ ≡ F` modulo alternating matrices exactly when
`U Q Uᵀ ≡ Q` modulo alternating matrices. -/
theorem isAlt_conj_sub_iff {P : Matrix α β R} {P' : Matrix β α R} (h : P' * P = 1)
    {Q : Matrix β β R} {F : Matrix α α R} (hPQ : IsAlt (P * Q * Pᵀ - F)) (U : Matrix β β R) :
    IsAlt (P * U * P' * F * (P * U * P')ᵀ - F) ↔ IsAlt (U * Q * Uᵀ - Q) := by
  have hT : Pᵀ * P'ᵀ = 1 := by rw [← Matrix.transpose_mul, h, Matrix.transpose_one]
  have e1 : P * U * P' * (P * Q * Pᵀ) * (P * U * P')ᵀ = P * (U * Q * Uᵀ) * Pᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P' P, h, Matrix.one_mul, ← Matrix.mul_assoc Pᵀ P'ᵀ, hT,
      Matrix.one_mul]
  have key : P * U * P' * F * (P * U * P')ᵀ - F =
      P * (U * Q * Uᵀ - Q) * Pᵀ +
        ((P * Q * Pᵀ - F) - P * U * P' * (P * Q * Pᵀ - F) * (P * U * P')ᵀ) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    rw [e1]
    abel
  rw [key]
  constructor
  · intro hg
    have h1 := hg.sub (hPQ.sub (hPQ.conj (P * U * P')))
    rw [add_sub_cancel_right] at h1
    exact (isAlt_conj_iff h _).1 h1
  · intro hU
    exact ((isAlt_conj_iff h _).2 hU).add (hPQ.sub (hPQ.conj _))

end Conjugation

section Chart

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n]
variable (R : Type u) [CommRing R] [Algebra K R]

/-- The matrix chart `R ⊗[K] M_n(K) ≃ M_n(R)`. -/
abbrev chart (K : Type u) [Field K] (n : Type) [Fintype n] [DecidableEq n] (R : Type u)
    [CommRing R] [Algebra K R] : R ⊗[K] Matrix n n K ≃ₐ[K] Matrix n n R :=
  (matrixEquivTensor n K R).symm

theorem chart_tmul (r : R) (M : Matrix n n K) :
    chart K n R (r ⊗ₜ[K] M) = r • M.map (algebraMap K R) :=
  rfl

theorem chart_one_tmul (M : Matrix n n K) :
    chart K n R ((1 : R) ⊗ₜ[K] M) = M.map (algebraMap K R) := by
  rw [chart_tmul, one_smul]

/-- The chart carries the extended scalar involution to the transpose. -/
theorem chart_baseChange (y : R ⊗[K] Matrix n n K) :
    chart K n R (((FirstKindInvolution.scalar K).matrix n).baseChange R y) =
      (chart K n R y)ᵀ := by
  induction y using TensorProduct.inductionOn with
  | tmul r M =>
    rw [FirstKindInvolution.baseChange_tmul, FirstKindInvolution.scalar_matrix_apply,
      chart_tmul, chart_tmul, Matrix.transpose_smul, Matrix.transpose_map]
  | add y y' hy hy' =>
    rw [FirstKindInvolution.map_add, _root_.map_add, _root_.map_add, hy, hy',
      Matrix.transpose_add]

/-- The chart of the defect `u Q ᵗu - Q`. -/
theorem chart_defect (Q : Matrix n n K) (y : R ⊗[K] Matrix n n K) :
    chart K n R (IsometryCut.defect ((FirstKindInvolution.scalar K).matrix n) Q y) =
      chart K n R y * Q.map (algebraMap K R) * (chart K n R y)ᵀ - Q.map (algebraMap K R) := by
  rw [IsometryCut.defect, _root_.map_sub, _root_.map_mul, _root_.map_mul, chart_baseChange,
    chart_one_tmul]

/-- An element of `R ⊗[K] M_n(K)` lies in the extended quadratic kernel `R ⊗ {a - ᵗa}`
exactly when its chart is alternating. -/
theorem mem_quadraticKernel_baseChange_iff (z : R ⊗[K] Matrix n n K) :
    z ∈ ((FirstKindInvolution.scalar K).quadraticKernel n).baseChange R ↔
      IsAlt (chart K n R z) := by
  change z ∈ ((FirstKindInvolution.scalar K).matrix n).alternatingSubspace.baseChange R ↔ _
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    FirstKindInvolution.mem_alternatingSubspace]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨chart K n R a, by rw [_root_.map_sub, chart_baseChange]⟩
  · rintro ⟨U, hU⟩
    refine ⟨(chart K n R).symm U, (chart K n R).injective ?_⟩
    rw [_root_.map_sub, chart_baseChange, AlgEquiv.apply_symm_apply, hU]

variable {R} in
/-- The chart commutes with coefficient changes. -/
theorem chart_naturality {R' : Type u} [CommRing R'] [Algebra K R'] (f : R →ₐ[K] R')
    (u : R ⊗[K] Matrix n n K) :
    chart K n R' (Algebra.TensorProduct.map f (AlgHom.id K (Matrix n n K)) u) =
      (chart K n R u).map f := by
  induction u using TensorProduct.inductionOn with
  | tmul r M =>
    rw [Algebra.TensorProduct.map_tmul, chart_tmul, chart_tmul, AlgHom.id_apply]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply]
  | add u u' hu hu' =>
    rw [_root_.map_add, _root_.map_add, _root_.map_add, hu, hu', Matrix.map_add _ (map_add f)]

end Chart

section Isometry

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  {n : Type} [Fintype n] [DecidableEq n] (q : (FirstKindInvolution.scalar K).QuadraticForms n)

/-- The base change of the isometry group `O(q)` to `L`. -/
abbrev baseChangeIsometryGroup : GroupScheme (Spec (CommRingCat.of L)) :=
  (GroupScheme.baseChange (scalarBaseMap K L)).obj ((FirstKindInvolution.scalar K).isometryGroup q)

/-- The unit of `Γ(T, ⊤) ⊗[K] M_n(K)` underlying a point of the base change of `O(q)`. -/
def isometryUnitPoint (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (baseChangeIsometryGroup (L := L) q).X) →*
      (restrictedSections K L T ⊗[K] Matrix n n K)ˣ :=
  (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n K))
      ((Over.map (scalarBaseMap K L)).obj T)).toMonoidHom.comp
    (((yonedaGrp.map ((FirstKindInvolution.scalar K).isometryGroupι q)).app
        (Opposite.op ((Over.map (scalarBaseMap K L)).obj T))).hom.comp
      (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L)
        ((FirstKindInvolution.scalar K).isometryGroup q) T).toMonoidHom)

theorem isometryUnitPoint_apply (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (baseChangeIsometryGroup (L := L) q).X) :
    isometryUnitPoint q T x = FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n K))
      ((Over.map (scalarBaseMap K L)).obj T)
      (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L)
          ((FirstKindInvolution.scalar K).isometryGroup q) T x ≫
        ((FirstKindInvolution.scalar K).isometryGroupι q).hom.hom) :=
  rfl

/-- The unit underlying a point has defect in the extended quadratic kernel. -/
theorem isometryUnitPoint_defect_mem (Q : Matrix n n K)
    (hQ : (Submodule.Quotient.mk Q : (FirstKindInvolution.scalar K).QuadraticForms n) = q)
    (T : Over (Spec (CommRingCat.of L))) (x : T ⟶ (baseChangeIsometryGroup (L := L) q).X) :
    IsometryCut.defect ((FirstKindInvolution.scalar K).matrix n) Q
        (isometryUnitPoint q T x : restrictedSections K L T ⊗[K] Matrix n n K) ∈
      ((FirstKindInvolution.scalar K).quadraticKernel n).baseChange
        (restrictedSections K L T) := by
  have hmem := ((FirstKindInvolution.scalar K).mem_range_isometryGroupι_iff q Q hQ _).1
    (SubgroupFunctor.mem_range.2 ⟨_, rfl⟩ :
      GroupScheme.baseChangePointsEquiv (scalarBaseMap K L)
          ((FirstKindInvolution.scalar K).isometryGroup q) T x ≫
        ((FirstKindInvolution.scalar K).isometryGroupι q).hom.hom ∈
        (SubgroupFunctor.range ((FirstKindInvolution.scalar K).isometryGroupι q)).carrier _)
  rw [isometryUnitPoint_apply]
  exact hmem

/-- Restriction of points acts on the underlying units by the coefficient change of global
sections. -/
theorem isometryUnitPoint_naturality {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ (baseChangeIsometryGroup (L := L) q).X) :
    isometryUnitPoint q T' (a ≫ x) =
      Units.map (Algebra.TensorProduct.map
        ((algΓ (CommRingCat.of K)).map ((Over.map (scalarBaseMap K L)).map a)).unop.hom
        (AlgHom.id K (Matrix n n K))).toMonoidHom (isometryUnitPoint q T x) := by
  rw [isometryUnitPoint_apply, isometryUnitPoint_apply,
    GroupScheme.baseChangePointsEquiv_naturality, Category.assoc,
    FiniteAlgebraUnits.pointsEquiv_naturality]

/-- Units of `Γ(T, ⊤) ⊗[K] M_n(K)` with defect in the extended quadratic kernel come from
points of the base change. -/
theorem exists_isometryUnitPoint_eq (Q : Matrix n n K)
    (hQ : (Submodule.Quotient.mk Q : (FirstKindInvolution.scalar K).QuadraticForms n) = q)
    (T : Over (Spec (CommRingCat.of L)))
    (w : (restrictedSections K L T ⊗[K] Matrix n n K)ˣ)
    (hw : IsometryCut.defect ((FirstKindInvolution.scalar K).matrix n) Q
        (w : restrictedSections K L T ⊗[K] Matrix n n K) ∈
      ((FirstKindInvolution.scalar K).quadraticKernel n).baseChange
        (restrictedSections K L T)) :
    ∃ x, isometryUnitPoint q T x = w := by
  set T' := (Over.map (scalarBaseMap K L)).obj T
  set y := (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n K)) T').symm w
  have hy : y ∈ (SubgroupFunctor.range
      ((FirstKindInvolution.scalar K).isometryGroupι q)).carrier T' := by
    rw [(FirstKindInvolution.scalar K).mem_range_isometryGroupι_iff q Q hQ,
      MulEquiv.apply_symm_apply]
    exact hw
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 hy
  refine ⟨(GroupScheme.baseChangePointsEquiv _ _ T).symm z, ?_⟩
  rw [isometryUnitPoint_apply, MulEquiv.apply_symm_apply, hz, MulEquiv.apply_symm_apply]

theorem isometryUnitPoint_injective (T : Over (Spec (CommRingCat.of L))) :
    Function.Injective (isometryUnitPoint (L := L) q T) := by
  intro x y h
  rw [isometryUnitPoint_apply, isometryUnitPoint_apply] at h
  have h4 := (FiniteAlgebraUnits.pointsEquiv _ _).injective h
  have := ((FirstKindInvolution.scalar K).isClosedSubgroup_isometryGroupι q).mono_overHom
  exact (GroupScheme.baseChangePointsEquiv _ _ T).injective ((cancel_mono _).1 h4)

section Split

variable {m : ℕ} (P : Matrix (Fin m ⊕ Fin m) n L) (P' : Matrix n (Fin m ⊕ Fin m) L)

section Ring

variable (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]

variable (K) in
/-- The matrix `P U P'` of an element `u` of `R ⊗[K] M_n(K)` with chart `U`. -/
def splitMatrix (u : R ⊗[K] Matrix n n K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R :=
  P.map (algebraMap L R) * chart K n R u * P'.map (algebraMap L R)

omit [IsScalarTower K L R] in
theorem map_mul_map_eq_one {α β : Type*} [Fintype β] [DecidableEq α]
    {A : Matrix α β L} {B : Matrix β α L} (h : A * B = 1) :
    A.map (algebraMap L R) * B.map (algebraMap L R) = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]

omit [DecidableEq n] in
theorem isAlt_map_hyperbolic {Q : Matrix n n K}
    (hPQ : IsAlt (P * Q.map (algebraMap K L) * Pᵀ - formMatrix (Fin m) L)) :
    IsAlt (P.map (algebraMap L R) * Q.map (algebraMap K R) * (P.map (algebraMap L R))ᵀ -
      formMatrix (Fin m) R) := by
  have h := hPQ.map (algebraMap L R)
  rwa [Matrix.map_sub _ (_root_.map_sub (algebraMap L R)), Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map, formMatrix_map, Matrix.map_map, ← RingHom.coe_comp,
    ← IsScalarTower.algebraMap_eq] at h

omit [Algebra K L] [IsScalarTower K L R] in
theorem splitMatrix_one (hPP' : P * P' = 1) : splitMatrix K P P' R 1 = 1 := by
  rw [splitMatrix, _root_.map_one, Matrix.mul_one]
  exact map_mul_map_eq_one R hPP'

omit [Algebra K L] [IsScalarTower K L R] in
theorem splitMatrix_mul (hP'P : P' * P = 1) (u v : R ⊗[K] Matrix n n K) :
    splitMatrix K P P' R (u * v) = splitMatrix K P P' R u * splitMatrix K P P' R v := by
  have h := map_mul_map_eq_one R hP'P
  simp only [splitMatrix, _root_.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P'.map _) (P.map _), h, Matrix.one_mul]

omit [Algebra K L] [IsScalarTower K L R] in
theorem splitMatrix_injective (hP'P : P' * P = 1) :
    Function.Injective (splitMatrix K P P' R) := by
  intro u v huv
  have h := map_mul_map_eq_one R hP'P
  have h2 : chart K n R u = chart K n R v := by
    have h' := congrArg (fun M => P'.map (algebraMap L R) * M * P.map (algebraMap L R)) huv
    simp only [splitMatrix, Matrix.mul_assoc] at h'
    simpa only [← Matrix.mul_assoc (P'.map _) (P.map _), h, Matrix.one_mul,
      Matrix.mul_one] using h'
  exact (chart K n R).injective h2

/-- `P U P'` is orthogonal for the split form exactly when `U Q Uᵀ - Q` is alternating, i.e.
when `u` is an isometry of `q`. -/
theorem splitMatrix_mem_iff (hP'P : P' * P = 1) {Q : Matrix n n K}
    (hPQ : IsAlt (P * Q.map (algebraMap K L) * Pᵀ - formMatrix (Fin m) L))
    (u : R ⊗[K] Matrix n n K) :
    splitMatrix K P P' R u ∈ orthogonalGroup (Fin m) R ↔
      IsometryCut.defect ((FirstKindInvolution.scalar K).matrix n) Q u ∈
        ((FirstKindInvolution.scalar K).quadraticKernel n).baseChange R := by
  rw [mem_quadraticKernel_baseChange_iff, chart_defect, mem_orthogonalGroup_iff, defect,
    splitMatrix]
  exact isAlt_conj_sub_iff (map_mul_map_eq_one R hP'P) (isAlt_map_hyperbolic P R hPQ) _

/-- The matrix `P U P'` commutes with coefficient changes of `L`-algebras. -/
theorem splitMatrix_naturality {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra L R']
    [IsScalarTower K L R'] (f : R →ₐ[L] R') (u : R ⊗[K] Matrix n n K) :
    splitMatrix K P P' R'
        (Algebra.TensorProduct.map (f.restrictScalars K) (AlgHom.id K _) u) =
      (splitMatrix K P P' R u).map f := by
  rw [splitMatrix, splitMatrix, chart_naturality, AlgHom.coe_restrictScalars', Matrix.map_mul,
    Matrix.map_mul, Matrix.map_map, Matrix.map_map]
  congr 2 <;> ext <;> simp

/-- Every orthogonal matrix is `P U P'` for a unit `u` which is an isometry of `q`. -/
theorem exists_splitMatrix_eq (hPP' : P * P' = 1) (hP'P : P' * P = 1) {Q : Matrix n n K}
    (hPQ : IsAlt (P * Q.map (algebraMap K L) * Pᵀ - formMatrix (Fin m) L))
    (g : orthogonalGroup (Fin m) R) :
    ∃ w : (R ⊗[K] Matrix n n K)ˣ,
      IsometryCut.defect ((FirstKindInvolution.scalar K).matrix n) Q
          (w : R ⊗[K] Matrix n n K) ∈
        ((FirstKindInvolution.scalar K).quadraticKernel n).baseChange R ∧
      splitMatrix K P P' R w = g := by
  have hPP'R := map_mul_map_eq_one R hPP'
  have hP'PR := map_mul_map_eq_one R hP'P
  set PR := P.map (algebraMap L R)
  set P'R := P'.map (algebraMap L R)
  set gm : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R :=
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R)
  set gi : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R := invMatrix gm
  have hggi : gm * gi = 1 := mul_invMatrix g.2
  have hgig : gi * gm = 1 := invMatrix_mul g.2
  let gu : (Matrix n n R)ˣ :=
    { val := P'R * gm * PR
      inv := P'R * gi * PR
      val_inv := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc PR P'R, hPP'R, Matrix.one_mul, ← Matrix.mul_assoc gm gi, hggi,
          Matrix.one_mul, hP'PR]
      inv_val := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc PR P'R, hPP'R, Matrix.one_mul, ← Matrix.mul_assoc gi, hgig,
          Matrix.one_mul, hP'PR] }
  let w : (R ⊗[K] Matrix n n K)ˣ :=
    Units.map (chart K n R).symm.toRingEquiv.toMonoidHom gu
  have hw : chart K n R (w : R ⊗[K] Matrix n n K) = P'R * gm * PR := by
    change chart K n R ((chart K n R).symm (P'R * gm * PR)) = _
    rw [AlgEquiv.apply_symm_apply]
  have hdw : splitMatrix K P P' R w = g := by
    rw [splitMatrix, hw]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc PR P'R, hPP'R, Matrix.one_mul, Matrix.mul_one]
  refine ⟨w, ?_, hdw⟩
  rw [← splitMatrix_mem_iff P P' R hP'P hPQ, hdw]
  exact g.2

end Ring

variable (Q : Matrix n n K)
  (hQ : (Submodule.Quotient.mk Q : (FirstKindInvolution.scalar K).QuadraticForms n) = q)
  (hPP' : P * P' = 1) (hP'P : P' * P = 1)
  (hPQ : IsAlt (P * Q.map (algebraMap K L) * Pᵀ - formMatrix (Fin m) L))
include hQ hPP' hP'P hPQ

/-- On points of the base change of `O(q)`, `u ↦ P U P'`. -/
def splitPointsHom (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (baseChangeIsometryGroup (L := L) q).X) →*
      orthogonalGroup (Fin m) (restrictedSections K L T) where
  toFun x := ⟨splitMatrix K P P' (restrictedSections K L T) (isometryUnitPoint q T x),
    (splitMatrix_mem_iff P P' _ hP'P hPQ _).2 (isometryUnitPoint_defect_mem q Q hQ T x)⟩
  map_one' := Subtype.ext (by
    change splitMatrix K P P' (restrictedSections K L T)
      ((isometryUnitPoint q T 1 : (restrictedSections K L T ⊗[K] Matrix n n K)ˣ) :
        restrictedSections K L T ⊗[K] Matrix n n K) = 1
    rw [_root_.map_one, Units.val_one]
    exact splitMatrix_one P P' _ hPP')
  map_mul' x y := Subtype.ext (by
    change splitMatrix K P P' (restrictedSections K L T)
      ((isometryUnitPoint q T (x * y) : (restrictedSections K L T ⊗[K] Matrix n n K)ˣ) :
        restrictedSections K L T ⊗[K] Matrix n n K) =
      splitMatrix K P P' (restrictedSections K L T) (isometryUnitPoint q T x) *
        splitMatrix K P P' (restrictedSections K L T) (isometryUnitPoint q T y)
    rw [_root_.map_mul, Units.val_mul]
    exact splitMatrix_mul P P' _ hP'P _ _)

theorem splitPointsHom_apply (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (baseChangeIsometryGroup (L := L) q).X) :
    (splitPointsHom q P P' Q hQ hPP' hP'P hPQ T x :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (restrictedSections K L T)) =
      splitMatrix K P P' (restrictedSections K L T) (isometryUnitPoint q T x) :=
  rfl

theorem splitPointsHom_bijective (T : Over (Spec (CommRingCat.of L))) :
    Function.Bijective (splitPointsHom q P P' Q hQ hPP' hP'P hPQ T) := by
  constructor
  · intro x y hxy
    have h1 := congrArg Subtype.val hxy
    rw [splitPointsHom_apply, splitPointsHom_apply] at h1
    exact isometryUnitPoint_injective q T (Units.ext (splitMatrix_injective P P' _ hP'P h1))
  · intro g
    obtain ⟨w, hw, hwg⟩ := exists_splitMatrix_eq P P' _ hPP' hP'P hPQ g
    obtain ⟨x, hx⟩ := exists_isometryUnitPoint_eq q Q hQ T w hw
    refine ⟨x, Subtype.ext ?_⟩
    rw [splitPointsHom_apply, hx, hwg]

/-- Points of the base change of `O(q)` are split orthogonal matrices. -/
def splitPointsEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (baseChangeIsometryGroup (L := L) q).X) ≃* orthogonalGroup (Fin m) Γ(T.left, ⊤) :=
  MulEquiv.ofBijective (splitPointsHom q P P' Q hQ hPP' hP'P hPQ T)
    (splitPointsHom_bijective q P P' Q hQ hPP' hP'P hPQ T)

theorem splitPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ (baseChangeIsometryGroup (L := L) q).X) :
    splitPointsEquiv q P P' Q hQ hPP' hP'P hPQ T' (a ≫ x) =
      map (Fin m) a.left.appTop.hom (splitPointsEquiv q P P' Q hQ hPP' hP'P hPQ T x) := by
  apply Subtype.ext
  change splitMatrix K P P' (restrictedSections K L T') (isometryUnitPoint q T' (a ≫ x)) =
    (splitMatrix K P P' (restrictedSections K L T) (isometryUnitPoint q T x)).map
      a.left.appTop.hom
  rw [isometryUnitPoint_naturality]
  let f : restrictedSections K L T →ₐ[L] restrictedSections K L T' :=
    { ((algΓ (CommRingCat.of K)).map ((Over.map (scalarBaseMap K L)).map a)).unop.hom.toRingHom
      with commutes' := fun c => ((algΓ (CommRingCat.of L)).map a).unop.hom.commutes c }
  exact splitMatrix_naturality (K := K) P P' (restrictedSections K L T) f
    (isometryUnitPoint q T x)

/-- **Splitting of `O(q)`.** The base change of the isometry group `O(q)` to `L` is the split
orthogonal group, on points by `u ↦ P U P'`. -/
def splittingIso :
    baseChangeIsometryGroup (L := L) q ≅ groupScheme (Fin m) (CommRingCat.of L) :=
  isoOfPointModels (fun T => orthogonalGroup (Fin m) Γ(T.left, ⊤))
    (fun a => map (Fin m) a.left.appTop.hom)
    (splitPointsEquiv q P P' Q hQ hPP' hP'P hPQ)
    (pointsEquiv (Fin m) (CommRingCat.of L))
    (splitPointsEquiv_naturality q P P' Q hQ hPP' hP'P hPQ)
    (fun a y => pointsEquiv_naturality a y)

end Split

/-- **Splitting of `O(q)` over an algebraically closed field.** If `L` is algebraically
closed, `Q + Qᵀ` is invertible and `n` has `2 m` elements, the base change to `L` of the
isometry group of the scalar quadratic form represented by `Q` is isomorphic to the split
orthogonal group `OrthogonalMatrix.groupScheme (Fin m) L`. -/
theorem nonempty_splittingIso [IsAlgClosed L] {m : ℕ} (hn : Fintype.card n = 2 * m)
    (Q : Matrix n n K) (hQ : IsUnit (Q + Qᵀ)) :
    Nonempty ((GroupScheme.baseChange (scalarBaseMap K L)).obj
        ((FirstKindInvolution.scalar K).isometryGroup
          (Submodule.Quotient.mk Q : (FirstKindInvolution.scalar K).QuadraticForms n)) ≅
      groupScheme (Fin m) (CommRingCat.of L)) := by
  have hQL : IsUnit (Q.map (algebraMap K L) + (Q.map (algebraMap K L))ᵀ) := by
    have h := hQ.map (algebraMap K L).mapMatrix
    rwa [_root_.map_add, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.transpose_map] at h
  obtain ⟨P, P', hPP', hP'P, hPQ⟩ := exists_hyperbolic_matrix hn _ hQL
  exact ⟨splittingIso _ P P' Q rfl hPP' hP'P hPQ⟩

end Isometry

end Langlands.GroupScheme.OrthogonalMatrix
