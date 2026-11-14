import Langlands.GroupScheme.Quaternionic.CocharacterWeightProjectors
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Scalar extension of all-test cocharacter row weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]

/-- The universal equation whose kernel is the ground-field weight space. -/
def cocharacterWeightEquation (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (c : ℤ) : (n → D) →ₗ[K] (n → LaurentPolynomial K ⊗[K] D) :=
  σ.cocharacterUniversalRowAction q f -
    LinearMap.pi (fun i =>
      (TensorProduct.mk K (LaurentPolynomial K) D (LaurentPolynomial.T c)).comp
        (LinearMap.proj i))

theorem ker_cocharacterWeightEquation (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (c : ℤ) :
    LinearMap.ker (σ.cocharacterWeightEquation q f c) =
      (σ.cocharacterWeightSpace q f c).restrictScalars K := by
  ext v
  change (σ.cocharacterUniversalRowAction q f v -
    (fun i => LaurentPolynomial.T c ⊗ₜ[K] v i) = 0) ↔
      v ∈ σ.cocharacterWeightSpace q f c
  rw [sub_eq_zero, σ.mem_cocharacterWeightSpace_iff_universal]
  rfl

variable (K) in
/-- The relative Laurent test algebra, retaining the original base field. -/
abbrev cocharacterExtendedTestAlgebra (R : CommAlgCat.{u} (CommRingCat.of K)) :
    CommAlgCat.{u} (CommRingCat.of K) :=
  CommAlgCat.of (CommRingCat.of K) (R ⊗[K] LaurentPolynomial K)

/-- Insert coefficients into their relative Laurent test algebra. -/
def cocharacterExtendedCoefficientMap (R : CommAlgCat.{u} (CommRingCat.of K)) :
    R ⟶ cocharacterExtendedTestAlgebra K R :=
  ConcreteCategory.ofHom (C := CommAlgCat (CommRingCat.of K))
    (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] LaurentPolynomial K)

/-- Specialize a scalar-extended row along a map of coefficient algebras. -/
def cocharacterRowSpecialization
    {R S : CommAlgCat.{u} (CommRingCat.of K)} (φ : R ⟶ S) :
    R ⊗[K] (n → D) →ₗ[K] (n → S ⊗[K] D) :=
  LinearMap.pi fun i => TensorProduct.map φ.hom.toLinearMap (LinearMap.proj i)

/-- The coefficient-algebra map inserting the original Laurent variable. -/
def cocharacterExtendedLaurentMap (R : CommAlgCat.{u} (CommRingCat.of K)) :
    cocharacterWeightTestAlgebra K ⟶ cocharacterExtendedTestAlgebra K R :=
  ConcreteCategory.ofHom (C := CommAlgCat (CommRingCat.of K))
    (Algebra.TensorProduct.includeRight :
      LaurentPolynomial K →ₐ[K] R ⊗[K] LaurentPolynomial K)

/-- The universal multiplicative-group point after extension of coefficients. -/
def cocharacterExtendedTestPoint (R : CommAlgCat.{u} (CommRingCat.of K)) :
    GroupScheme.affinePoints (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
      (cocharacterExtendedTestAlgebra K R) :=
  GroupScheme.affinePointMap (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
    (cocharacterExtendedLaurentMap R) (cocharacterWeightUniversalPoint K)

theorem cocharacterExtendedTestPoint_zpow_val
    (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ) :
    (((Gm.affineUnitsEquiv (CommRingCat.of K) (cocharacterExtendedTestAlgebra K R)
      (cocharacterExtendedTestPoint R)) ^ c : _ˣ) :
        R ⊗[K] LaurentPolynomial K) = (1 : R) ⊗ₜ[K] LaurentPolynomial.T c := by
  rw [cocharacterExtendedTestPoint, Gm.affineUnitsEquiv_naturality,
    cocharacterWeightUniversalPoint_unit, ← map_zpow]
  change (cocharacterExtendedLaurentMap R).hom
    ((Gm.relativeCoordUnit K ^ c : (LaurentPolynomial K)ˣ) : LaurentPolynomial K) = _
  rw [Gm.relativeCoordUnit_zpow_val]
  rfl

/-- Evaluation of both coefficient and Laurent factors in an arbitrary test algebra. -/
def cocharacterExtendedEvaluation {R S : CommAlgCat.{u} (CommRingCat.of K)}
    (φ : R ⟶ S) (t : Sˣ) : cocharacterExtendedTestAlgebra K R ⟶ S :=
  ConcreteCategory.ofHom (C := CommAlgCat (CommRingCat.of K))
    (Algebra.TensorProduct.lift φ.hom (cocharacterWeightEvaluation S t).hom
      (fun _ _ => Commute.all _ _))

theorem cocharacterExtendedEvaluation_tmul
    {R S : CommAlgCat.{u} (CommRingCat.of K)} (φ : R ⟶ S) (t : Sˣ)
    (r : R) (p : LaurentPolynomial K) :
    (cocharacterExtendedEvaluation φ t).hom (r ⊗ₜ[K] p) =
      φ.hom r * (cocharacterWeightEvaluation S t).hom p := by
  simp [cocharacterExtendedEvaluation]

theorem cocharacterExtendedTestPoint_evaluate
    {R S : CommAlgCat.{u} (CommRingCat.of K)} (φ : R ⟶ S)
    (t : GroupScheme.affinePoints (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp S) :
    GroupScheme.affinePointMap (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
      (cocharacterExtendedEvaluation φ (Gm.affineUnitsEquiv (CommRingCat.of K) S t))
      (cocharacterExtendedTestPoint R) = t := by
  apply (Gm.affineUnitsEquiv (CommRingCat.of K) S).injective
  rw [Gm.affineUnitsEquiv_naturality]
  apply Units.ext
  change (cocharacterExtendedEvaluation φ _).hom
    ((Gm.affineUnitsEquiv (CommRingCat.of K) (cocharacterExtendedTestAlgebra K R)
      (cocharacterExtendedTestPoint R)) : R ⊗[K] LaurentPolynomial K) = _
  have h := cocharacterExtendedTestPoint_zpow_val R 1
  simp only [zpow_one] at h
  rw [h, cocharacterExtendedEvaluation_tmul, cocharacterWeightEvaluation_T]
  simp

/-- Insert a scalar-extended row into the relative Laurent test algebra. -/
def cocharacterExtendedRow (R : CommAlgCat.{u} (CommRingCat.of K)) :
    R ⊗[K] (n → D) →ₗ[R] (n → (R ⊗[K] LaurentPolynomial K) ⊗[K] D) :=
  LinearMap.pi fun i => TensorProduct.AlgebraTensorModule.map
    (Algebra.linearMap R (R ⊗[K] LaurentPolynomial K))
    (LinearMap.proj i)

/-- The required Laurent monomial times a scalar-extended row. -/
def cocharacterExtendedMonomialRow (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ) :
    R ⊗[K] (n → D) →ₗ[R] (n → (R ⊗[K] LaurentPolynomial K) ⊗[K] D) :=
  LinearMap.pi fun i => TensorProduct.AlgebraTensorModule.map
    ((TensorProduct.AlgebraTensorModule.mk K R R (LaurentPolynomial K)).flip
      (LaurentPolynomial.T c))
    (LinearMap.proj i)

omit [FiniteDimensional K D] [Fintype n] [DecidableEq n] in
theorem cocharacterRowSpecialization_coefficientMap
    (R : CommAlgCat.{u} (CommRingCat.of K)) (z : R ⊗[K] (n → D)) :
    cocharacterRowSpecialization (cocharacterExtendedCoefficientMap R) z =
      cocharacterExtendedRow R z := by
  induction z with
  | tmul r v => rfl
  | add x y hx hy => simp [hx, hy]

omit [FiniteDimensional K D] [Fintype n] [DecidableEq n] in
theorem cocharacterExtendedMonomialRow_eq_smul
    (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ) (z : R ⊗[K] (n → D)) :
    cocharacterExtendedMonomialRow R c z =
      ((1 : R) ⊗ₜ[K] (LaurentPolynomial.T c : LaurentPolynomial K)) •
        cocharacterExtendedRow R z := by
  induction z with
  | tmul r v =>
    funext i
    simp [cocharacterExtendedMonomialRow, cocharacterExtendedRow,
      TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [hx, hy, smul_add]

omit [FiniteDimensional K D] [Fintype n] [DecidableEq n] in
theorem cocharacterExtendedRow_evaluate
    {R S : CommAlgCat.{u} (CommRingCat.of K)} (φ : R ⟶ S)
    (t : Sˣ) (z : R ⊗[K] (n → D)) :
    (fun i => Algebra.TensorProduct.map (cocharacterExtendedEvaluation φ t).hom
      (AlgHom.id K D) (cocharacterExtendedRow R z i)) =
        cocharacterRowSpecialization φ z := by
  induction z with
  | tmul r v =>
    funext i
    simp [cocharacterExtendedRow, cocharacterRowSpecialization,
      cocharacterExtendedEvaluation]
  | add x y hx hy =>
    simp only [_root_.map_add, Pi.add_apply] at *
    rw [← hx, ← hy]
    rfl

omit [FiniteDimensional K D] [Fintype n] [DecidableEq n] in
theorem cocharacterExtendedMonomialRow_evaluate
    {R S : CommAlgCat.{u} (CommRingCat.of K)} (φ : R ⟶ S)
    (t : Sˣ) (c : ℤ) (z : R ⊗[K] (n → D)) :
    (fun i => Algebra.TensorProduct.map (cocharacterExtendedEvaluation φ t).hom
      (AlgHom.id K D) (cocharacterExtendedMonomialRow R c z i)) =
        (t ^ c : Sˣ) • cocharacterRowSpecialization φ z := by
  induction z with
  | tmul r v =>
    funext i
    simp [cocharacterExtendedMonomialRow, cocharacterRowSpecialization,
      cocharacterExtendedEvaluation, cocharacterWeightEvaluation,
      TensorProduct.smul_tmul', Units.smul_def, mul_comm]
  | add x y hx hy =>
    simp only [_root_.map_add, Pi.add_apply, smul_add] at *
    rw [← hx, ← hy]
    rfl

/-- The actual universal row-action equation on the scalar-extended row module. -/
def cocharacterWeightEquationOver (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ) :
    R ⊗[K] (n → D) →ₗ[R] (n → (R ⊗[K] LaurentPolynomial K) ⊗[K] D) :=
  ((σ.isometryRowActionOver q (cocharacterExtendedTestAlgebra K R)
    (cocharacterExtendedTestPoint R ≫ f.hom.hom)).restrictScalars R).comp
      (cocharacterExtendedRow R) - cocharacterExtendedMonomialRow R c

/-- Weight rows over a coefficient algebra, defined by the actual relative
Laurent-point row-action equation. -/
def cocharacterWeightSpaceOver (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ) :
    Submodule R (R ⊗[K] (n → D)) :=
  LinearMap.ker (σ.cocharacterWeightEquationOver q f R c)

/-- The relative Laurent-point equation is equivalent to the actual eigenvector
condition over every further coefficient algebra. -/
theorem mem_cocharacterWeightSpaceOver_iff (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ) (z : R ⊗[K] (n → D)) :
    z ∈ σ.cocharacterWeightSpaceOver q f R c ↔
      ∀ (S : CommAlgCat.{u} (CommRingCat.of K)) (φ : R ⟶ S)
        (t : GroupScheme.affinePoints (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp S),
        σ.isometryRowActionOver q S (t ≫ f.hom.hom)
            (cocharacterRowSpecialization φ z) =
          (Gm.affineUnitsEquiv (CommRingCat.of K) S t ^ c : Sˣ) •
            cocharacterRowSpecialization φ z := by
  change (σ.isometryRowActionOver q (cocharacterExtendedTestAlgebra K R)
      (cocharacterExtendedTestPoint R ≫ f.hom.hom) (cocharacterExtendedRow R z) -
        cocharacterExtendedMonomialRow R c z = 0) ↔ _
  rw [sub_eq_zero]
  constructor
  · intro hz S φ t
    let ev := cocharacterExtendedEvaluation φ
      (Gm.affineUnitsEquiv (CommRingCat.of K) S t)
    have ht : (σ.isometryGroup q).affinePointMap ev
        (cocharacterExtendedTestPoint R ≫ f.hom.hom) = t ≫ f.hom.hom := by
      change ((algSpec (CommRingCat.of K)).map ev.op ≫
        cocharacterExtendedTestPoint R) ≫ f.hom.hom = _
      rw [show (algSpec (CommRingCat.of K)).map ev.op ≫
        cocharacterExtendedTestPoint R = t from cocharacterExtendedTestPoint_evaluate φ t]
    have h := σ.isometryRowActionOver_naturality q ev
      (cocharacterExtendedTestPoint R ≫ f.hom.hom) (cocharacterExtendedRow R z)
    rw [ht, hz, cocharacterExtendedRow_evaluate,
      cocharacterExtendedMonomialRow_evaluate] at h
    exact h
  · intro hz
    have h := hz (cocharacterExtendedTestAlgebra K R)
      (cocharacterExtendedCoefficientMap R) (cocharacterExtendedTestPoint R)
    rw [cocharacterRowSpecialization_coefficientMap] at h
    change _ = (((Gm.affineUnitsEquiv (CommRingCat.of K)
      (cocharacterExtendedTestAlgebra K R) (cocharacterExtendedTestPoint R)) ^ c : _ˣ) :
        R ⊗[K] LaurentPolynomial K) • cocharacterExtendedRow R z at h
    rw [cocharacterExtendedTestPoint_zpow_val, ← cocharacterExtendedMonomialRow_eq_smul] at h
    exact h

/-- Rebracket and distribute the scalar extension of Laurent-valued rows. -/
def cocharacterExtendedEquationEquiv (R : CommAlgCat.{u} (CommRingCat.of K)) :
    R ⊗[K] (n → LaurentPolynomial K ⊗[K] D) ≃ₗ[R]
      (n → (R ⊗[K] LaurentPolynomial K) ⊗[K] D) :=
  TensorProduct.piRight K R R (fun _ : n => LaurentPolynomial K ⊗[K] D) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ =>
      (TensorProduct.AlgebraTensorModule.assoc K K R R (LaurentPolynomial K) D).symm)

omit [FiniteDimensional K D] in
theorem cocharacterExtendedEquationEquiv_tmul
    (R : CommAlgCat.{u} (CommRingCat.of K)) (r : R)
    (v : n → LaurentPolynomial K ⊗[K] D) (i : n) :
    cocharacterExtendedEquationEquiv R (r ⊗ₜ[K] v) i =
      (TensorProduct.AlgebraTensorModule.assoc K K R R (LaurentPolynomial K) D).symm
        (r ⊗ₜ[K] v i) := rfl

/-- Tensoring the ground-field equation gives the actual extended row equation. -/
theorem cocharacterWeightEquationOver_eq (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ) :
    σ.cocharacterWeightEquationOver q f R c =
      (cocharacterExtendedEquationEquiv R).toLinearMap.comp
        ((σ.cocharacterWeightEquation q f c).baseChange R) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro r v
  have ht :
      (σ.isometryGroup q).affinePointMap (cocharacterExtendedLaurentMap R)
          (cocharacterWeightUniversalPoint K ≫ f.hom.hom) =
        cocharacterExtendedTestPoint R ≫ f.hom.hom := by
    change (algSpec (CommRingCat.of K)).map (cocharacterExtendedLaurentMap R).op ≫
      (cocharacterWeightUniversalPoint K ≫ f.hom.hom) =
      ((algSpec (CommRingCat.of K)).map (cocharacterExtendedLaurentMap R).op ≫
        cocharacterWeightUniversalPoint K) ≫ f.hom.hom
    exact (Category.assoc _ _ _).symm
  have hn := σ.isometryRowActionOver_naturality q (cocharacterExtendedLaurentMap R)
    (cocharacterWeightUniversalPoint K ≫ f.hom.hom)
    (fun i => (1 : LaurentPolynomial K) ⊗ₜ[K] v i)
  rw [ht] at hn
  have hins :
      cocharacterExtendedRow R (r ⊗ₜ[K] v) =
        r • (fun i => Algebra.TensorProduct.map
          (cocharacterExtendedLaurentMap R).hom (AlgHom.id K D)
            ((1 : LaurentPolynomial K) ⊗ₜ[K] v i)) := by
    funext i
    simp [cocharacterExtendedRow, cocharacterExtendedLaurentMap,
      TensorProduct.smul_tmul']
  have ha :
      σ.isometryRowActionOver q (cocharacterExtendedTestAlgebra K R)
          (cocharacterExtendedTestPoint R ≫ f.hom.hom)
          (cocharacterExtendedRow R (r ⊗ₜ[K] v)) =
        r • (fun i => Algebra.TensorProduct.map
          (cocharacterExtendedLaurentMap R).hom (AlgHom.id K D)
            (σ.cocharacterUniversalRowAction q f v i)) := by
    rw [hins, LinearMap.map_smul_of_tower, hn]
    rfl
  have hrebracket (p : LaurentPolynomial K ⊗[K] D) :
      r • Algebra.TensorProduct.map (cocharacterExtendedLaurentMap R).hom
          (AlgHom.id K D) p =
        (TensorProduct.AlgebraTensorModule.assoc K K R R (LaurentPolynomial K) D).symm
          (r ⊗ₜ[K] p) := by
    induction p with
    | tmul p d =>
      simp [cocharacterExtendedLaurentMap, TensorProduct.smul_tmul']
    | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add, smul_add]
  change σ.isometryRowActionOver q (cocharacterExtendedTestAlgebra K R)
      (cocharacterExtendedTestPoint R ≫ f.hom.hom)
      (cocharacterExtendedRow R (r ⊗ₜ[K] v)) -
        cocharacterExtendedMonomialRow R c (r ⊗ₜ[K] v) =
      cocharacterExtendedEquationEquiv R
        (r ⊗ₜ[K] (σ.cocharacterWeightEquation q f c v))
  rw [ha]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, hrebracket,
    cocharacterExtendedEquationEquiv_tmul]
  simp [cocharacterWeightEquation, cocharacterExtendedMonomialRow,
    TensorProduct.tmul_sub]

/-- The actual extended weight space is the kernel of the tensor-extended equation. -/
theorem cocharacterWeightSpaceOver_eq_ker_baseChange (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ) :
    σ.cocharacterWeightSpaceOver q f R c =
      LinearMap.ker ((σ.cocharacterWeightEquation q f c).baseChange R) := by
  ext z
  change σ.cocharacterWeightEquationOver q f R c z = 0 ↔ _
  rw [σ.cocharacterWeightEquationOver_eq]
  exact (cocharacterExtendedEquationEquiv R).map_eq_zero_iff

/-- The actual extended weight space is the scalar extension of the original
all-test weight space. -/
def cocharacterWeightBaseChangeEquiv (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ) :
    R ⊗[K] (σ.cocharacterWeightSpace q f c) ≃ₗ[R]
      σ.cocharacterWeightSpaceOver q f R c :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R)
      (LinearEquiv.ofEq _ _ (σ.ker_cocharacterWeightEquation q f c).symm) ≪≫ₗ
    LinearMap.tensorKerEquiv R R (σ.cocharacterWeightEquation q f c) ≪≫ₗ
      LinearEquiv.ofEq _ _ (σ.cocharacterWeightSpaceOver_eq_ker_baseChange q f R c).symm

theorem cocharacterWeightBaseChangeEquiv_tmul (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (R : CommAlgCat.{u} (CommRingCat.of K)) (c : ℤ)
    (r : R) (v : σ.cocharacterWeightSpace q f c) :
    (σ.cocharacterWeightBaseChangeEquiv q f R c (r ⊗ₜ[K] v) :
      R ⊗[K] (n → D)) = r ⊗ₜ[K] (v : n → D) := rfl

/-- Field extension preserves the ground-field dimension of an actual weight space. -/
theorem finrank_cocharacterWeightSpaceOver (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (L : Type u) [Field L] [Algebra K L] (c : ℤ) :
    finrank L (σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) c) =
        finrank K (σ.cocharacterWeightSpace q f c) := by
  rw [← (σ.cocharacterWeightBaseChangeEquiv q f
    (CommAlgCat.of (CommRingCat.of K) L) c).finrank_eq]
  exact Module.finrank_baseChange

/-- In division-algebra units the extended dimension is the original dimension
times the dimension of the division algebra over its ground field. -/
theorem finrank_cocharacterWeightSpaceOver_eq_mul (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (L : Type u) [Field L] [Algebra K L] (c : ℤ) :
    finrank L (σ.cocharacterWeightSpaceOver q f
      (CommAlgCat.of (CommRingCat.of K) L) c) =
        finrank K D * finrank D (σ.cocharacterWeightSpace q f c) := by
  rw [σ.finrank_cocharacterWeightSpaceOver]
  exact (Module.finrank_mul_finrank K D (σ.cocharacterWeightSpace q f c)).symm

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
