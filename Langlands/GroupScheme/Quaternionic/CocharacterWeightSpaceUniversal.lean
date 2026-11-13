import Langlands.GroupScheme.Quaternionic.CocharacterWeightSpace
import Langlands.GroupScheme.MultiplicativeLaurent

/-! # Universal detection of division-algebra row weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]

/-- The coefficient-algebra isometry unit is natural in the test algebra. -/
theorem isometryAffineUnitsOver_naturality (q : σ.QuadraticForms n)
    {R S : CommAlgCat.{u} (CommRingCat.of K)} (φ : R ⟶ S)
    (a : (σ.isometryGroup q).affinePoints R) :
    σ.isometryAffineUnitsOver q S
        ((σ.isometryGroup q).affinePointMap φ a) =
      Units.map (Algebra.TensorProduct.map φ.hom (AlgHom.id K (Matrix n n D))).toMonoidHom
        (σ.isometryAffineUnitsOver q R a) := by
  change FiniteAlgebraUnits.affinePointsEquiv _ S
    (((algSpec (CommRingCat.of K)).map φ.op ≫ a) ≫
      (σ.isometryGroupι q).hom.hom) = _
  rw [Category.assoc]
  exact FiniteAlgebraUnits.affinePointsEquiv_naturality _ φ _

/-- The inverse-right row operator over an arbitrary commutative test algebra. -/
def isometryRowActionOver (q : σ.QuadraticForms n)
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (a : (σ.isometryGroup q).affinePoints R) :
    Module.End (R ⊗[K] D) (n → R ⊗[K] D) :=
  (TensorMatrix.equiv R n
    (((σ.isometryAffineUnitsOver q R a)⁻¹ : (R ⊗[K] Matrix n n D)ˣ) :
      R ⊗[K] Matrix n n D)).toLinearMapRight'

/-- Row action commutes with every map of coefficient algebras. -/
theorem isometryRowActionOver_naturality (q : σ.QuadraticForms n)
    {R S : CommAlgCat.{u} (CommRingCat.of K)} (φ : R ⟶ S)
    (a : (σ.isometryGroup q).affinePoints R) (v : n → R ⊗[K] D) :
    σ.isometryRowActionOver q S ((σ.isometryGroup q).affinePointMap φ a)
        (fun i => Algebra.TensorProduct.map φ.hom (AlgHom.id K D) (v i)) =
      fun i => Algebra.TensorProduct.map φ.hom (AlgHom.id K D)
        (σ.isometryRowActionOver q R a v i) := by
  unfold isometryRowActionOver
  rw [isometryAffineUnitsOver_naturality, ← map_inv]
  simp only [Units.coe_map, Matrix.toLinearMapRight'_apply]
  change Matrix.vecMul _
      (TensorMatrix.equiv S n (Algebra.TensorProduct.map φ.hom (AlgHom.id K _)
        (((σ.isometryAffineUnitsOver q R a)⁻¹ : (R ⊗[K] Matrix n n D)ˣ) :
          R ⊗[K] Matrix n n D))) = _
  rw [TensorMatrix.naturality]
  funext i
  exact (RingHom.map_vecMul
    (Algebra.TensorProduct.map φ.hom (AlgHom.id K D)).toRingHom _ v i).symm

variable (K) in
/-- The Laurent test algebra used to detect all cocharacter weights. -/
abbrev cocharacterWeightTestAlgebra : CommAlgCat.{u} (CommRingCat.of K) :=
  CommAlgCat.of (CommRingCat.of K) (LaurentPolynomial K)

variable (K) in
/-- The coefficient point of the multiplicative group whose unit is the Laurent variable. -/
def cocharacterWeightUniversalPoint :
    GroupScheme.affinePoints (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
      (cocharacterWeightTestAlgebra K) :=
  (Gm.affineUnitsEquiv (CommRingCat.of K) (cocharacterWeightTestAlgebra K)).symm
    (Gm.relativeCoordUnit K)

variable (K) in
theorem cocharacterWeightUniversalPoint_unit :
    Gm.affineUnitsEquiv (CommRingCat.of K) (cocharacterWeightTestAlgebra K)
      (cocharacterWeightUniversalPoint K) = Gm.relativeCoordUnit K :=
  MulEquiv.apply_symm_apply _ _

/-- Evaluation of the Laurent variable at an arbitrary coefficient unit. -/
def cocharacterWeightEvaluation (R : CommAlgCat.{u} (CommRingCat.of K)) (t : Rˣ) :
    cocharacterWeightTestAlgebra K ⟶ R :=
  ConcreteCategory.ofHom (C := CommAlgCat (CommRingCat.of K))
    { LaurentPolynomial.eval₂ (algebraMap K R) t with
      commutes' := fun r => LaurentPolynomial.eval₂_C _ _ r }

theorem cocharacterWeightEvaluation_T (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : Rˣ) (c : ℤ) :
    (cocharacterWeightEvaluation R t).hom (LaurentPolynomial.T c) = (t ^ c : Rˣ) := by
  change LaurentPolynomial.eval₂ (algebraMap K R) t (LaurentPolynomial.T c) = _
  exact LaurentPolynomial.eval₂_T _ _ _

/-- Every coefficient point is obtained by evaluating the Laurent universal point. -/
theorem cocharacterWeightUniversalPoint_evaluate
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp R) :
    GroupScheme.affinePointMap (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
        (cocharacterWeightEvaluation R (Gm.affineUnitsEquiv (CommRingCat.of K) R t))
        (cocharacterWeightUniversalPoint K) = t := by
  apply (Gm.affineUnitsEquiv (CommRingCat.of K) R).injective
  rw [Gm.affineUnitsEquiv_naturality, cocharacterWeightUniversalPoint_unit]
  apply Units.ext
  change LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T 1) = _
  simp

/-- A row has cocharacter weight `c` if and only if its weight equation holds at
the single Laurent universal point. This retains finite fields and characteristic two. -/
theorem mem_cocharacterWeightSpace_iff_universal (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (c : ℤ) (v : n → D) :
    v ∈ σ.cocharacterWeightSpace q f c ↔
      σ.isometryRowActionOver q (cocharacterWeightTestAlgebra K)
          (cocharacterWeightUniversalPoint K ≫ f.hom.hom)
          (fun i => (1 : LaurentPolynomial K) ⊗ₜ[K] v i) =
        fun i => LaurentPolynomial.T c ⊗ₜ[K] v i := by
  constructor
  · intro hv
    have h := hv (cocharacterWeightTestAlgebra K) (cocharacterWeightUniversalPoint K)
    rw [cocharacterWeightUniversalPoint_unit, Gm.relativeCoordUnit_zpow_val] at h
    exact h
  · intro hv R t
    let φ := cocharacterWeightEvaluation R
      (Gm.affineUnitsEquiv (CommRingCat.of K) R t)
    have ht :
        (σ.isometryGroup q).affinePointMap φ
            (cocharacterWeightUniversalPoint K ≫ f.hom.hom) = t ≫ f.hom.hom := by
      change ((algSpec (CommRingCat.of K)).map φ.op ≫
        cocharacterWeightUniversalPoint K) ≫ f.hom.hom = _
      rw [show (algSpec (CommRingCat.of K)).map φ.op ≫
          cocharacterWeightUniversalPoint K = t from
        cocharacterWeightUniversalPoint_evaluate R t]
    have h := σ.isometryRowActionOver_naturality q φ
      (cocharacterWeightUniversalPoint K ≫ f.hom.hom)
      (fun i => (1 : LaurentPolynomial K) ⊗ₜ[K] v i)
    rw [ht, hv] at h
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at h
    have h1 : φ.hom (1 : LaurentPolynomial K) = (1 : R) := φ.hom.map_one
    have hT : φ.hom (LaurentPolynomial.T c) =
        ((Gm.affineUnitsEquiv (CommRingCat.of K) R t) ^ c : Rˣ) :=
      cocharacterWeightEvaluation_T R _ c
    rw [h1, hT] at h
    exact h

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
