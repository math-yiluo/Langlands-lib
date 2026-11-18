import Langlands.GroupScheme.SimplyConnected.NormOneTitsDescent
import Langlands.Algebra.GaloisAlgebraDescentInfinite
import Langlands.Algebra.MatrixAlgEquivInnerProof

/-! # Actual Galois conjugators of a norm-one splitting chart -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralSimpleUnits.TitsDescent

open Langlands.GaloisAlgebraDescent

variable {k L A : Type u} [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A]
    {I : Type} [Fintype I] [DecidableEq I]
    (e : L ⊗[k] A ≃ₐ[L] Matrix I I L)

private theorem coefficientConjugate_symm_apply (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    coefficientConjugate k L A σ.symm (coefficientConjugate k L A σ x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul l a => simp only [coefficientConjugate_tmul, σ.symm_apply_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The Galois-shifted chart, made linear by the inverse coefficient action. -/
def galoisChart (σ : L ≃ₐ[k] L) : L ⊗[k] A ≃ₐ[L] Matrix I I L where
  toRingEquiv :=
    ((Algebra.TensorProduct.congr σ.symm (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv.trans
      e.toRingEquiv).trans σ.toRingEquiv.mapMatrix
  commutes' l := by
    change (e (coefficientConjugate k L A σ.symm
      (algebraMap L (L ⊗[k] A) l))).map σ = algebraMap L (Matrix I I L) l
    rw [Algebra.algebraMap_eq_smul_one, coefficientConjugate_smul, map_one,
      map_smul, map_one]
    ext i j
    by_cases h : i = j <;>
      simp [h, Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_eq_smul_one]

@[simp] theorem galoisChart_apply (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    galoisChart e σ x = (e (coefficientConjugate k L A σ.symm x)).map σ := rfl

@[simp] theorem galoisChart_constant (σ : L ≃ₐ[k] L) (a : A) :
    galoisChart e σ (1 ⊗ₜ[k] a) = (e (1 ⊗ₜ[k] a)).map σ := by
  rw [galoisChart_apply, coefficientConjugate_tmul, map_one]

/-- A chosen invertible matrix comparing the actual original and Galois-shifted charts. -/
def galoisConjugator (σ : L ≃ₐ[k] L) : (Matrix I I L)ˣ :=
  Classical.choose (Langlands.MatrixAlgebra.exists_unit_conj_of_charts e (galoisChart e σ))

theorem galoisConjugator_spec (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    galoisChart e σ x =
      (galoisConjugator e σ : Matrix I I L) * e x *
        ((galoisConjugator e σ)⁻¹ : (Matrix I I L)ˣ) :=
  Classical.choose_spec
    (Langlands.MatrixAlgebra.exists_unit_conj_of_charts e (galoisChart e σ)) x

/-- The conjugator has the convention used by the actual twisted fixed matrix algebra. -/
theorem galoisConjugator_constant (σ : L ≃ₐ[k] L) (a : A) :
    (galoisConjugator e σ : Matrix I I L) * e (1 ⊗ₜ[k] a) =
      (e (1 ⊗ₜ[k] a)).map σ * (galoisConjugator e σ : Matrix I I L) := by
  have h := congrArg (fun M : Matrix I I L => M * (galoisConjugator e σ : Matrix I I L))
    (galoisConjugator_spec e σ (1 ⊗ₜ[k] a))
  rw [galoisChart_constant] at h
  simpa only [mul_assoc, Units.inv_mul, mul_one] using h.symm

/-- The chart-induced semilinear matrix action is exactly twisted coefficient conjugation. -/
theorem galoisConjugator_matrixAction (σ : L ≃ₐ[k] L) (X : Matrix I I L) :
    (galoisConjugator e σ : Matrix I I L) * (matrixAction e).act σ X =
      X.map σ * (galoisConjugator e σ : Matrix I I L) := by
  have h := congrArg (fun M : Matrix I I L => M * (galoisConjugator e σ : Matrix I I L))
    (galoisConjugator_spec e σ (coefficientConjugate k L A σ (e.symm X)))
  rw [galoisChart_apply, coefficientConjugate_symm_apply, e.apply_symm_apply] at h
  simpa only [matrixAction_act, mul_assoc, Units.inv_mul, mul_one] using h.symm

/-- The actual fixed algebra agrees with the all-Galois intertwining equations. -/
theorem mem_fixed_iff_galoisConjugator (X : Matrix I I L) :
    X ∈ (matrixAction e).fixed ↔
      ∀ σ : L ≃ₐ[k] L, (galoisConjugator e σ : Matrix I I L) * X =
        X.map σ * (galoisConjugator e σ : Matrix I I L) := by
  constructor
  · intro hX σ
    have h := galoisConjugator_matrixAction e σ X
    rw [hX σ] at h
    exact h
  · intro hX σ
    have h := (galoisConjugator_matrixAction e σ X).trans (hX σ).symm
    exact (galoisConjugator e σ).isUnit.mul_right_injective h

section ArbitraryGalois

variable [IsGalois k L]

theorem fixedHom_surjective_of_isGalois : Function.Surjective (fixedHom e) := by
  intro X
  have hx : ∀ σ : L ≃ₐ[k] L,
      coefficientConjugate k L A σ (e.symm (X : Matrix I I L)) =
        e.symm (X : Matrix I I L) := by
    intro σ
    apply e.injective
    rw [e.apply_symm_apply]
    exact X.property σ
  obtain ⟨a, ha⟩ := (mem_range_includeRight_iff_of_isGalois k L A
    (e.symm (X : Matrix I I L))).mpr hx
  refine ⟨a, Subtype.ext ?_⟩
  change e ((Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A) a) = _
  change (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A) a =
    e.symm (X : Matrix I I L) at ha
  rw [ha, e.apply_symm_apply]

/-- Over any Galois splitting extension the actual fixed matrix algebra is the original algebra. -/
def fixedEquivOfIsGalois : A ≃ₐ[k] (matrixAction e).fixed :=
  AlgEquiv.ofBijective (fixedHom e)
    ⟨fixedHom_injective e, fixedHom_surjective_of_isGalois e⟩

@[simp] theorem fixedEquivOfIsGalois_val (a : A) :
    (fixedEquivOfIsGalois e a : Matrix I I L) = e (1 ⊗ₜ[k] a) := rfl

end ArbitraryGalois

section AllTests

open SpecialLinearInnerForm

variable {R : Type u} [CommRing R] [Algebra k R]
    (f : L →+* R) (hf : f.comp (algebraMap k L) = algebraMap k R)

/-- Every coefficient extension of the original algebra chart has the same Galois intertwiner. -/
theorem galoisConjugator_chartAlong (σ : L ≃ₐ[k] L) (x : R ⊗[k] A) :
    (galoisConjugator e σ : Matrix I I L).map f * chartAlong e f hf x =
      chartAlong e (f.comp σ.toAlgHom.toRingHom)
        (by
          apply RingHom.ext
          intro r
          change f (σ (algebraMap k L r)) = algebraMap k R r
          rw [σ.commutes]
          exact RingHom.congr_fun hf r) x *
          (galoisConjugator e σ : Matrix I I L).map f := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [chartAlong_tmul, chartAlong_tmul, mul_smul_comm, smul_mul_assoc]
    have h := congrArg (fun M : Matrix I I L => M.map f) (galoisConjugator_constant e σ a)
    simp only [Matrix.map_mul, Matrix.map_map] at h
    change (galoisConjugator e σ : Matrix I I L).map f * (e (1 ⊗ₜ[k] a)).map f =
      (e (1 ⊗ₜ[k] a)).map (f.comp σ.toAlgHom.toRingHom) *
        (galoisConjugator e σ : Matrix I I L).map f at h
    exact congrArg (fun M : Matrix I I R => r • M) h
  | add x y hx hy =>
    simp only [map_add, mul_add, add_mul, hx, hy]

end AllTests

section NormOnePoints

open SpecialLinearInnerForm Langlands.AlgebraicGeometry.PointTopology

variable [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]

/-- The actual norm-one chart matrices have the constructed Galois intertwiner on every test. -/
theorem galoisConjugator_normOneChartPoints (σ : L ≃ₐ[k] L)
    {V : Over (Spec (CommRingCat.of k))} (s : V ⟶ ringTest k L)
    (g : V ⟶ (normOne k A).X) :
    (galoisConjugator e σ : Matrix I I L).map (pointScalars s) *
      (normOneChartPoints e s g : Matrix I I _) =
        (normOneChartPoints e (s ≫ ringTestMap k σ.toAlgHom) g : Matrix I I _) *
          (galoisConjugator e σ : Matrix I I L).map (pointScalars s) := by
  rw [normOneChartPoints_val, normOneChartPoints_val]
  have hs : pointScalars (s ≫ ringTestMap k σ.toAlgHom) =
      (pointScalars s).comp σ.toAlgHom.toRingHom :=
    pointScalars_comp_ringTestMap s σ
  rw [chartAlong_congr e (pointScalars_comp_algebraMap _) hs]
  exact galoisConjugator_chartAlong e (pointScalars s)
    (pointScalars_comp_algebraMap s) σ _

end NormOnePoints

end Langlands.GroupScheme.CentralSimpleUnits.TitsDescent
