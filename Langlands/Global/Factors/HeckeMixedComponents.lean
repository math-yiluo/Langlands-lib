import Langlands.Global.NormOneIdeleClassCompact
import Langlands.Global.Factors.HeckeMixedProductFormula
import Langlands.Global.Factors.HeckeMultiplicativeProductFormula
import Langlands.Global.Factors.HeckeDivisorNorm

/-! # Actual infinite ideles in mixed coordinates -/

noncomputable section

universe u

namespace Langlands.Global.HeckeFunctionalEquation

open NumberField NumberField.InfinitePlace
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open scoped Real FourierTransform NNReal

variable {K : Type u} [Field K] [NumberField K]

/-- The mixed-space unit of an actual idele, using Mathlib's existing ring equivalence. -/
def mixedInfiniteUnit (a : Ideles K) : (mixedEmbedding.mixedSpace K)ˣ :=
  Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).toMonoidHom
    ((ideleProductEquiv K a).1)

@[simp] theorem mixedInfiniteUnit_mul (a b : Ideles K) :
    mixedInfiniteUnit (a * b) = mixedInfiniteUnit a * mixedInfiniteUnit b := by
  simp [mixedInfiniteUnit]

@[simp] theorem mixedInfiniteUnit_one :
    mixedInfiniteUnit (1 : Ideles K) = 1 := by
  simp [mixedInfiniteUnit]

@[simp] theorem mixedInfiniteUnit_inv (a : Ideles K) :
    mixedInfiniteUnit a⁻¹ = (mixedInfiniteUnit a)⁻¹ := by
  simp [mixedInfiniteUnit]

@[simp] theorem mixedInfiniteUnit_val (a : Ideles K) :
    (mixedInfiniteUnit a : mixedEmbedding.mixedSpace K) =
      InfiniteAdeleRing.ringEquiv_mixedSpace K a.val.1 := rfl

/-- Principal ideles give precisely the mixed embedding on units. -/
theorem mixedInfiniteUnit_diagonal (a : Kˣ) :
    mixedInfiniteUnit (diagonalUnits K a) =
      Units.map (mixedEmbedding K).toMonoidHom a := by
  apply Units.ext
  change InfiniteAdeleRing.ringEquiv_mixedSpace K
      (algebraMap K (InfiniteAdeles K) (a : K)) = mixedEmbedding K (a : K)
  exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := K) (x := (a : K))).symm

/-- The mixed norm has exactly the original infinite-place multiplicities. -/
theorem norm_mixedCoordinates (x : InfiniteAdeles K) :
    mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace K x) =
      ∏ v : InfinitePlace K, ‖x v‖ ^ v.mult :=
  NormOneIdeleClass.norm_ringEquiv_mixedSpace x

theorem norm_mixedInfiniteUnit_pos (a : Ideles K) :
    0 < mixedEmbedding.norm (mixedInfiniteUnit a : mixedEmbedding.mixedSpace K) := by
  classical
  rw [mixedInfiniteUnit_val, norm_mixedCoordinates]
  apply Finset.prod_pos
  intro v _
  exact pow_pos (norm_pos_iff.mpr (infiniteIdeleProjection K v a).ne_zero) _

/-- The normalized idelic norm in the mixed-space and finite-divisor coordinates. -/
theorem full_eq_mixed_mul_divisor_norm_inv (a : Ideles K) :
    ((IdeleAbsoluteValue.full K a : ℝ≥0) : ℝ) =
      mixedEmbedding.norm (mixedInfiniteUnit a : mixedEmbedding.mixedSpace K) *
        (HeckeDivisor.norm (Langlands.ClassField.Global.ideleDivisor a))⁻¹ := by
  rw [mixedInfiniteUnit_val, norm_mixedCoordinates]
  exact HeckeDivisor.full_eq_infinite_mul_norm_inv a

set_option backward.isDefEq.respectTransparency false in
/-- Every supplied real and complex presentation gives the actual infinite character. -/
theorem infinite_character_eq_mixed
    (χ : HeckeCharacter K)
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (hR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))
    (a : Ideles K) :
    (χ.atInfinity ((ideleProductEquiv K a).1) : ℂ) =
      Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
        (fun v => (dC v).weight) (fun v => (dC v).exponent)
        (mixedInfiniteUnit a : mixedEmbedding.mixedSpace K) := by
  classical
  rw [infinite_multiplicative_product, Units.coe_prod, prod_eq_prod_mul_prod,
    Hecke.mixedCharFun]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    rw [← hR v (infiniteIdeleProjection K v.1 a), (dR v).character_eq]
    rfl
  · apply Finset.prod_congr rfl
    intro v _
    rw [← hC v (infiniteIdeleProjection K v.1 a), (dC v).character_eq]
    rfl

/-- Full local multiplicative expansion with the supplied archimedean presentations. -/
theorem character_eq_mixed_mul_finite
    (χ : HeckeCharacter K)
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (hR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))
    (a : Ideles K) (S : Finset (FinitePlace K))
    (hχ : multiplicativeIntegralControl χ ⊆ S) (ha : nonunitPlaces a ⊆ S) :
    (χ.onIdeles a : ℂ) =
      Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
        (fun v => (dC v).weight) (fun v => (dC v).exponent)
        (mixedInfiniteUnit a : mixedEmbedding.mixedSpace K) *
          ∏ v ∈ S, (χ.finiteComponent v (finiteIdeleProjection K v a) : ℂ) := by
  rw [multiplicative_product_atInfinity χ a S hχ ha, Units.val_mul, Units.coe_prod,
    infinite_character_eq_mixed χ dR hR dC hC]

set_option backward.isDefEq.respectTransparency false in
/-- The supplied scales describe the actual character on every infinite adele. -/
theorem infinite_additive_eq_mixed
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (hR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v))
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (hC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v))
    (x : InfiniteAdeles K) :
    ψ (x, (0 : FiniteAdeles K)) =
      𝐞 (Hecke.addTrace (fun v => (aR v : ℝ)) (fun v => (aC v : ℂ))
        (InfiniteAdeleRing.ringEquiv_mixedSpace K x)) := by
  classical
  rw [infinite_additive_product, prod_eq_prod_mul_prod, Hecke.addTrace_apply,
    AddChar.map_add_eq_mul, addChar_sum, addChar_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    change ψ ((Pi.single v.1 (x v.1) : InfiniteAdeles K), (0 : FiniteAdeles K)) = _
    rw [hR v, realScaledCharacter_apply]
    rfl
  · apply Finset.prod_congr rfl
    intro v _
    change ψ ((Pi.single v.1 (x v.1) : InfiniteAdeles K), (0 : FiniteAdeles K)) = _
    rw [hC v, complexScaledCharacter_apply, Algebra.trace_complex_apply]
    rfl

end Langlands.Global.HeckeFunctionalEquation
