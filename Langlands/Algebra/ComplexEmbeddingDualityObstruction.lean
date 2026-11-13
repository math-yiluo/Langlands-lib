import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky
import Mathlib.Algebra.Field.ULift

/-!
# A complex embedding whose restriction module differs from its dual

Internal algebraic input for auditing the bare-additive interpretation of
Renard I.4.2. This module supplies the restriction-module construction and its intrinsic dimension
obstruction. The source's actual functor identifications are separate.
-/

noncomputable section

open Cardinal

namespace Langlands.Algebra.ComplexEmbeddingDualityObstruction

private abbrev K := FractionRing (Polynomial ℂ)
private abbrev L := AlgebraicClosure K

private theorem cardinal_L : #L = #ℂ := by
  have hK : #K = #ℂ := by
    rw [Cardinal.mk_fractionRing, Polynomial.cardinalMk_eq_max,
      max_eq_left (by rw [Cardinal.mk_complex]; exact aleph0_le_continuum)]
  apply le_antisymm
  · calc
      #L ≤ max #K ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max K L
      _ = #ℂ := by rw [hK, max_eq_left (by
        rw [Cardinal.mk_complex]
        exact aleph0_le_continuum)]
  · exact Cardinal.mk_le_of_injective (RingHom.injective (algebraMap ℂ L))

private theorem inclusion_not_surjective : ¬ Function.Surjective (algebraMap ℂ L) := by
  have htransK : Transcendental ℂ (algebraMap (Polynomial ℂ) K Polynomial.X) :=
    (transcendental_algebraMap_iff (R := ℂ)
      (IsFractionRing.injective (Polynomial ℂ) K)).2 (Polynomial.transcendental_X ℂ)
  have htransL : Transcendental ℂ
      (algebraMap K L (algebraMap (Polynomial ℂ) K Polynomial.X)) :=
    (transcendental_algebraMap_iff (R := ℂ)
      (RingHom.injective (algebraMap K L))).2 htransK
  intro h
  obtain ⟨c, hc⟩ := h (algebraMap K L (algebraMap (Polynomial ℂ) K Polynomial.X))
  apply htransL
  rw [← hc]
  exact isAlgebraic_algebraMap c

/-- A unital field endomorphism of the complex numbers need not be onto. -/
theorem exists_nonsurjective_endomorphism :
    ∃ σ : ℂ →+* ℂ, ¬ Function.Surjective σ := by
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (K := ℂ) (L := L) (by rw [Cardinal.mk_complex]; exact aleph0_lt_continuum)
    (Cardinal.eq.mp cardinal_L.symm)
  refine ⟨e.symm.toRingHom.comp (algebraMap ℂ L), ?_⟩
  intro h
  apply inclusion_not_surjective
  intro x
  obtain ⟨c, hc⟩ := h (e.symm x)
  exact ⟨c, e.symm.injective hc⟩

/-- A distinct copy of the ordinary complex field, with scalars restricted by `σ`. -/
def Carrier (_σ : ℂ →+* ℂ) := ULift.{0} ℂ

instance (σ : ℂ →+* ℂ) : Field (Carrier σ) :=
  inferInstanceAs (Field (ULift.{0} ℂ))

/-- The ordinary underlying-field comparison; this does not preserve complex scalars. -/
def carrierRingEquiv (σ : ℂ →+* ℂ) : Carrier σ ≃+* ℂ :=
  ULift.ringEquiv

instance (σ : ℂ →+* ℂ) : Algebra ℂ (Carrier σ) :=
  ((carrierRingEquiv σ).symm.toRingHom.comp σ).toAlgebra

@[simp]
theorem carrier_algebraMap (σ : ℂ →+* ℂ) (c : ℂ) :
    carrierRingEquiv σ (algebraMap ℂ (Carrier σ) c) = σ c := rfl

@[simp]
theorem carrier_smul (σ : ℂ →+* ℂ) (c : ℂ) (z : Carrier σ) :
    carrierRingEquiv σ (c • z) = σ c * carrierRingEquiv σ z := rfl

/-- A proper self-embedding gives an infinite-dimensional restriction module. -/
theorem not_finite (σ : ℂ →+* ℂ) (hσ : ¬ Function.Surjective σ) :
    ¬ Module.Finite ℂ (Carrier σ) := by
  intro h
  let := h
  have hs := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ℂ) (K := Carrier σ)).2
  apply hσ
  intro c
  obtain ⟨z, hz⟩ := hs ((carrierRingEquiv σ).symm c)
  exact ⟨z, by simpa using congrArg (carrierRingEquiv σ) hz⟩

/-- The actual complex algebraic dual has strictly greater dimension. -/
theorem rank_lt_dual (σ : ℂ →+* ℂ) (hσ : ¬ Function.Surjective σ) :
    Module.rank ℂ (Carrier σ) < Module.rank ℂ (Module.Dual ℂ (Carrier σ)) := by
  apply rank_lt_rank_dual
  exact le_of_not_gt fun h ↦ not_finite σ hσ (Module.rank_lt_aleph0_iff.mp h)

/-- Consequently no complex-linear equivalence with that algebraic dual exists. -/
theorem no_linearEquiv_dual (σ : ℂ →+* ℂ) (hσ : ¬ Function.Surjective σ) :
    IsEmpty (Carrier σ ≃ₗ[ℂ] Module.Dual ℂ (Carrier σ)) := by
  refine ⟨fun e ↦ ?_⟩
  exact (ne_of_lt (rank_lt_dual σ hσ)) e.rank_eq

end Langlands.Algebra.ComplexEmbeddingDualityObstruction
