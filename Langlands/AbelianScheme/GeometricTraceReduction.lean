import Langlands.AbelianScheme.GeometricEndomorphismTraceComparisonStatement
import Langlands.AbelianScheme.Tate.GeometricPrimeAdicRankProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # Geometric rank and rational extension of integral prime traces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AbelianScheme.GeometricTrace

variable {k : Type u} [Field k]
  (A : AbelianScheme (Spec (CommRingCat.of k)))

private theorem prime_isUnit [CharZero k] (p : ℕ) [Fact p.Prime] :
    IsUnit (p : Γ(Spec (CommRingCat.of k), ⊤)) := by
  have hp : (p : k) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  simpa using (isUnit_iff_ne_zero.mpr hp).map (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The actual rational Tate module has geometric rank at every prime. -/
theorem primeTate_finrank [IsAlgClosed k] [CharZero k]
    (p : ℕ) [Fact p.Prime] (g : ℕ)
    (hg : A.HasRelativeDimension g) :
    Module.finrank ℚ_[p] (Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) p) = 2 * g :=
  (Tate.PrimeAdic.geometricPrimeAdicRank _ A g hg p (prime_isUnit p) k (𝟙 _)).2.2

/-- Finite dimensionality does not require a supplied relative dimension. -/
theorem primeTate_finiteDimensional [IsAlgClosed k] [CharZero k]
    (p : ℕ) [Fact p.Prime] :
    FiniteDimensional ℚ_[p] (Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) p) := by
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  obtain ⟨g, hg⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    _ _ A.X.hom inferInstance inferInstance
  exact (Tate.PrimeAdic.geometricPrimeAdicRank _ A g hg p
    (prime_isUnit p) k (𝟙 _)).2.1

/-- The actual prime trace restricted to integral endomorphisms. -/
def integralPrimeTrace (p : ℕ) [Fact p.Prime] : End A →ₗ[ℤ] ℚ_[p] :=
  ((primeEndomorphismTrace A p).restrictScalars ℤ).comp
    (endToEnd0 A).toAddMonoidHom.toIntLinearMap

/-- Common rational values on integral endomorphisms extend pointwise to End0. -/
theorem exists_commonRationalTrace
    (h : ∀ f : End A, ∃ t : ℚ,
      ∀ (p : ℕ) [Fact p.Prime], algebraMap ℚ ℚ_[p] t = integralPrimeTrace A p f)
    (a : End0 A) :
    ∃ t : ℚ, ∀ (p : ℕ) [Fact p.Prime],
      algebraMap ℚ ℚ_[p] t = primeEndomorphismTrace A p a := by
  obtain ⟨a⟩ := a
  induction a using TensorProduct.inductionOn with
  | tmul q f =>
      obtain ⟨t, ht⟩ := h (End.of f)
      refine ⟨q * t, ?_⟩
      intro p _
      have he : (End.of (q ⊗ₜ[ℤ] f) : End0 A) = q • (End.of (homToHom0 f) : End0 A) := by
        apply End.ext
        change q ⊗ₜ[ℤ] f = q • homToHom0 f
        simp [homToHom0_apply, TensorProduct.smul_tmul']
      change _ = primeEndomorphismTrace A p (End.of (q ⊗ₜ[ℤ] f) : End0 A)
      rw [he, map_smul, map_mul, ht p]
      rfl
  | add a b ha hb =>
      obtain ⟨t, ht⟩ := ha
      obtain ⟨s, hs⟩ := hb
      refine ⟨t + s, ?_⟩
      intro p _
      change _ = primeEndomorphismTrace A p ((End.of a : End0 A) + (End.of b : End0 A))
      rw [map_add, ht p, hs p, map_add]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A common rational integral trace determines a rational-linear trace on End0. -/
def rationalTraceOfIntegral
    (h : ∀ f : End A, ∃ t : ℚ,
      ∀ (p : ℕ) [Fact p.Prime], algebraMap ℚ ℚ_[p] t = integralPrimeTrace A p f) :
    End0 A →ₗ[ℚ] ℚ where
  toFun a := (exists_commonRationalTrace A h a).choose
  map_add' a b := by
    apply (algebraMap ℚ ℚ_[2]).injective
    rw [map_add, (exists_commonRationalTrace A h (a + b)).choose_spec 2,
      (exists_commonRationalTrace A h a).choose_spec 2,
      (exists_commonRationalTrace A h b).choose_spec 2, map_add]
  map_smul' q a := by
    apply (algebraMap ℚ ℚ_[2]).injective
    change algebraMap ℚ ℚ_[2] (exists_commonRationalTrace A h (q • a)).choose =
      algebraMap ℚ ℚ_[2] (q • (exists_commonRationalTrace A h a).choose)
    rw [(exists_commonRationalTrace A h (q • a)).choose_spec 2,
      map_rat_smul (algebraMap ℚ ℚ_[2]),
      (exists_commonRationalTrace A h a).choose_spec 2, map_smul]

theorem rationalTraceOfIntegral_spec
    (h : ∀ f : End A, ∃ t : ℚ,
      ∀ (p : ℕ) [Fact p.Prime], algebraMap ℚ ℚ_[p] t = integralPrimeTrace A p f)
    (p : ℕ) [Fact p.Prime] (a : End0 A) :
    algebraMap ℚ ℚ_[p] (rationalTraceOfIntegral A h a) =
      primeEndomorphismTrace A p a :=
  (exists_commonRationalTrace A h a).choose_spec p

/-- It suffices to establish rationality and prime independence on integral
endomorphisms. Geometric rank and rational linearity supply the other clauses. -/
theorem comparison_of_integral
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
      (A : AbelianScheme (Spec (CommRingCat.of k))) (f : End A), ∃ t : ℚ,
        ∀ (p : ℕ) [Fact p.Prime],
          algebraMap ℚ ℚ_[p] t = integralPrimeTrace A p f) :
    GeometricEndomorphismTraceComparisonStatement.{u} := by
  intro k _ _ _ A p _
  refine ⟨primeTate_finiteDimensional A p, primeTate_finrank A p, ?_⟩
  have he := geometricEndomorphismTrace_eq A (rationalTraceOfIntegral A (h k A))
    (rationalTraceOfIntegral_spec A (h k A) 2)
  intro a
  rw [he]
  exact rationalTraceOfIntegral_spec A (h k A) p a

end Langlands.AbelianScheme.GeometricTrace
