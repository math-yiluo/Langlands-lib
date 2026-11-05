import Langlands.GroupScheme.Rational.CompactMatrixIntegrality
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-! # Spectral integrality from commuting factors of a positive power -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

section Topology

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

/-- Multiplication of actual rational points, bundled continuously for the
canonical identity-test topology. -/
def rationalPointsMulContinuousMap :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
    C(rationalPoints G × rationalPoints G, rationalPoints G) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup R G
  exact ⟨fun p => p.1 * p.2, continuous_mul⟩

@[simp] theorem rationalPointsMulContinuousMap_apply (p : rationalPoints G × rationalPoints G) :
    rationalPointsMulContinuousMap G p = p.1 * p.2 := rfl

/-- Commuting points whose nonnegative powers lie in compact sets have a
product with the same property. -/
theorem exists_compact_powers_mul (x y : rationalPoints G) (hxy : Commute x y)
    (C D : Set (rationalPoints G))
    (hC : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
      IsCompact C)
    (hD : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
      IsCompact D)
    (hx : ∀ k : ℕ, x ^ k ∈ C) (hy : ∀ k : ℕ, y ^ k ∈ D) :
    ∃ K : Set (rationalPoints G),
      (letI : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X;
        IsCompact K) ∧ ∀ k : ℕ, (x * y) ^ k ∈ K := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology R G.X
  refine ⟨rationalPointsMulContinuousMap G '' (C ×ˢ D),
    (hC.prod hD).image (rationalPointsMulContinuousMap G).continuous, fun k => ?_⟩
  exact ⟨(x ^ k, y ^ k), ⟨hx k, hy k⟩, (hxy.mul_pow k).symm⟩

end Topology

namespace MatrixRepresentation

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Integrality of the actual representation matrix descends from any positive
power of a rational point. -/
theorem isIntegral_rationalMatrix_of_pow (ρ : MatrixRepresentation G n)
    (g : rationalPoints G) {m : ℕ} (hm : 0 < m)
    (h : IsIntegral (ValuativeRel.valuation F).integer
      (ρ.rationalMatrix (g ^ m) : Matrix n n F)) :
    IsIntegral (ValuativeRel.valuation F).integer
      (ρ.rationalMatrix g : Matrix n n F) := by
  apply IsIntegral.of_pow hm
  simpa only [map_pow, Units.val_pow_eq_pow_val] using h

/-- An integral actual representation matrix has every characteristic
coefficient in the canonical valuation ring. -/
theorem charpoly_coeff_vle_one_of_isIntegral_rationalMatrix
    (ρ : MatrixRepresentation G n) (g : rationalPoints G)
    (h : IsIntegral (ValuativeRel.valuation F).integer
      (ρ.rationalMatrix g : Matrix n n F)) (i : ℕ) :
    (ρ.rationalMatrix g : Matrix n n F).charpoly.coeff i ≤ᵥ (1 : F) := by
  apply (ValuativeRel.valuation F).vle_one_iff.mpr
  apply (Valuation.integer.integers (ValuativeRel.valuation F)).isIntegral_iff_v_le_one.mp
  exact Langlands.LinearAlgebra.isIntegral_charpoly_coeff h i

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

/-- A positive power factored into commuting points with compact powers gives
an integral matrix for the original point in every actual representation. -/
theorem isIntegral_rationalMatrix_of_pow_eq_mul
    (ρ : MatrixRepresentation G n) (g x y : rationalPoints G)
    {m : ℕ} (hm : 0 < m) (hpow : g ^ m = x * y) (hxy : Commute x y)
    (C D : Set (rationalPoints G))
    (hC : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact C)
    (hD : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact D)
    (hx : ∀ k : ℕ, x ^ k ∈ C) (hy : ∀ k : ℕ, y ^ k ∈ D) :
    IsIntegral (ValuativeRel.valuation F).integer
      (ρ.rationalMatrix g : Matrix n n F) := by
  apply ρ.isIntegral_rationalMatrix_of_pow g hm
  rw [hpow]
  obtain ⟨K, hK, hxyK⟩ := exists_compact_powers_mul G x y hxy C D hC hD hx hy
  exact ρ.isIntegral_rationalMatrix_of_powers_mem_compact (x * y) K hK hxyK

/-- The corresponding coefficient bound, without any condition on the
representation's faithfulness or dimension. -/
theorem charpoly_coeff_vle_one_of_pow_eq_mul
    (ρ : MatrixRepresentation G n) (g x y : rationalPoints G)
    {m : ℕ} (hm : 0 < m) (hpow : g ^ m = x * y) (hxy : Commute x y)
    (C D : Set (rationalPoints G))
    (hC : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact C)
    (hD : letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact D)
    (hx : ∀ k : ℕ, x ^ k ∈ C) (hy : ∀ k : ℕ, y ^ k ∈ D) (i : ℕ) :
    (ρ.rationalMatrix g : Matrix n n F).charpoly.coeff i ≤ᵥ (1 : F) :=
  ρ.charpoly_coeff_vle_one_of_isIntegral_rationalMatrix g
    (ρ.isIntegral_rationalMatrix_of_pow_eq_mul g x y hm hpow hxy C D hC hD hx hy) i

end MatrixRepresentation

end Langlands.GroupScheme
