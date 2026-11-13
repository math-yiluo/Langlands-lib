import Langlands.LocalFactor.Ramification.Galois
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Trace

/-!
# The class-function form of the Artin conductor

For a finite group with a family of subgroups `G_i`, the weighted sum
`Σ_{i<b} (|G_i| / |G_0|) codim V^{G_i}` equals
`|G_0|⁻¹ Σ_g m(g) (dim V - tr ρ(g))`, where `m(g)` counts the indices `i < b`
with `g ∈ G_i`. The proof is the averaging formula
`dim V^H = |H|⁻¹ Σ_{h ∈ H} tr ρ(h)`. This is Serre, *Local Fields*, VI §2,
Proposition 2, read backwards.
-/

noncomputable section

namespace Langlands.LocalFactor.SpectralConductor

open Module Ramification
open scoped BigOperators

universe uG uV

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- The averaging formula for the dimension of the fixed vectors of a finite subgroup. -/
theorem finrank_fixedVectors [Fintype G] [DecidableEq G] (ρ : Representation ℂ G V)
    (H : Subgroup G) [DecidablePred (· ∈ H)] :
    (finrank ℂ (fixedVectors ρ H) : ℂ) =
      (Fintype.card H : ℂ)⁻¹ * ∑ g : G, if g ∈ H then LinearMap.trace ℂ V (ρ g) else 0 := by
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let : Invertible (Fintype.card H : ℂ) := invertibleOfNonzero hcard
  rw [fixedVectors, ← (Representation.isProj_averageMap (ρ.comp H.subtype)).trace]
  have h2 : ∑ h : H, LinearMap.trace ℂ V (ρ h) =
      ∑ g : G, if g ∈ H then LinearMap.trace ℂ V (ρ g) else 0 := by
    rw [← Finset.sum_filter]
    refine (Finset.sum_subtype (Finset.univ.filter (fun g => g ∈ H)) (fun x => ?_)
      (fun g => LinearMap.trace ℂ V (ρ g))).symm
    simp
  rw [← h2]
  simp [Representation.averageMap, GroupAlgebra.average, map_sum]

/-- One weighted codimension term as an average of `dim V - tr ρ(g)` over `H`. -/
theorem weightedCodimension_eq [Fintype G] [DecidableEq G] (ρ : Representation ℂ G V)
    (H G₀ : Subgroup G) [DecidablePred (· ∈ H)] :
    ((((Nat.card H : ℚ) / Nat.card G₀ * fixedCodimension G ρ H : ℚ)) : ℂ) =
      (Nat.card G₀ : ℂ)⁻¹ * ∑ g : G,
        if g ∈ H then ((finrank ℂ V : ℂ) - LinearMap.trace ℂ V (ρ g)) else 0 := by
  have hfix := finrank_fixedVectors ρ H
  have hle : finrank ℂ (fixedVectors ρ H) ≤ finrank ℂ V := Submodule.finrank_le _
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ g : G, if g ∈ H then ((finrank ℂ V : ℂ) - LinearMap.trace ℂ V (ρ g)) else 0) =
      (Fintype.card H : ℂ) * finrank ℂ V -
        ∑ g : G, if g ∈ H then LinearMap.trace ℂ V (ρ g) else 0 := by
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
    congr 2
    rw [← Fintype.card_subtype]
  rw [hsum, fixedCodimension, Nat.card_eq_fintype_card (α := H)]
  push_cast [Nat.cast_sub hle]
  rw [hfix]
  field_simp

open Classical in
/-- The number of lower groups `G_i`, `i < b`, containing `g`. -/
def lowerCount (R : Type*) (G : Type*) [CommRing R] [IsLocalRing R] [Group G]
    [MulSemiringAction G R] (b : ℕ) (g : G) : ℕ :=
  ((Finset.range b).filter (fun i => g ∈ lowerGroup R G i)).card

/-- The class-function form of the Artin conductor of a finite group acting on a
local ring: `a(ρ) = |G_0|⁻¹ Σ_g m(g) (dim V - tr ρ(g))`. -/
theorem artinConductor_eq_classSum (R : Type*) [CommRing R] [IsLocalRing R]
    [MulSemiringAction G R] [IsNoetherianRing R] [FaithfulSMul G R] [Fintype G]
    [DecidableEq G] (ρ : Representation ℂ G V) (b : ℕ)
    (hb : ∀ i ≥ b, lowerGroup R G i = ⊥) :
    ((Ramification.artinConductor R G ρ : ℚ) : ℂ) =
      (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ * ∑ g : G,
        (lowerCount R G b g : ℂ) * ((finrank ℂ V : ℂ) - LinearMap.trace ℂ V (ρ g)) := by
  classical
  rw [Ramification.artinConductor_eq_sum_range R G ρ b hb, Rat.cast_sum]
  have hterm (i : ℕ) : ((Ramification.conductorTerm R G ρ i : ℚ) : ℂ) =
      (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ * ∑ g : G,
        if g ∈ lowerGroup R G i then
          ((finrank ℂ V : ℂ) - LinearMap.trace ℂ V (ρ g)) else 0 :=
    weightedCodimension_eq ρ (lowerGroup R G i) (lowerGroup R G 0)
  simp only [hterm, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [lowerCount, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Langlands.LocalFactor.SpectralConductor
