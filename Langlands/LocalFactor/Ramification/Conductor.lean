import Langlands.LocalFactor.Ramification.Filtration
import Langlands.Representation.Smooth.FixedVectors.Definitions
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite ramification conductor expressions

These are the rational weighted fixed-space codimension sums attached to the
actual maximal-ideal congruence filtration. Finiteness of their support is
proved from the ring action, rather than supplied as a hypothesis or cutoff.
-/

noncomputable section

namespace Langlands.Ramification

open Module
open scoped BigOperators

universe uR uG uk uV uW

variable (R : Type uR) (G : Type uG) [CommRing R] [IsLocalRing R]
  [Group G] [MulSemiringAction G R]
  {k : Type uk} [Field k]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]

/-- Codimension of the actual subgroup-fixed subspace. -/
def fixedCodimension [FiniteDimensional k V]
    (ρ : Representation k G V) (H : Subgroup G) : ℕ :=
  finrank k V - finrank k (fixedVectors ρ H)

private theorem fixedVectors_bot (ρ : Representation k G V) :
    fixedVectors ρ (⊥ : Subgroup G) = ⊤ := by
  ext v
  change (∀ g : (⊥ : Subgroup G), ρ g v = v) ↔ True
  constructor
  · intro _
    trivial
  · intro _ g
    have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.property
    simp [hg]

variable [FiniteDimensional k V] [FiniteDimensional k W]

@[simp] theorem fixedCodimension_bot (ρ : Representation k G V) :
    fixedCodimension G ρ ⊥ = 0 := by
  rw [fixedCodimension, fixedVectors_bot G ρ, finrank_top, Nat.sub_self]

theorem fixedCodimension_equiv {ρ : Representation k G V}
    {σ : Representation k G W} (e : ρ.Equiv σ) (H : Subgroup G) :
    fixedCodimension G ρ H = fixedCodimension G σ H := by
  unfold fixedCodimension
  rw [e.toLinearEquiv.finrank_eq, (fixedVectorsEquiv e H).finrank_eq]

/-- The `i`th Artin summand, with the inertia denominator `|G₀|`. -/
def conductorTerm (ρ : Representation k G V) (i : ℕ) : ℚ :=
  (Nat.card (lowerGroup R G i) : ℚ) / Nat.card (lowerGroup R G 0) *
    fixedCodimension G ρ (lowerGroup R G i)

theorem conductorTerm_eq_zero {ρ : Representation k G V} {i : ℕ}
    (hi : lowerGroup R G i = ⊥) : conductorTerm R G ρ i = 0 := by
  simp [conductorTerm, hi]

theorem conductorTerm_nonneg (ρ : Representation k G V) (i : ℕ) :
    0 ≤ conductorTerm R G ρ i :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem conductorTerm_equiv {ρ : Representation k G V}
    {σ : Representation k G W} (e : ρ.Equiv σ) (i : ℕ) :
    conductorTerm R G ρ i = conductorTerm R G σ i := by
  simp only [conductorTerm, fixedCodimension_equiv G e]

section FiniteAction

variable [IsNoetherianRing R] [FaithfulSMul G R] [Finite G]

theorem conductorTerm_hasFiniteSupport (ρ : Representation k G V) :
    (conductorTerm R G ρ).HasFiniteSupport := by
  obtain ⟨b, hb⟩ := exists_lowerGroup_eq_bot R G
  apply (Finset.range b).finite_toSet.subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hi (conductorTerm_eq_zero R G (hb i (Nat.le_of_not_gt h)))

theorem conductorTail_hasFiniteSupport (ρ : Representation k G V) :
    (fun i => conductorTerm R G ρ (i + 1)).HasFiniteSupport := by
  obtain ⟨b, hb⟩ := exists_lowerGroup_eq_bot R G
  apply (Finset.range b).finite_toSet.subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hi (conductorTerm_eq_zero R G
    (hb (i + 1) ((Nat.le_of_not_gt h).trans (Nat.le_succ i))))

/-- The Artin expression is an actual finite sum, including the inertia term.
Its integrality is a separate theorem, not built into this definition. -/
def artinConductor (ρ : Representation k G V) : ℚ :=
  ∑ i ∈ (conductorTerm_hasFiniteSupport R G ρ).toFinset, conductorTerm R G ρ i

/-- The Swan expression is the actual finite positive-index tail.
The denominator is still `|G₀|`, not `|G₁|`. -/
def swanConductor (ρ : Representation k G V) : ℚ :=
  ∑ i ∈ (conductorTail_hasFiniteSupport R G ρ).toFinset,
    conductorTerm R G ρ (i + 1)

theorem artinConductor_eq_finsum (ρ : Representation k G V) :
    artinConductor R G ρ = ∑ᶠ i, conductorTerm R G ρ i :=
  (finsum_eq_sum _ (conductorTerm_hasFiniteSupport R G ρ)).symm

theorem swanConductor_eq_finsum (ρ : Representation k G V) :
    swanConductor R G ρ = ∑ᶠ i, conductorTerm R G ρ (i + 1) :=
  (finsum_eq_sum _ (conductorTail_hasFiniteSupport R G ρ)).symm

/-- Any proved termination bound computes the same Artin expression. -/
theorem artinConductor_eq_sum_range (ρ : Representation k G V) (b : ℕ)
    (hb : ∀ i ≥ b, lowerGroup R G i = ⊥) :
    artinConductor R G ρ = ∑ i ∈ Finset.range b, conductorTerm R G ρ i := by
  rw [artinConductor_eq_finsum]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hi (conductorTerm_eq_zero R G (hb i (Nat.le_of_not_gt h)))

/-- Any proved termination bound computes the same Swan expression. -/
theorem swanConductor_eq_sum_range (ρ : Representation k G V) (b : ℕ)
    (hb : ∀ i ≥ b, lowerGroup R G i = ⊥) :
    swanConductor R G ρ = ∑ i ∈ Finset.range b, conductorTerm R G ρ (i + 1) := by
  rw [swanConductor_eq_finsum]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hi (conductorTerm_eq_zero R G
    (hb (i + 1) ((Nat.le_of_not_gt h).trans (Nat.le_succ i))))

omit [IsNoetherianRing R] [FaithfulSMul G R] in
theorem conductorTerm_zero (ρ : Representation k G V) :
    conductorTerm R G ρ 0 = fixedCodimension G ρ (lowerGroup R G 0) := by
  have h : (Nat.card (lowerGroup R G 0) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := lowerGroup R G 0)).ne'
  simp [conductorTerm, h]

/-- The tame term is exactly the codimension of inertia invariants. -/
theorem artinConductor_eq_tame_add_swan (ρ : Representation k G V) :
    artinConductor R G ρ =
      (fixedCodimension G ρ (lowerGroup R G 0) : ℚ) + swanConductor R G ρ := by
  obtain ⟨b, hb⟩ := exists_lowerGroup_eq_bot R G
  rw [artinConductor_eq_sum_range R G ρ (b + 1)
    (fun i hi => hb i ((Nat.le_succ b).trans hi)),
    swanConductor_eq_sum_range R G ρ b hb, Finset.sum_range_succ', conductorTerm_zero]
  exact add_comm _ _

theorem artinConductor_equiv {ρ : Representation k G V}
    {σ : Representation k G W} (e : ρ.Equiv σ) :
    artinConductor R G ρ = artinConductor R G σ := by
  simp only [artinConductor_eq_finsum, conductorTerm_equiv R G e]

theorem swanConductor_equiv {ρ : Representation k G V}
    {σ : Representation k G W} (e : ρ.Equiv σ) :
    swanConductor R G ρ = swanConductor R G σ := by
  simp only [swanConductor_eq_finsum, conductorTerm_equiv R G e]

end FiniteAction

end Langlands.Ramification
