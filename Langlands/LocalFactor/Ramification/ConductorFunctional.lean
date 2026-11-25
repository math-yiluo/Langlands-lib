import Langlands.LocalFactor.SpectralConductorFunctional
import Langlands.LocalFactor.Ramification.Herbrand.QuotientProof
import Mathlib.RepresentationTheory.Character

/-!
# The Artin conductor as a linear functional of the character

For a finite group `G` acting faithfully on a Noetherian local ring `R`, with lower groups
`G_i = lowerGroup R G i`, the depth `i_G(g)` of `g ≠ 1` is the number of `i` with `g ∈ G_i`
(`lowerDepth`). The functional `f ↦ |G_0|⁻¹ Σ_g i_G(g) (f 1 − f g)` on complex functions on
`G` (`artinFunctional`) takes the value `a(ρ)` on the character of every finite-dimensional
complex representation `ρ` (`artinFunctional_character`). Hence the Artin conductor depends only
on the character, and it is additive on virtual characters.

This file also gives non-negativity of the Artin and Swan expressions and, for the p-adic
conductors, the decomposition into the tame part and the Swan part.
-/

noncomputable section

namespace Langlands.Ramification

open Module
open scoped BigOperators

universe uR uG uk uV uW uK uL

section Depth

variable (R : Type uR) (G : Type uG) [CommRing R] [IsLocalRing R] [Group G]
  [MulSemiringAction G R]

/-- The number of `i` with `g ∈ G_i`: Serre's `i_G(g)` for `g ≠ 1`, and `0` at `g = 1`
(where the set of indices is infinite). -/
def lowerDepth (g : G) : ℕ :=
  Nat.card {i : ℕ // g ∈ lowerGroup R G i}

variable {R G}

@[simp]
theorem lowerDepth_one : lowerDepth R G 1 = 0 := by
  have : Infinite {i : ℕ // (1 : G) ∈ lowerGroup R G i} :=
    Infinite.of_injective (fun i => ⟨i, (lowerGroup R G i).one_mem⟩)
      (fun _ _ h => congrArg Subtype.val h)
  exact Nat.card_eq_zero_of_infinite

/-- For `g ≠ 1` and a bound `b` past which the lower groups vanish, the truncated count
`SpectralConductor.lowerCount R G b g` is the depth of `g`. -/
theorem lowerCount_eq_lowerDepth {b : ℕ} (hb : ∀ i ≥ b, lowerGroup R G i = ⊥) {g : G}
    (hg : g ≠ 1) : LocalFactor.SpectralConductor.lowerCount R G b g = lowerDepth R G g := by
  classical
  unfold LocalFactor.SpectralConductor.lowerCount lowerDepth
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨And.right, fun hi => ⟨?_, hi⟩⟩
  by_contra hlt
  rw [hb i (Nat.le_of_not_gt hlt)] at hi
  exact hg (Subgroup.mem_bot.mp hi)

end Depth

section Functional

variable (R : Type uR) (G : Type uG) [CommRing R] [IsLocalRing R] [Group G]
  [MulSemiringAction G R] [Fintype G]

/-- The Artin functional `f ↦ |G_0|⁻¹ Σ_g i_G(g) (f 1 − f g)` on complex functions on `G`. -/
def artinFunctional : (G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ *
    ∑ g : G, (lowerDepth R G g : ℂ) * (f 1 - f g)
  map_add' f f' := by
    simp only [Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun g _ => by ring
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring

theorem artinFunctional_apply (f : G → ℂ) :
    artinFunctional R G f = (Nat.card (lowerGroup R G 0) : ℂ)⁻¹ *
      ∑ g : G, (lowerDepth R G g : ℂ) * (f 1 - f g) := rfl

/-- The functional vanishes on constant functions. -/
@[simp]
theorem artinFunctional_const (c : ℂ) : artinFunctional R G (fun _ => c) = 0 := by
  simp [artinFunctional_apply]

/-- **The Artin conductor as a function of the character.** For a finite group acting
faithfully on a Noetherian local ring and a finite-dimensional complex representation `ρ`,
the Artin functional of the character of `ρ` is the Artin expression of `ρ`. -/
theorem artinFunctional_character [IsNoetherianRing R] [FaithfulSMul G R]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    artinFunctional R G ρ.character = ((artinConductor R G ρ : ℚ) : ℂ) := by
  classical
  obtain ⟨b, hb⟩ := exists_lowerGroup_eq_bot R G
  rw [LocalFactor.SpectralConductor.artinConductor_eq_classSum R ρ b hb, artinFunctional_apply,
    Representation.char_one]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : g = 1
  · subst hg
    simp [Representation.character]
  · rw [lowerCount_eq_lowerDepth hb hg]
    rfl

end Functional

section Nonneg

variable (R : Type uR) (G : Type uG) [CommRing R] [IsLocalRing R] [Group G]
  [MulSemiringAction G R] [IsNoetherianRing R] [FaithfulSMul G R] [Finite G]
  {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The Artin expression is non-negative. -/
theorem artinConductor_nonneg (ρ : Representation k G V) : 0 ≤ artinConductor R G ρ :=
  Finset.sum_nonneg fun i _ => conductorTerm_nonneg R G ρ i

/-- The Swan expression is non-negative. -/
theorem swanConductor_nonneg (ρ : Representation k G V) : 0 ≤ swanConductor R G ρ :=
  Finset.sum_nonneg fun i _ => conductorTerm_nonneg R G ρ (i + 1)

end Nonneg

namespace Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

section General

variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- The Artin expression of a representation of a finite p-adic Galois group is
non-negative. -/
theorem artinConductor_nonneg (ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V) :
    0 ≤ artinConductor T K ρ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  exact Ramification.artinConductor_nonneg T.Integers _ ρ

/-- The Swan expression of a representation of a finite p-adic Galois group is
non-negative. -/
theorem swanConductor_nonneg (ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V) :
    0 ≤ swanConductor T K ρ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  exact Ramification.swanConductor_nonneg T.Integers _ ρ

/-- The Artin expression is the codimension of the inertia invariants plus the Swan
expression. -/
theorem artinConductor_eq_tame_add_swan
    (ρ : Representation k (F.Carrier ≃ₐ[K] F.Carrier) V) :
    artinConductor T K ρ =
      (fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K) : ℚ) +
        swanConductor T K ρ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  have h := Ramification.artinConductor_eq_tame_add_swan T.Integers
    (F.Carrier ≃ₐ[K] F.Carrier) ρ
  have h0 : lowerGroup T.Integers (F.Carrier ≃ₐ[K] F.Carrier) 0 = inertia T K :=
    lowerRamificationGroup_zero T K
  rw [h0] at h
  exact h

end General

section Complex

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- **The p-adic Artin conductor depends only on the character.** -/
theorem artinConductor_eq_of_character_eq
    {ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V}
    {σ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) W}
    (h : ρ.character = σ.character) : artinConductor T K ρ = artinConductor T K σ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  have hρ := artinFunctional_character T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ρ
  have hσ := artinFunctional_character T.Integers (F.Carrier ≃ₐ[K] F.Carrier) σ
  rw [h, hσ] at hρ
  change Ramification.artinConductor T.Integers _ ρ =
    Ramification.artinConductor T.Integers _ σ
  exact_mod_cast hρ.symm

end Complex

end Padic

end Langlands.Ramification
