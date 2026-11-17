import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction
import Langlands.Representation.Archimedean.RealCharacterPairReducible
import Langlands.Representation.Archimedean.RealBlockMultiplierGeneric
import Langlands.Representation.Archimedean.RealAdjacentMultiplierInjectivity

/-!
# Swapping two unlinked real characters

Proof of `Langlands.Archimedean.RealCharacterSwapStatement`: for two real character blocks `a`,
`b` at an arbitrary position `pre`, `post` whose Mœglin data are not linked, there is an
injective intertwiner from the standard module of `pre ++ a :: b :: post` to that of
`pre ++ b :: a :: post`.

The intertwiner is the Frobenius map along the block of the pair with the generic multiplier
`genericMultiplier ν ε`, where `c = b`, `d = a`, `ν = t_d - t_c` and `ε = pairParity c d`
(`exists_injective_swap`). If `ν` avoids `±(ε + 2m + 1)` for every `m : ℕ`, the multiplier has
no zeros and satisfies the recurrence `IsRecurrent (ν + 1) ε` without any condition on `Re ν`
(`RealBlockMultiplier.genericMultiplier_ne_zero_of_ne`,
`RealBlockMultiplier.isRecurrent_genericMultiplier_of_ne`). The recurrence makes the map an
intertwiner, and the Frobenius map in the other direction with the pointwise inverse multiplier
is a left inverse. The remaining work is to translate "not linked" into the two conditions
(`ne_of_not_isLinked`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean.RealCharacterSwap

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator
open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
  RealCharacterPairReducible

set_option backward.isDefEq.respectTransparency false

/-- **Injective generic swap.** Put `ν = t_d - t_c` and `ε = pairParity c d`. If `ν` avoids
`ε + 2m + 1` and `-(ε + 2m + 1)` for every `m : ℕ`, the Frobenius map with the generic
multiplier `genericMultiplier ν ε` is an injective intertwiner from the standard module of
`pre ++ d :: c :: post` to that of `pre ++ c :: d :: post`. No condition on `Re ν` is needed. -/
theorem exists_injective_swap {n : ℕ} {pre post : List RealBlock} {c d : RealCharacterData}
    (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n)
    (hne : ∀ m : ℕ, d.exponent - c.exponent ≠ (pairParity c d : ℂ) + 2 * m + 1)
    (hden : ∀ m : ℕ, d.exponent - c.exponent ≠ -((pairParity c d : ℂ) + 2 * m + 1)) :
    RealInjectiveIntertwinerExists n (pre ++ RealBlock.character d :: RealBlock.character c :: post)
      (pre ++ RealBlock.character c :: RealBlock.character d :: post) := by
  have hε : pairParity c d = 0 ∨ pairParity c d = 1 := pairParity_eq c d
  have hsym : IsSymmetric (pairParity c d) (sigma0 c d)
      (genericMultiplier (d.exponent - c.exponent) (pairParity c d)) :=
    isSymmetric_genericMultiplier _ hε
  have h0 := data_swap hn hsym
  have hB := data_unswap hn hsym
  have hμ0 := genericMultiplier_ne_zero_of_ne hne hden
  have hrec : IsRecurrent (GramFormula.realPositionExponent (pre ++ dc c d ++ post) (realRank pre) -
      GramFormula.realPositionExponent (pre ++ dc c d ++ post) (realRank pre + 1) + 1)
      (pairParity c d) (genericMultiplier (d.exponent - c.exponent) (pairParity c d)) := by
    rw [exponent_swp_zero, exponent_swp_one]
    exact isRecurrent_genericMultiplier_of_ne hε hden
  have hleft : ∀ g, blockFrobMap hB (blockFrobMap h0 g) = g := fun g =>
    blockFrobMap_blockFrobMap_eq h0 hB g fun j _ hj _ _ =>
      absurd (inv_mul_cancel₀ (hμ0 j)) hj
  have hinj : Function.Injective (blockFrobMap h0) := fun f g hfg => by
    rw [← hleft f, ← hleft g, hfg]
  rw [← mid_pair pre post (RealBlock.character d) (RealBlock.character c)]
  exact ⟨blockFrobMap h0, hinj, isRealStandardIntertwiner_blockFrobMap h0 hrec⟩

/-- Two unlinked character data: their exponent difference avoids `±(e + 2m + 1)` for every
integer `e ≥ 0` with `e + ε₁ + ε₂` even. -/
theorem ne_of_not_isLinked {ε₁ ε₂ : Fin 2} {s₁ s₂ : ℂ}
    (h : ¬ (MoeglinDatum.character ε₁ s₁).IsLinked (MoeglinDatum.character ε₂ s₂))
    {e : ℤ} (he0 : 0 ≤ e) (he : Even (e + (ε₁.val : ℤ) + (ε₂.val : ℤ))) (m : ℕ) :
    s₁ - s₂ ≠ (e : ℂ) + 2 * m + 1 ∧ s₁ - s₂ ≠ -((e : ℂ) + 2 * m + 1) := by
  obtain ⟨r, hr⟩ := he
  constructor
  · intro hs
    apply h
    refine ⟨e + 2 * m + 1, by omega, by rw [hs]; push_cast; ring, ⟨r + m, by omega⟩⟩
  · intro hs
    apply h
    refine ⟨-(e + 2 * m + 1), by omega, by rw [hs]; push_cast; ring,
      ⟨(ε₁.val : ℤ) + ε₂.val - r - m - 1, by omega⟩⟩

/-- The parity of a pair is a nonnegative integer `e` with `e + ε_b + ε_a` even. -/
theorem even_pairParity_add (a b : RealCharacterData) :
    0 ≤ pairParity b a ∧ Even (pairParity b a + (a.parity.val : ℤ) + (b.parity.val : ℤ)) := by
  unfold pairParity
  refine ⟨by positivity, ⟨(((b.parity.val + a.parity.val) / 2 +
    (b.parity.val + a.parity.val) % 2 : ℕ) : ℤ), ?_⟩⟩
  omega

/-- **Swapping two unlinked real characters.** -/
theorem realCharacterSwap : RealCharacterSwapStatement := by
  intro n pre post a b hrank _ hunl
  have hl : ¬ (MoeglinDatum.character a.parity a.exponent).IsLinked
      (MoeglinDatum.character b.parity b.exponent) :=
    hunl _ (List.mem_singleton_self _) _ (List.mem_singleton_self _)
  have hrank' : realRank (pre ++ RealBlock.character b :: RealBlock.character a :: post) = n := by
    rw [← hrank]
    exact realRank_perm (List.Perm.append_left pre (List.Perm.swap _ _ _))
  obtain ⟨he0, he⟩ := even_pairParity_add a b
  exact exists_injective_swap (c := b) (d := a) hrank'
    (fun m => (ne_of_not_isLinked hl he0 he m).1)
    (fun m => (ne_of_not_isLinked hl he0 he m).2)

end Langlands.Archimedean.RealCharacterSwap
