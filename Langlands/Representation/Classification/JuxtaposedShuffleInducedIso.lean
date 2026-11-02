import Langlands.Representation.Classification.JuxtaposedShuffleCombinatorics
import Langlands.Representation.Classification.JuxtaposedSwapLifting

/-!
# Products of shuffled twists of one cuspidal representation

For the juxtaposed runs `l, …, l+q-1` and `0, …, l-1`, every shuffle `S` other than
the identity one gives a product `i(⊗ₖ ν^(e_S(k)) A)` along the uniform shape that is
isomorphic to the product for the initial shuffle `{0, …, q-1}`. The input is an
isomorphism `ν^a A × ν^b A ≅ ν^b A × ν^a A` of two-block products whenever
`b + 1 < a`; it is lifted along adjacent swaps (`uniform_adjacentSwap`) and
iterated over the right moves of `shuffle_induction`.
-/

noncomputable section

namespace Langlands.Classification.JuxtaposedShuffle

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- With a natural first run and the second run starting at `0`, shuffle exponents
are natural numbers. -/
theorem exists_natCast_shuffleExponent {m : ℕ} (S : Finset (Fin m)) (a : ℕ) (k : Fin m) :
    ∃ n : ℕ, shuffleExponent S (a : ℝ) 0 k = n := by
  unfold shuffleExponent
  split_ifs
  · exact ⟨a + (S.filter (· < k)).card, by push_cast; ring⟩
  · exact ⟨(Sᶜ.filter (· < k)).card, by simp⟩

/-- A right move `i ∈ S`, `i + 1 ∉ S` whose exponents do not differ by exactly one
exchanges exponents differing by more than one. -/
theorem shuffleExponent_add_one_lt_of_move {q l : ℕ} {S : Finset (Fin (q + l))}
    (hS : S.card = q) {i j : Fin (q + l)} (hi : i ∈ S) (hj : j ∉ S)
    (hgap : shuffleExponent S (l : ℝ) 0 i ≠ shuffleExponent S (l : ℝ) 0 j + 1) :
    shuffleExponent S (l : ℝ) 0 j + 1 < shuffleExponent S (l : ℝ) 0 i := by
  have hlt := shuffleExponent_lt_of_move hS hi hj
  obtain ⟨a, ha⟩ := exists_natCast_shuffleExponent S l i
  obtain ⟨b, hb⟩ := exists_natCast_shuffleExponent S l j
  rw [ha, hb] at hlt hgap ⊢
  have hlt' : b < a := by exact_mod_cast hlt
  have hne : a ≠ b + 1 := fun h => hgap (by rw [h]; push_cast; ring)
  have : b + 1 < a := by omega
  exact_mod_cast this

/-- The shuffle factors `ν^(e_S(k)) A` as a family over `Fin m` of representations
of `GL_r`; it is `shuffleFactors` with its uniform-shape indexing unfolded. -/
abbrev shuffleFamily {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    {m : ℕ} (S : Finset (Fin m)) (a₀ a₁ : ℝ) :
    letI := T.topology
    Fin m → SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier) :=
  fun k => T.segmentFactor A (shuffleExponent S a₀ a₁ k)

theorem shuffleFamily_swapShuffle {r : ℕ}
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    {m : ℕ} (S : Finset (Fin m)) (a₀ a₁ : ℝ) {i j : Fin m} (hij : j.val = i.val + 1)
    (hS : i ∈ S ↔ j ∉ S) :
    shuffleFamily (T := T) A (swapShuffle S i j) a₀ a₁ =
      fun k => shuffleFamily (T := T) A S a₀ a₁ (Equiv.swap i j k) := by
  funext k
  simp only [shuffleFamily, shuffleExponent_swapShuffle S a₀ a₁ hij hS]

/-- Every shuffle of the juxtaposed runs other than the identity one gives a product
isomorphic to the product for the initial shuffle, provided the two orders of
`ν^a A × ν^b A` are isomorphic whenever `b + 1 < a`. -/
theorem shuffleFamily_induced_iso {q l r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hswap : ∀ a b : ℕ, b + 1 < a → letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj ![T.segmentFactor A (a : ℝ), T.segmentFactor A (b : ℝ)] ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj ![T.segmentFactor A (b : ℝ), T.segmentFactor A (a : ℝ)]))
    (S : Finset (Fin (q + l))) (hS : S.card = q) (hid : S ≠ idShuffle q l) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
        (BlockShape.uniform (q + l) r hr)).obj (shuffleFamily (m := q + l) A S (l : ℝ) 0) ≅
      (T.normalizedProductInductionFunctor.{uF, uV} (BlockShape.uniform (q + l) r hr)).obj
        (shuffleFamily (m := q + l) A (initShuffle q l) (l : ℝ) 0)) := by
  let := T.topology
  refine shuffle_induction (fun S => Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
      (BlockShape.uniform (q + l) r hr)).obj (shuffleFamily (m := q + l) A S (l : ℝ) 0) ≅
    (T.normalizedProductInductionFunctor.{uF, uV} (BlockShape.uniform (q + l) r hr)).obj
      (shuffleFamily (m := q + l) A (initShuffle q l) (l : ℝ) 0))) ⟨Iso.refl _⟩ ?_ S hS hid
  rintro S ⟨iv, hiv⟩ ⟨jv, hjv⟩ hS hij hi hj hgap ⟨e⟩
  dsimp only at hij
  subst hij
  have hlt := shuffleExponent_add_one_lt_of_move hS hi hj hgap
  obtain ⟨a, ha⟩ := exists_natCast_shuffleExponent S l ⟨iv, hiv⟩
  obtain ⟨b, hb⟩ := exists_natCast_shuffleExponent S l ⟨iv + 1, hjv⟩
  rw [ha, hb] at hlt
  have h2 := hswap a b (by exact_mod_cast hlt)
  rw [← ha, ← hb] at h2
  obtain ⟨e'⟩ := uniform_adjacentSwap.{uF, uV} hr
    (shuffleFamily (T := T) A S (l : ℝ) 0) iv hjv h2
  rw [shuffleFamily_swapShuffle A S (l : ℝ) 0 rfl ⟨fun _ => hj, fun _ => hi⟩]
  exact ⟨e'.symm ≪≫ e⟩

/-- `shuffleFamily_induced_iso` for the block factors `shuffleFactors` of
`TwoSegmentSocleShuffleJacquet`. -/
theorem shuffle_induced_iso {q l r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hswap : ∀ a b : ℕ, b + 1 < a → letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj ![T.segmentFactor A (a : ℝ), T.segmentFactor A (b : ℝ)] ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj ![T.segmentFactor A (b : ℝ), T.segmentFactor A (a : ℝ)]))
    (S : Finset (Fin (q + l))) (hS : S.card = q) (hid : S ≠ idShuffle q l) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
        (BlockShape.uniform (q + l) r hr)).obj (shuffleFactors F T A (q + l) hr S l 0) ≅
      (T.normalizedProductInductionFunctor.{uF, uV} (BlockShape.uniform (q + l) r hr)).obj
        (shuffleFactors F T A (q + l) hr (initShuffle q l) l 0)) :=
  shuffleFamily_induced_iso hr A hswap S hS hid

end Langlands.Classification.JuxtaposedShuffle
