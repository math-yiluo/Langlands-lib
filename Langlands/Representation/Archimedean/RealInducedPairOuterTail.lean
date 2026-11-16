import Langlands.Representation.Archimedean.RealInducedPairFrobenius
import Langlands.Representation.Archimedean.RealInducedPairIntertwiner
import Langlands.Representation.Archimedean.RealInducedPairQuotientPresentation
import Langlands.Representation.Archimedean.RealInducedPairLinkedReplacement

/-! # The outer tail at a linked pair of real induction blocks -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairOuterTail

open RealBlockFrobeniusMap RealBlockMultiplier RealBlockJacquet RealBlockPosition
open RealCharacterPair RealCharacterPairReducible RealStandardFiltration
open RealInducedPairFrobenius RealInducedPairLinkedReplacement

section General

variable {n p : ℕ} {ds es fs : List RealBlock}

theorem ofEqMap_eq_zero_iff (h : KF n ds = KF n es) (f : KF n ds) :
    ofEqMap h f = 0 ↔ f = 0 :=
  (LinearEquiv.ofEq _ _ h).map_eq_zero_iff

theorem ker_ofEqMap_comp (h : KF n es = KF n fs) (T : KF n ds →ₗ[ℂ] KF n es) :
    LinearMap.ker ((ofEqMap h).comp T) = LinearMap.ker T := by
  exact LinearMap.ker_comp_of_ker_eq_bot T
    (LinearMap.ker_eq_bot_of_injective (LinearEquiv.ofEq _ _ h).injective)

/-- The tail kernel is detected by the surviving Fourier modes of its source. -/
theorem tail_eq_zero_iff {ℓ : ℕ} {ε : ℤ} {τ : ℂ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) (hτ : τ ^ 2 = 1)
    (hD : IsBlockFrobData n ds es p ε τ (tailMultiplier ℓ ε τ)) (f : KF n ds) :
    blockFrobMap hD f = 0 ↔
      ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ, (ℓ : ℤ) ≤ |j| →
        blockFourierCoefficient n p j (f : Langlands.GeneralLinear n ℝ → ℂ) g = 0 := by
  constructor
  · intro hf g hg j hj
    have hc := blockFourierCoefficient_blockFrobMap hD f hg j
    rw [hf, ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at hc
    by_cases hjp : Even (j - ε)
    · have hj' : (ℓ : ℤ) < |j| := by
        by_contra hnot
        have heq : |j| = (ℓ : ℤ) := le_antisymm (not_lt.mp hnot) hj
        exact (not_lt_of_ge heq.symm.le)
          (abs_lt_of_parity hpar hjp heq.le)
      have hm := (tailMultiplier_ne_zero_iff hℓ hε hpar hτ hjp).mpr hj'
      exact (mul_eq_zero.mp hc.symm).resolve_left hm
    · exact blockFourierCoefficient_eq_zero_of_not_even hD.lt hD.par f hjp g
  · intro hf
    refine eq_of_blockFourierCoefficient_eq hD.lt fun j g hg => ?_
    rw [blockFourierCoefficient_blockFrobMap hD _ hg]
    change _ = blockFourierCoefficient n p j (0 : Langlands.GeneralLinear n ℝ → ℂ) g
    rw [blockFourierCoefficient_zero]
    by_cases hj : (ℓ : ℤ) ≤ |j|
    · rw [hf g hg j hj, mul_zero]
    · by_cases hjp : Even (j - ε)
      · have hm : tailMultiplier ℓ ε τ j = 0 := by
          by_contra hne
          have hj' := (tailMultiplier_ne_zero_iff hℓ hε hpar hτ hjp).mp hne
          omega
        rw [hm, zero_mul]
      · rw [blockFourierCoefficient_eq_zero_of_not_even hD.lt hD.par f hjp g, mul_zero]

end General

variable (d e : ComplexCharacterData) (k : ℕ)

/-- The remaining endpoint characters surrounding the actual outer replacement block. -/
abbrev outerList : List RealBlock :=
  [.character (first d), .induced (outerData d e k), .character (second e)]

theorem outerWeight_pos : 0 < outerWeight d e k := by
  unfold outerWeight
  omega

/-- The outer replacement is precisely the induction of the two central characters
of the descending four-character presentation. -/
theorem pairInduced_eq_outer :
    pairInduced (second d) (first e) (outerWeight d e k) = outerData d e k := by
  unfold pairInduced outerData
  congr 1
  change ((d.exponent - (d.weight.natAbs : ℂ) / 2) +
    (e.exponent + (e.weight.natAbs : ℂ) / 2)) / 2 = _
  unfold outerExponent
  ring

variable {d e k}

theorem outer_gap (h : IsLinkedAt d e k) :
    (first e).exponent - (second d).exponent = (outerWeight d e k : ℂ) := by
  obtain ⟨h1, h2, -, -⟩ := endpoint_equalities h
  change (e.exponent + (e.weight.natAbs : ℂ) / 2) -
    (d.exponent - (d.weight.natAbs : ℂ) / 2) = _
  linear_combination -h1 + h2

/-- This is exactly the resonance parity needed for the canonical central characters. -/
theorem outer_parity
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))) :
    Even ((outerWeight d e k : ℤ) - 1 - pairParity (second d) (first e)) := by
  unfold pairParity
  change Even ((outerWeight d e k : ℤ) - 1 -
    (((0 + (e.weight.natAbs + 1) % 2) % 2 : ℕ) : ℤ))
  rw [Int.even_iff] at hp ⊢
  omega

variable (h : IsLinkedAt d e k)
  (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))

/-- Central tail on the full four-character source. -/
abbrev dataTail :=
  data_D (n := 4) (pre := [.character (first d)]) (post := [.character (second e)])
    rfl (outerWeight_pos d e k) (outer_parity hp) (outer_gap h)

abbrev dataSection :=
  data_q1 (n := 4) (pre := [.character (first d)]) (post := [.character (second e)])
    rfl (outerWeight_pos d e k) (outer_parity hp) (outer_gap h)

abbrev dataBinomial :=
  data_q0 (n := 4) (ℓ := outerWeight d e k)
    (pre := [.character (first d)]) (post := [.character (second e)])
    (c := second d) (d := first e) rfl

abbrev dataInverseBinomial :=
  data_B (n := 4) (ℓ := outerWeight d e k)
    (pre := [.character (first d)]) (post := [.character (second e)])
    (c := second d) (d := first e) rfl

/-- The actual mixed target before identifying its induction datum with `outerData`. -/
abbrev rawOuterList : List RealBlock :=
  [.character (first d),
    .induced (pairInduced (second d) (first e) (outerWeight d e k)),
    .character (second e)]

theorem rawOuterList_eq : rawOuterList (d := d) (e := e) (k := k) = outerList d e k := by
  simp only [rawOuterList, outerList, pairInduced_eq_outer]

/-- The outer tail on the actual source with both original Fourier windows retained. -/
def outerMap : KF 4 (src d e) →ₗ[ℂ] KF 4 (outerList d e k) :=
  (ofEqMap (congrArg (KF 4) (rawOuterList_eq (d := d) (e := e) (k := k)))).comp
    ((blockFrobMap (dataTail h hp)).comp (Submodule.inclusion (src_le_l0 d e)))

/-- Exact compact and Lie equivariance, with no landing premise. -/
theorem outerMap_exact :
    IsRealIntertwinerModulo 4 (src d e) (outerList d e k) ⊥ (outerMap h hp) := by
  apply modulo_comp_bot (modulo_ofEqMap _) (modulo_comp_bot ?_ (RealInducedPairFrobenius.inclusion_intertwiner d e))
  exact RealInducedPairQuotientPresentation.tail_exact
    (n := 4) (pre := [.character (first d)]) (post := [.character (second e)])
    rfl (outerWeight_pos d e k) (outer_parity hp) (outer_gap h)

/-- The full principal-series tail has exactly the explicit central binomial image
as its kernel. -/
theorem full_kernel :
    LinearMap.ker (blockFrobMap (dataTail h hp)) =
      LinearMap.range (blockFrobMap (dataBinomial (d := d) (e := e) (k := k))) :=
  RealInducedPairQuotientPresentation.ker_tail_eq_range
    (outerWeight_pos d e k) (pairParity_eq _ _) (outer_parity hp)
    (neg_one_pow_sq_fin _) dataBinomial dataInverseBinomial (dataTail h hp)

/-- The restricted kernel is the intersection of the explicit binomial image
with the actual two-induced-block source, expressed as a preimage. -/
theorem kernel :
    LinearMap.ker (outerMap h hp) =
      (LinearMap.range (blockFrobMap (dataBinomial (d := d) (e := e) (k := k)))).comap
        (Submodule.inclusion (src_le_l0 d e)) := by
  unfold outerMap
  rw [ker_ofEqMap_comp, LinearMap.ker_comp, full_kernel h hp]

/-- No surjectivity of the restricted map is used here: the full tail has an
explicit inverse-tail section. -/
theorem full_tail_section (f : KF 4 (rawOuterList (d := d) (e := e) (k := k))) :
    blockFrobMap (dataTail h hp) (blockFrobMap (dataSection h hp) f) = f :=
  RealCharacterInducedPushforward.tail_inv
    (outerWeight_pos d e k) (pairParity_eq _ _) (outer_parity hp)
    (neg_one_pow_sq_fin _) (dataTail h hp) (dataSection h hp) rfl
    (by rw [pairInduced_weight, abs_of_nonneg (Int.natCast_nonneg _)]) f

/-- The kernel condition in the actual source is precisely central low-mode support. -/
theorem outerMap_eq_zero_iff (f : KF 4 (src d e)) :
    outerMap h hp f = 0 ↔
      ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (outerWeight d e k : ℤ) ≤ |j| →
        blockFourierCoefficient 4 1 j (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  change ofEqMap
    (congrArg (KF 4) (rawOuterList_eq (d := d) (e := e) (k := k)))
      (blockFrobMap (dataTail h hp) (Submodule.inclusion (src_le_l0 d e) f)) = 0 ↔ _
  rw [ofEqMap_eq_zero_iff]
  exact tail_eq_zero_iff (outerWeight_pos d e k) (pairParity_eq _ _) (outer_parity hp)
    (neg_one_pow_sq_fin _) (dataTail h hp) (Submodule.inclusion (src_le_l0 d e) f)

end RealInducedPairOuterTail

open RealInducedPairOuterTail RealInducedPairLinkedReplacement RealInducedPairFrobenius
  RealBlockFrobeniusMap in
/-- The actual linked outer tail is exact, with the explicit restricted binomial kernel. -/
def RealInducedPairOuterTailStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))),
    IsRealIntertwinerModulo 4 (src d e) (outerList d e k) ⊥ (outerMap h hp) ∧
      LinearMap.ker (outerMap h hp) =
        (LinearMap.range (blockFrobMap
          (dataBinomial (d := d) (e := e) (k := k)))).comap
            (Submodule.inclusion (src_le_l0 d e))

open RealInducedPairOuterTail in
theorem realInducedPairOuterTail : RealInducedPairOuterTailStatement := by
  intro d e k h hp
  exact ⟨outerMap_exact h hp, kernel h hp⟩

end Langlands.Archimedean
