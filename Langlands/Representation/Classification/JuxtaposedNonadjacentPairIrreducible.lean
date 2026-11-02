import Langlands.Representation.Classification.JuxtaposedSwapFromLibrary
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement

/-!
# Irreducibility of `ν^a A × ν^b A` from Zelevinsky 1.11(a)

For a supercuspidal representation `A` of `GL_r` and natural numbers `a, b` with
`b + 1 < a`, neither of `ν^a A` and `ν^b A` is the twist by `ν` of the other, so
Zelevinsky 1980, Proposition 1.11(a) (`TwoSupercuspidalNonadjacentProductIrreducible`)
makes their product irreducible. This file transports that conclusion from
`Shahidi.twoBlocks r r` to `BlockShape.uniform 2 r`, the form used by the shuffle
isomorphisms.
-/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory

namespace Langlands.Classification.JuxtaposedShuffle

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- If `b ≠ a + 1`, the rank-indexed class of `ν^b A` is not that of `ν (ν^a A)`. -/
theorem segmentSupercuspidalFactor_ne_twist_one {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    {a b : ℕ} (hab : b ≠ a + 1) :
    letI := T.topology
    (⟨r, (segmentSupercuspidalFactor F T A (b : ℝ)).isoClass⟩ :
        Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨r, T.supercuspidalClassRealPowerTwist r 1
        (segmentSupercuspidalFactor F T A (a : ℝ)).isoClass⟩ := by
  letI := T.topology
  intro h
  have hc := eq_of_heq (Sigma.mk.inj h).2
  let β : CuspidalDatum.{uV, uF} T := ⟨r, hr, A.isoClass⟩
  have hβ : β.twist ((b : ℤ) : ℝ) = β.twist (((a + 1 : ℕ) : ℤ) : ℝ) := by
    rw [Int.cast_natCast, Int.cast_natCast,
      show ((a + 1 : ℕ) : ℝ) = 1 + (a : ℝ) by push_cast; ring, ← CuspidalDatum.twist_twist]
    exact congrArg (CuspidalDatum.mk r hr) hc
  have := cuspidalDatum_integralTwist_injective F T β hβ
  omega

/-- **Irreducibility of `ν^a A × ν^b A`.** Assume Zelevinsky 1.11(a). For a
supercuspidal representation `A` of `GL_r` and natural numbers with `b + 1 < a`, the
product `ν^a A × ν^b A` along `BlockShape.uniform 2 r` is irreducible. -/
theorem uniform_two_isIrreducible_of_nonadjacent
    (h11 : TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T)
    {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (a b : ℕ) (hab : b + 1 < a) :
    letI := T.topology
    ((T.normalizedProductInductionFunctor.{uF, uV} (BlockShape.uniform 2 r hr)).obj
      ![T.segmentFactor A.obj (a : ℝ), T.segmentFactor A.obj (b : ℝ)]).IsIrreducible := by
  letI := T.topology
  have h := h11 r r hr hr (segmentSupercuspidalFactor F T A (a : ℝ))
    (segmentSupercuspidalFactor F T A (b : ℝ))
    (segmentSupercuspidalFactor_ne_twist_one T hr A (by omega))
    (segmentSupercuspidalFactor_ne_twist_one T hr A (by omega))
  have heq := productFunctor_obj_eq_of_heq (T := T) (twoBlocks_rankCast_eq_uniform hr) _ _
    (twoBlockFactors_heq hr (T.segmentFactor A.obj (a : ℝ)) (T.segmentFactor A.obj (b : ℝ)))
  rw [← heq, rankCast_isIrreducible_iff]
  exact h

end Langlands.Classification.JuxtaposedShuffle
