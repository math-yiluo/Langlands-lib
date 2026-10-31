import Langlands.Representation.Geometric.RefinedJacquetRealTwist
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.Classification.MaximalConeLifting
import Langlands.Representation.Parabolic.RefinedLeviRealTwistProof

/-!
# Real twists of actual refined Jacquet modules

Specialize the quotient-map character equivalence to the actual refined
radical, the supplied p-adic normalization, and flattened Levi coordinates.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Restrict the coarse real character to the common refined Levi. -/
theorem leviRealPowerCharacter_refinedLevi (t : Fin B.length → ℝ) :
    (T.leviRealPowerCharacter B t).comp (refinedLevi F.Carrier B S).subtype =
      (T.leviRealPowerCharacter (B.flatten S)
        (fun k => t ((B.flattenBlockEquiv S).symm k).1)).comp
          (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom := by
  let := T.topology
  apply MonoidHom.ext
  intro m
  have h := (refinedLeviRealTwist.{uF, 0, 0} p F T n B S
    (Rep.of (Representation.trivial ℂ ((B.flatten S).Levi F.Carrier) ℂ))
    0 t).1 (refinedLeviSection F.Carrier B S m)
  simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    refinedLeviSection_val, refinedLeviProjection_section] using h

/-- The same actual quotient equivalence in flattened product-Levi coordinates. -/
def flattenedNormalizedRefinedJacquetRealTwistEquiv
    (t : Fin B.length → ℝ) (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation.Equiv
      ((T.normalizedRefinedJacquet B S (T.leviRealPowerTwist B t ρ)).comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
      (T.leviRealPowerTwist (B.flatten S)
        (fun k => t ((B.flattenBlockEquiv S).symm k).1)
        ((T.normalizedRefinedJacquet B S ρ).comp
          (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) :=
  Representation.Equiv.mk
    (T.normalizedRefinedJacquetRealTwistEquiv B S ρ t).toLinearEquiv fun m => by
      have h := (T.normalizedRefinedJacquetRealTwistEquiv B S ρ t).isIntertwining'
        (flattenedLeviEquiv F.Carrier B S m)
      change _ = ((T.leviRealPowerCharacter (B.flatten S)
        (fun k => t ((B.flattenBlockEquiv S).symm k).1) m : ℂ) •
          T.normalizedRefinedJacquet B S ρ (flattenedLeviEquiv F.Carrier B S m)).comp _
      change _ = ((T.leviRealPowerCharacter B t
        (flattenedLeviEquiv F.Carrier B S m).val : ℂ) •
          T.normalizedRefinedJacquet B S ρ (flattenedLeviEquiv F.Carrier B S m)).comp _ at h
      rw [T.leviRealPowerCharacter_flatten B S t m] at h
      exact h

@[simp]
theorem flattenedNormalizedRefinedJacquetRealTwistEquiv_mk
    (t : Fin B.length → ℝ) (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    T.flattenedNormalizedRefinedJacquetRealTwistEquiv B S t ρ
        (refinedJacquetMk B S (T.leviRealPowerTwist B t ρ) v) =
      refinedJacquetMk B S ρ v := rfl

@[simp]
theorem flattenedNormalizedRefinedJacquetRealTwistEquiv_symm_mk
    (t : Fin B.length → ℝ) (ρ : Representation ℂ (B.Levi F.Carrier) V) (v : V) :
    (T.flattenedNormalizedRefinedJacquetRealTwistEquiv B S t ρ).symm
        (refinedJacquetMk B S ρ v) =
      refinedJacquetMk B S (T.leviRealPowerTwist B t ρ) v := rfl

/-- The quotient equivalence commutes with every descended ambient intertwiner. -/
theorem normalizedRefinedJacquetRealTwistEquiv_naturality
    (t : Fin B.length → ℝ) {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {σ : Representation ℂ (B.Levi F.Carrier) W} (f : ρ.IntertwiningMap σ) :
    (twistIntertwining ((T.leviRealPowerCharacter B t).comp
        (refinedLevi F.Carrier B S).subtype)
      (T.normalizedRefinedJacquetMap B S f)).comp
        (T.normalizedRefinedJacquetRealTwistEquiv B S ρ t).toIntertwiningMap =
      (T.normalizedRefinedJacquetRealTwistEquiv B S σ t).toIntertwiningMap.comp
        (T.normalizedRefinedJacquetMap B S
          (twistIntertwining (T.leviRealPowerCharacter B t) f)) :=
  Jacquet.normalizedActionOfModulusTwistEquiv_naturality
    (refinedUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
    (refinedLevi_le_normalizer B S) (T.leviRealPowerCharacter B t)
    (T.refinedUnipotent_le_ker_leviRealPowerCharacter B S t)
    (T.refinedLeviModulus B S) f

end Langlands.PadicField.TopologicalData
