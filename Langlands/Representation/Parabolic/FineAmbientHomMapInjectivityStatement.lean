import Langlands.Representation.Parabolic.FineAmbientHomMap

/-! # Injectivity of the specified fine-to-ambient Hom map

This module states the internal algebraic injectivity target for the actual
public map attached to a specified surjective outer intertwiner. It supplies
no proof.
-/

noncomputable section

namespace Langlands.RelativeHomComparison

open GeneralLinear Geometric RelativeJacquetMultiplicity Parabolic

universe uF uV uW uZ

/-- The actual fine-to-ambient Hom map is injective for an irreducible coarse
target and a specified surjective outer intertwiner with nontrivial target. -/
def FineAmbientHomMapInjectivityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
      (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)
      (hω : IsSmooth ω.ρ) (π : Rep.{uW} ℂ (B.Levi F.Carrier)),
      Representation.IsIrreducible π.ρ →
      ∀ J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier), Nontrivial J.V →
      ∀ q : (CuspidalJacquetMultiplicity.induced T B
        (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ,
        Function.Surjective q →
        Function.Injective (fineAmbientHomMap T B S ω v₀ t hω π J q)

end Langlands.RelativeHomComparison
