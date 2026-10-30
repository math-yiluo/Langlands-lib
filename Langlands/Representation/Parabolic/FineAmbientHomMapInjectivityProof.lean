import Langlands.Representation.Parabolic.FineAmbientHomMapInjectivityStatement
import Langlands.Representation.Parabolic.InductionFactorMatchingProof

/-! # Injectivity of the specified fine-to-ambient Hom map

This module proves `FineAmbientHomMapInjectivityStatement`: the actual public
`fineAmbientHomMap` is injective on the entire space of inner intertwiners when
the coarse target is irreducible, the ambient carrier is nontrivial and the
specified outer intertwiner is surjective.
-/

noncomputable section

namespace Langlands.RelativeHomComparison

open GeneralLinear Geometric RelativeJacquetMultiplicity Parabolic

universe uF uV uW uZ

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
  (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)

/-- For a surjective specified outer intertwiner, the actual value of the
fine-to-ambient Hom map at a surjective inner intertwiner is surjective. -/
theorem fineAmbientHomMap_surjective
    (hω : letI := T.topology; IsSmooth ω.ρ)
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier))
    (q : (CuspidalJacquetMultiplicity.induced T B
      (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ)
    (hq : Function.Surjective q)
    (f : (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ.IntertwiningMap π.ρ)
    (hf : Function.Surjective f) :
    Function.Surjective (fineAmbientHomMap T B S ω v₀ t hω π J q f) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  have hπ : IsSmooth π.ρ :=
    isSmooth_of_surjective f hf
      (T.isSmooth_normalizedRefinedInduced B S (fineTwist T B S ω v₀ 0).ρ)
  have hft : Function.Surjective (coarseTwistHom T B S ω v₀ t π f) :=
    hf.comp (coarseTwistEquiv T B S ω v₀ t).symm.surjective
  have hi : Function.Surjective
      (T.normalizedParabolicInducedMap B (coarseTwistHom T B S ω v₀ t π f)) :=
    normalizedInducedSurjectivity_of_smoothInductionSurjectivity T B
      Induction.smoothInductionSurjectivity _ _ _ _ _
      (T.isSmooth_normalizedRefinedInduced B S (fineTwist T B S ω v₀ t).ρ)
      ((T.isSmooth_leviRealPowerTwist_iff B t π.ρ).mpr hπ) hft
  rw [fineAmbientHomMap_apply]
  exact hq.comp (hi.comp (flatStagesEquiv T B S ω v₀ t hω).symm.surjective)

/-- The actual fine-to-ambient Hom map is injective on all inner intertwiners,
for an irreducible coarse target, a nontrivial ambient carrier and a specified
surjective outer intertwiner. -/
theorem fineAmbientHomMapInjective :
    FineAmbientHomMapInjectivityStatement.{uF, uV, uW, uZ} := by
  intro p _ F T
  let := T.topology
  intro n B S ω v₀ t hω π hπ J hJ q hq
  let := hπ
  let := hJ
  let C := fineAmbientHomMap T B S ω v₀ t hω π J q
  have hker : ∀ f, C f = 0 → f = 0 := by
    intro f hzero
    by_contra hf
    have hfSurj : Function.Surjective f :=
      (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
    have hCf := fineAmbientHomMap_surjective T B S ω v₀ t hω π J q hq f hfSurj
    obtain ⟨w, hw⟩ := exists_ne (0 : J.V)
    obtain ⟨x, hx⟩ := hCf w
    change C f x = w at hx
    rw [hzero] at hx
    exact hw hx.symm
  intro f g hfg
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hfg, sub_self]

end Langlands.RelativeHomComparison
