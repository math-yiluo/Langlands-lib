/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedGlobalSections
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Injectivity of restriction on the punctured power-series section

## References

* Stacks Project, Tags 0EY9, 0BK0, 0EKP and 0EL8
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Injectivity of restriction on morphisms of finite étale covers in the
power-series punctured-section situation. This is the uniqueness part of
Stacks Project, Tag 0EY9, proved here using connectedness and a faithful
geometric-fibre functor. -/
theorem finiteEtale_powerSeries_punctured_section_restriction_injective
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    let z := Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))
    ∀ P Q : V.toScheme.FiniteEtale,
      Function.Injective ((FiniteEtale.pullback (z ∣_ V)).map (X := P) (Y := Q)) := by
  classical
  dsimp only
  let z := Spec.map
    (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))
  obtain ⟨x, hx⟩ : ∃ x : Spec (.of A), x ≠ IsLocalRing.closedPoint A := by
    by_contra h
    have heq : ∀ x : PrimeSpectrum A, x = IsLocalRing.closedPoint A := by
      push Not at h
      change ∀ x : PrimeSpectrum A, x = IsLocalRing.closedPoint A at h
      exact h
    have : Subsingleton (PrimeSpectrum A) := ⟨fun a b ↦ (heq a).trans (heq b).symm⟩
    have hdim : ringKrullDim A ≤ 0 := Order.krullDim_nonpos_of_subsingleton
    have hb := IsLocalRing.depth_le_supportDim (R := A) A
    rw [Module.supportDim_self_eq_ringKrullDim] at hb
    have htwo : (2 : WithBot ℕ∞) ≤ 0 :=
      (WithBot.coe_le_coe.mpr hdepth).trans (hb.trans hdim)
    norm_num at htwo
  let x₀ : (z ⁻¹ᵁ V).toScheme := ⟨x, (hV x).mpr hx⟩
  have : Nonempty V.toScheme := ⟨(z ∣_ V) x₀⟩
  let φ := ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom
  -- The structure-sheaf comparison suffices; no internal Hom completion is needed.
  have hφ := bijective_powerSeries_punctured_globalSections A hdepth d hd V hV
  have : Nontrivial Γ(V.toScheme, ⊤) :=
    (V.toScheme.presheaf.germ ⊤ ((z ∣_ V) x₀) trivial).hom.domain_nontrivial
  have : IsLocalRing Γ(V.toScheme, ⊤) := IsLocalRing.of_surjective' φ hφ.2
  have : ConnectedSpace V.toScheme :=
    (connectedSpace_iff_isIdempotentElem V.toScheme).mpr
      (fun e he ↦ IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem he)
  intro P Q a b hab
  let s := (z ⁻¹ᵁ V).toScheme.algClosurePoint x₀
  let t := s ≫ (z ∣_ V)
  apply (FiniteEtale.fiber t).map_injective
  apply ConcreteCategory.hom_ext
  intro y
  apply FiniteEtale.fiber_ext
  let c := Limits.pullback.lift y.left s (FiniteEtale.fiber_left_comp t y)
  have hh := congrArg
    (fun k ↦ c ≫ k.hom.left ≫ Limits.pullback.fst Q.obj.hom (z ∣_ V)) hab
  change y.left ≫ a.hom.left = y.left ≫ b.hom.left
  simpa [c, z, Category.assoc, FiniteEtale.pullback_map_hom_left] using hh

end AlgebraicGeometry.Scheme
