/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

public import Mathlib.RingTheory.RingHom.Flat

public import Mathlib.RingTheory.AdjoinRoot

public import Mathlib.RingTheory.Localization.AtPrime.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts
import WeilConjectures.AlgebraicGeometry.Morphisms.RootProductChartStalkLocalization
import WeilConjectures.AlgebraicGeometry.Morphisms.TraitDivisorChartSectionGenericFactor

/-!
# Localized tame root chart and its transverse generic factor

## References

* Stacks Project, Tags 0EYH and 0EYI, proof before parts (1) and (2)
* Stacks Project, Tags 0EYH and 0EYI, proof before parts (1) and (2), and Tag 0EYJ, the trait
  reduction
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The geometric chart construction, retaining the localization at the chosen root point.
It does not identify that localization with the whole root algebra or assert that the
canonical map into the whole root algebra is local. -/
theorem GaloisCover.stalk_normalization_trait_section_localized_root_chart {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη)
    (U : S.Opens)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    IsFinite n → ∀ x : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a) : Scheme.{u}),
      n x = τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) →
      let B := (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
        (pullback.fst c a)).presheaf.stalk x
      let J := (IsLocalRing.maximalIdeal ((pullback c a).presheaf.stalk (n x))).map
        (n.stalkMap x).hom
      ∃ (R : CommRingCat.{u}) (_ : IsLocalRing R) (f : R) (e : ℕ),
        0 < e ∧ f ∈ IsLocalRing.maximalIdeal R ∧
        let p := (Polynomial.X : Polynomial R) ^ e - Polynomial.C f
        let D := AdjoinRoot p
        ∃ (P : Ideal D) (hP : P.IsMaximal),
          letI : P.IsPrime := hP.isPrime
          let E := Localization.AtPrime P
          ∃ (β : B →+* E), IsLocalHom β ∧ β.Flat ∧
          J.map β = (IsLocalRing.maximalIdeal R).map
            ((algebraMap D E).comp (AdjoinRoot.of p)) ∧
          ∃ (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
            (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K)
            (ϖ : A) (π : Kˣ) (b : Spec (CommRingCat.of K) ⟶ Spec S.functionField),
            IsLocalRing.maximalIdeal A = Ideal.span {ϖ} ∧ (π : K) = algebraMap A K ϖ ∧
            ∃ g : Spec (CommRingCat.of
                (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e - Polynomial.C (π : K)))) ⟶
                pullback Z.π (b ≫ sη),
              IsOpenImmersion g ∧
              g ≫ pullback.snd Z.π (b ≫ sη) =
                Spec.map (CommRingCat.ofHom (algebraMap K
                  (AdjoinRoot ((Polynomial.X : Polynomial K) ^ e -
                    Polynomial.C (π : K))))) := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro hn x hx
  have hchart := GaloisCover.stalk_normalization_trait_divisor_charts
      (S := S) (C := C) (Cη := Cη)
      c σ hσ G hG q j hCη Z U jU PA ψ hjU hψ
      s hs hmin hdvr
  dsimp only at hchart
  have hchartn := hchart hn
  have hchartx := hchartn x
  have hcharth := hchartx hx
  obtain ⟨R, φ, y, ρ, ϖ₀, hdata⟩ := hcharth
  obtain ⟨hφ, hy, hϖ₀, hρ, hf, m, e, he, α, hα⟩ := hdata
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
    (pullback.fst c (S.fromSpecStalk s))
  have hlocal := rootProductChart_stalk_localization n R φ y hφ x hy
    (ρ ϖ₀) hf m e he α hα
  dsimp only at hlocal
  obtain ⟨k, R₀, hR₀, f₀, hf₀, P, hP, β, hβ, hflat, hJ⟩ := hlocal
  have : IsDiscreteValuationRing (S.presheaf.stalk s) := hdvr
  have hgen := GaloisCover.trait_divisor_chart_section_generic_factor (G := G) c σ hσ j sη hsj Z U
    jU PA ψ hjU hψ s
  dsimp only at hgen
  have hgen2 := hgen x hx R φ y ρ ϖ₀ hφ hy hϖ₀ hρ m e α hα k
  obtain ⟨A, hAd, hAdvr, δ, _, _, hAmax, _, _, ε, _, g, hg, hgπ⟩ := hgen2
  have hϖ : algebraMap A (FractionRing A) (δ ϖ₀) ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr fun h0 ↦ ?_
    exact IsDiscreteValuationRing.not_a_field' (R := A)
      (by rw [hAmax, h0, Ideal.span_singleton_eq_bot])
  exact ⟨R₀, hR₀, f₀, e k, he k, hf₀, P, hP, β, hβ, hflat, hJ, A, hAd, hAdvr, FractionRing A,
    inferInstance, inferInstance, inferInstance, δ ϖ₀, Units.mk0 _ hϖ,
    Spec.map (CommRingCat.ofHom ε), hAmax, rfl, g, hg, hgπ⟩

end AlgebraicGeometry.Scheme
