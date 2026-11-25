/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale

import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitSectionLift
import WeilConjectures.AlgebraicGeometry.Morphisms.RootProductChartBaseChangeFactor
import WeilConjectures.AlgebraicGeometry.Morphisms.TraitNormalizationGenericSectionComparison

/-! Generic section factors of a supplied trait-divisor chart.

## References

* Stacks Project, Tags 0EYH, 0EYI and 0EYJ
* Stacks Project, Tag 0EYI, preliminary paragraph before parts (1) and (2), and Tag 0EYJ, the local
  trait reduction
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Each supplied trait-divisor root factor restricts along the section to a
root of a uniformizer over an unramified trait extension.

Precisely: let `n` be the base change of the relative normalization to
`C ×_S Spec 𝒪_{S,s}`, `τ` the section induced by `σ`, and
`φ: Spec R ⟶ C ×_S Spec 𝒪_{S,s}` an étale chart through a point of `n` over `τ` of the
closed point, lying over `Spec ρ`, on which `n` is the product of the root covers
`R[T]/(T^(e k) - ρ(ϖ₀))`. Then there are a DVR `A` with an injective
`δ: 𝒪_{S,s} →+* A` and `ι: R →+* A` such that `Spec ι` followed by `φ` equals `Spec δ`
followed by `τ`, `δ ϖ₀` is a uniformizer of `A` equal to `ι (ρ ϖ₀)`, and, writing
`K = Frac A` and `ε: k(S) →+* K` for the extension of `𝒪_{S,s} → A → K`, the `k`-th
root factor `K[T]/(T^(e k) - δ ϖ₀)` is an open subscheme of `Z` pulled back along
`Spec ε` followed by the generic section `sη`, compatibly with the projections to `Spec K`. -/
theorem GaloisCover.trait_divisor_chart_section_generic_factor {S C : Scheme.{u}}
    [IsNoetherian S] [IsIntegral S]
    (c : C ⟶ S) (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    {G : Type (u + 1)} [Group G] [Finite G]
    {Cη : Scheme.{u}} (j : Cη ⟶ C) (sη : Spec S.functionField ⟶ Cη)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη)
    (U : S.Opens) (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU)
    (s : S) [IsDiscreteValuationRing (S.presheaf.stalk s)] :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    ∀ x : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a) : Scheme.{u}),
      n x = τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) →
      ∀ (R : CommRingCat.{u}) (φ : Spec R ⟶ pullback c a) (y : Spec R)
        (ρ : S.presheaf.stalk s →+* R) (ϖ₀ : S.presheaf.stalk s),
        Etale φ → φ y = n x →
        IsLocalRing.maximalIdeal (S.presheaf.stalk s) = Ideal.span {ϖ₀} →
        φ ≫ pullback.snd c a = Spec.map (CommRingCat.ofHom ρ) →
        ∀ (m : ℕ) (e : Fin m → ℕ)
          (α : pullback n φ ≅ Spec (CommRingCat.of (∀ k : Fin m,
              AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ₀))))),
            α.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap R (∀ k : Fin m,
                AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C (ρ ϖ₀))))) =
              pullback.snd n φ → ∀ k : Fin m,
          ∃ (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
            (δ : S.presheaf.stalk s →+* A) (ι : R →+* A),
            Function.Injective δ ∧
            IsLocalRing.maximalIdeal A = Ideal.span {δ ϖ₀} ∧
            ι (ρ ϖ₀) = δ ϖ₀ ∧
            Spec.map (CommRingCat.ofHom ι) ≫ φ = Spec.map (CommRingCat.ofHom δ) ≫ τ ∧
            ∃ ε : S.functionField →+* FractionRing A,
              ε.comp (algebraMap (S.presheaf.stalk s) S.functionField) =
                (algebraMap A (FractionRing A)).comp δ ∧
              ∃ g : Spec (CommRingCat.of (AdjoinRoot ((Polynomial.X : Polynomial
                  (FractionRing A)) ^ e k - Polynomial.C (algebraMap A _ (δ ϖ₀))))) ⟶
                  pullback Z.π (Spec.map (CommRingCat.ofHom ε) ≫ sη),
                IsOpenImmersion g ∧
                g ≫ pullback.snd Z.π (Spec.map (CommRingCat.ofHom ε) ≫ sη) =
                  Spec.map (CommRingCat.ofHom (algebraMap (FractionRing A)
                    (AdjoinRoot ((Polynomial.X : Polynomial (FractionRing A)) ^ e k -
                      Polynomial.C (algebraMap A _ (δ ϖ₀)))))) := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  intro x hx R φ y ρ ϖ₀ hφ hy hϖ₀ hρ m e α hα k
  let a := S.fromSpecStalk s
  let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
    (pullback.fst c a)
  let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
    pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  have hτ : τ ≫ pullback.snd c a = 𝟙 _ := by simp [τ]
  have hyτ : φ y = τ (IsLocalRing.closedPoint (S.presheaf.stalk s)) := hy.trans hx
  obtain ⟨A, hAd, hAv, δ, ι, hδ, hmax, hcoeff, hcomm⟩ :=
    etale_trait_section_lift (S.presheaf.stalk s) (pullback.snd c a) τ hτ
      R φ y hφ hyτ ρ hρ ϖ₀ hϖ₀
  let K := FractionRing A
  let θ : R →+* K := (algebraMap A K).comp ι
  have hθ : θ (ρ ϖ₀) = algebraMap A K (δ ϖ₀) := congrArg (algebraMap A K) hcoeff
  obtain ⟨ε, hε, β, hβ⟩ :=
    GaloisCover.trait_normalization_generic_section_comparison
      c σ hσ j sη hsj Z U jU PA ψ hjU hψ s A K δ hδ
  have hbase : Spec.map (CommRingCat.ofHom θ) ≫ φ =
      Spec.map (CommRingCat.ofHom ((algebraMap A K).comp δ)) ≫ τ := by
    rw [show Spec.map (CommRingCat.ofHom θ) =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
        Spec.map (CommRingCat.ofHom ι) by simp [θ, ← Spec.map_comp]]
    rw [Category.assoc, hcomm]
    simp only [← Category.assoc, ← Spec.map_comp]
    rfl
  have hfactor := rootProductChart_baseChange_factor n R φ (ρ ϖ₀) m e α hα K θ k
  rw [hθ, hbase] at hfactor
  obtain ⟨g, hg, hw⟩ := hfactor
  refine ⟨A, hAd, hAv, δ, ι, hδ, hmax, hcoeff, hcomm, ε, hε, g ≫ β.hom, inferInstance,
    ?_⟩
  rw [Category.assoc, hβ, hw]

end AlgebraicGeometry.Scheme
