/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharts
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectTransportComplete
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionAlgEquiv
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformLocalModelCohomology
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion

/-! # Perfect charts for the actual unlifted Padic datum

Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.8.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A bounded constructible complete complex has constant perfect models on covers
of finitely many strata, using its actual unlifted coefficient datum. This assertion
has no elementary-divisor decomposition and no assertion about consecutive-quotient Tor.

Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.8.
(blueprint: lem-weil-pbc-adic-unlifted-perfect-charts).

Proof: choose a basis of the finite extension E over Q_l and use its coordinate image
in a finite power of Q_l to obtain an algebraically isomorphic field in the smaller
universe. Uniqueness of the extended absolute value identifies the two valuation rings.
Their uniformizers generate the corresponding maximal ideals, so the ring equivalence
identifies every power of those ideals, independently of the chosen uniformizers.
Consequently it identifies the quotient diagrams and their completed ring sheaves.
Restriction of scalars along these isomorphisms is an exact equivalence, compatible
with derived reduction, the intrinsic completion unit and the retained etale origins.
Apply the integral stratified-perfect characterization to this transported complex.
Choose a covering family generating each covering sieve. Localization at its weakly
etale objects identifies slice module sheaves with module sheaves on the covering
schemes. Compose inverse images along the cover map and stratum immersion. Transport
back the finite-projective complexes and the local isomorphisms along the coefficient
ring equivalence. Finite projectivity and both bounds are invariant under this exact
scalar equivalence. This produces the displayed perfect values and their isomorphisms.
The empty scheme and zero complexes require no nonempty chart or positive rank. -/
theorem pbc_adic_unlifted_perfect_charts
    (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)) :
    let d := pbcPadicCoefficientDatum l E
    let B := pbcAdicCompletion T d
    ∃ (S : Stratification T)
      (V : ∀ a : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain a)),
      ∀ (a : Fin S.n) (j : (V a).I₀),
        let g := (V a).f j ≫ S.immersion a
        ∃ C : completedConstantDerived
            (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)),
          @DerivedCategory.IsPerfectRingComplex _ _ (HasDerivedCategory.standard _) C ∧
          Nonempty ((adicTowerPullback g B).obj K.obj ≅
            (adicTowerPullback g B).obj ((integralConstantDerived T d).obj C)) := by
  intro d B
  obtain ⟨E₀, _, _, _, ⟨σ⟩⟩ := Padic.exists_algEquiv_coefficientExtension.{u} l E
  let φ : Padic.coefficientExtensionIntegers l E ≃+* PbcIntegralRing l E₀ :=
    (Padic.coefficientExtensionIntegersEquiv l σ).trans ULift.ringEquiv.symm
  have hφ : d.ideal.map φ = (pbcIntegralDatum l E₀).ideal := by
    change Ideal.map φ (Ideal.span {Padic.coefficientExtensionUniformizer l E}) =
      Ideal.span {pbcUniformizer l E₀}
    have h := Padic.map_span_coefficientExtensionUniformizer l
      (Padic.coefficientExtensionIntegersEquiv l σ)
    rw [Ideal.map_span, Set.image_singleton] at h ⊢
    have h' := congrArg (Ideal.map (ULift.ringEquiv.symm : Padic.coefficientExtensionIntegers l E₀
      ≃+* PbcIntegralRing l E₀)) h
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at h'
    exact h'
  have hl' : IsUnit (l : Γ(T, ⊤)) :=
    T.toRingedSpace.isUnit_of_isUnit_germ ⊤ (l : Γ(T, ⊤)) (fun x _ ↦ by
      simpa only [map_natCast] using hl x)
  have hπ : Padic.coefficientExtensionUniformizer l E ≠ 0 :=
    Padic.coefficientExtensionUniformizer_ne_zero l E
  have hp := pbcUniformLocalModelCohomology_of_principal d
    (Padic.coefficientExtensionUniformizer l E) rfl hπ T K.obj ⟨K.property.2.1, K.property.2.2⟩
  have hK := isIntegralStratifiedPerfect_of_ringEquiv T d (pbcIntegralDatum l E₀) φ hφ
    (fun K' hc' hp' ↦ ((integralStratifiedPerfectCharacterization T l E₀ hdim hl' K').1).mp
      ⟨hc', pbcUniformReductionCriterion_backward l E₀ T K' hp'⟩)
    K.obj K.property.1 hp
  exact IsIntegralStratifiedPerfect.exists_cover_charts T d K.obj hK

end AlgebraicGeometry.Scheme
