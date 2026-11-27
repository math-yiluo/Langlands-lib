import Langlands.Global.LocalWavePacketSomeCompactReduction
import Langlands.Global.AdelicTruncatedEisensteinAsymptoticsStatement

/-! # Lapid's §8 limit for standard parabolic subgroups

Lapid 2011, §8, p.328, works with standard parabolic subgroups `P, P' ⊇ P₀` of one minimal pair
`(P₀, A₀)` and one maximal compact `K` in good position. This module states the limit of
truncated inner products of wave packets (the sufficient condition of §8 obtained from Lemma 9)
in that standard setting, and states the transport to arbitrary presented parabolics.

* `TruncatedStandardWavePacketLimitStatement`: for every maximal split torus `i : T → G` and
  generic cocharacter `ν` there is one maximal compact `K` with `Q(𝔸)K = G(𝔸)` for `P₀` and every
  standard `Q`, whose full-quotient truncation has Arthur's projection property, such that the
  limit holds for wave packets of holomorphic families on any two standard parabolic subgroups.
* `TruncatedWavePacketStandardizationStatement`: the first statement implies
  `TruncatedWavePacketSectionSomeCompactLimitStatement`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter
open scoped CategoryTheory.MonObj TensorProduct Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- Lapid 2011, §8, p.328 (the sufficient condition obtained from Lemma 9), for standard
parabolic subgroups. For every number field `F`, connected reductive `G`, maximal split torus
`i : T → G` and generic cocharacter `ν` (with minimal parabolic `P₀` and standard parabolic
subgroups `Q`), there is a maximal compact `K` of `G(𝔸)` with `P₀(𝔸)K = Q(𝔸)K = G(𝔸)` for every
standard `Q` such that, for all reflection data `D` and comparisons `hρ`:

* for some `C` and every `T` with `β(T) > C` for all simple roots `β`, the full-quotient
  truncation `truncation hG hi D hK₀ hρ T` extends to an orthogonal projection on
  `L²(G(F) \ G(𝔸))`;
* for all standard parabolic subgroups `P = P_J`, `P' = P_{J'}`, all data of
  `TruncatedWavePacketSectionSomeCompactLimitStatement` with respect to `K` for `P` and `P'`
  (holomorphic families `λ ↦ ∑_l b_{j,l}(λ) v_{j,l}` with entire `b_{j,l}`, continuations
  `E j` holomorphic on `DE ⊇ {i e(x) : x ∈ Sx}`, smooth coefficients `c j` vanishing outside
  the compact `Sx`, likewise for `P'`; representatives of `Ω(P, P')`; expansions of
  `∑_l b_{j,l}(λ) M(w, λ) v_{j,l}`), where "sufficiently regular" is
  `IsStandardRegularParameter D`, and every direction `v₀` on which every simple root is
  positive: the functions `y ↦ Θ(y.out)`, `y ↦ Θ'(y.out)` on `G(F) \ G(𝔸)` are measurable and
  bounded on compact sets, their truncations `Λ^{j v₀}` are eventually square integrable with
  bounded norms, and `(Λ^{j v₀} Θ, Λ^{j v₀} Θ')` tends to
  `∫ ∑_{w ∈ Ω(P, P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ` as `j → ∞`, written out in the data. -/
def TruncatedStandardWavePacketLimitStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
  ∃ K : Subgroup (AdelicGroupPoints F G),
    IsMaximalCompactSubgroup F G K ∧
    IsIwasawaCompact (Standard.parabolicHom i ν ∅) K ∧
    (∀ S : StandardIndex hG hi ν, IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K) ∧
  ∀ (D : RelativeRootReflectionData i) (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    (hK₀ : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hK : ∀ S : StandardIndex hG hi ν, IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K),
    (∃ C : ℝ, ∀ Tp : V T, (∀ β ∈ simpleRelativeRoots i ν, C < eval T β Tp) →
      IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)
        (fun f q => truncation hG hi D hK₀ hρ Tp
          (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) q.out)) ∧
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth), IsClosedSubgroup rho →
  ∀ (J J' : StandardIndex hG hi ν)
    (π' : Standard.parabolicScheme i ν J'.roots ⟶ Standard.leviScheme i ν J'.roots),
    Standard.leviToParabolic i ν J'.roots ≫ π' = 𝟙 (Standard.leviScheme i ν J'.roots) →
  ∀ (μM' : Measure (AdelicGroupPoints F (Standard.leviScheme i ν J'.roots)))
    [μM'.IsHaarMeasure],
    IsIwasawaCompatibleMeasure K (hK J').isCompact (Standard.parabolicHom i ν J'.roots)
      (Standard.unipotentToParabolic i ν J'.roots) (Standard.leviToParabolic i ν J'.roots) μM' →
  ∀ {n n' : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν J.roots))
    (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν J'.roots))
    (β' : (Fin n' → ℝ) → ℝ),
    Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
  ∀ (k q : ℕ) (v : Fin k → Fin q → AdelicGroupPoints F G → ℂ)
    (b : Fin k → Fin q → ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ)
    (c : Fin k → (Fin n → ℝ) → ℂ) (Sx : Set (Fin n → ℝ))
    (E : Fin k → ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) →
      AdelicGroupPoints F G → ℂ)
    (DE : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))),
    (∀ j l, IsSquareIntegrableInducedForm K (hK J).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J.roots) (Standard.unipotentToParabolic i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) (v j l)) →
    (∀ j l, IsMeromorphicInCoordinatesOn (b j l) Set.univ) →
    IsCompact Sx →
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ ∀ x ∉ Sx, c j x = 0) →
    (fun x => imaginaryParameter F _ (e x)) '' Sx ⊆ DE →
    (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) DE) →
    (∀ j, ∃ R : ℝ, ∀ lam, IsStandardRegularParameter D J.roots R lam → ∀ g,
      E j lam g = ∑ l, b j l lam * (hK J).eisensteinSeries (v j l) lam g) →
  ∀ (k' q' : ℕ) (v' : Fin k' → Fin q' → AdelicGroupPoints F G → ℂ)
    (b' : Fin k' → Fin q' → ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) →
      ℂ)
    (c' : Fin k' → (Fin n' → ℝ) → ℂ) (Sx' : Set (Fin n' → ℝ))
    (E' : Fin k' → ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) →
      AdelicGroupPoints F G → ℂ)
    (DE' : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots))),
    (∀ j l, IsSquareIntegrableInducedForm K (hK J').isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J'.roots) (Standard.unipotentToParabolic i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (v' j l)) →
    (∀ j l, IsMeromorphicInCoordinatesOn (b' j l) Set.univ) →
    IsCompact Sx' →
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c' j) ∧ ∀ x ∉ Sx', c' j x = 0) →
    (fun x => imaginaryParameter F _ (e' x)) '' Sx' ⊆ DE' →
    (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E' j lam g) DE') →
    (∀ j, ∃ R : ℝ, ∀ lam, IsStandardRegularParameter D J'.roots R lam → ∀ g,
      E' j lam g = ∑ l, b' j l lam * (hK J').eisensteinSeries (v' j l) lam g) →
  ∀ (Ω : Type) [Fintype Ω] (w : Ω → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cw : Ω → (Standard.leviScheme i ν J'.roots ⟶ Standard.leviScheme i ν J.roots)),
    (∀ t, IsWeylConjugation (Standard.parabolicHom i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (w t) (cw t)) →
    Function.Injective (fun t => weylParameter (Standard.leviToParabolic i ν J.roots) (cw t) π') →
    (∀ σ ∈ weylParameterSet (Standard.parabolicHom i ν J.roots)
        (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν J'.roots)
        (Standard.leviToParabolic i ν J'.roots) π',
      ∃ t, weylParameter (Standard.leviToParabolic i ν J.roots) (cw t) π' = σ) →
  ∀ (m : ℕ) (ψ : Ω → Fin k → Fin m → AdelicGroupPoints F G → ℂ)
    (coeff : Ω → Fin k → Fin m → ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) →
      ℂ)
    (DM : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))),
    (∀ t j a, IsSquareIntegrableInducedForm K (hK J').isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν J'.roots) (Standard.unipotentToParabolic i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (ψ t j a)) →
    (fun x => imaginaryParameter F _ (e x)) '' Sx ⊆ DM →
    (∀ t j a, IsMeromorphicInCoordinatesOn (coeff t j a) DM) →
    (∀ t j, ∃ R : ℝ, ∀ lam, IsStandardRegularParameter D J.roots R lam → ∀ g,
      ∑ l, b j l lam * (hK J).intertwiningOperator (hK J')
          (Standard.unipotentToParabolic i ν J.roots) (Standard.leviToParabolic i ν J.roots)
          (Standard.unipotentToParabolic i ν J'.roots) (cw t) π' (w t) (v j l) lam g =
        ∑ a, coeff t j a lam * ψ t j a g) →
  ∀ v₀ : V T, (∀ β ∈ simpleRelativeRoots i ν, 0 < eval T β v₀) →
  let Θ : AdelicGroupPoints F G → ℂ := fun g =>
    ∫ x, ∑ j, c j x * E j (imaginaryParameter F _ (e x)) g ∂(spectralMeasure n)
  let Θ' : AdelicGroupPoints F G → ℂ := fun g =>
    ∫ x, ∑ j, c' j x * E' j (imaginaryParameter F _ (e' x)) g ∂(spectralMeasure n')
  let μG : Measure (RationalQuotient F G) :=
    LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
      (isDiscrete_rationalSubgroup F G) Measure.haar
  let trunc (j : ℕ) (f : RationalQuotient F G → ℂ) (y : RationalQuotient F G) : ℂ :=
    truncation hG hi D hK₀ hρ ((j : ℝ) • v₀)
      (fun x => f (LeftCosetSpace.mk (rationalSubgroup F G) x)) y.out
  let f : RationalQuotient F G → ℂ := fun y => Θ y.out
  let f' : RationalQuotient F G → ℂ := fun y => Θ' y.out
  Measurable f ∧ Measurable f' ∧
    (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖f x‖ ≤ B) ∧
    (∀ C : Set (RationalQuotient F G), IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖f' x‖ ≤ B) ∧
    (∀ᶠ j : ℕ in atTop, MemLp (trunc j f) 2 μG) ∧
    (∀ᶠ j : ℕ in atTop, MemLp (trunc j f') 2 μG) ∧
    (∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
      (∫ y, trunc j f y * (starRingEnd ℂ) (trunc j f y) ∂μG).re ≤ B) ∧
    (∃ B : ℝ, ∀ᶠ j : ℕ in atTop,
      (∫ y, trunc j f' y * (starRingEnd ℂ) (trunc j f' y) ∂μG).re ≤ B) ∧
    Tendsto (fun j : ℕ => ∫ y, trunc j f y * (starRingEnd ℂ) (trunc j f' y) ∂μG) atTop
      (𝓝 (∫ x, ∑ t, ∑ j, ∑ a, ∑ j', ∑ l',
          c j x * coeff t j a (imaginaryParameter F _ (e x)) *
            (starRingEnd ℂ) (c' j' (e'.symm (realWeylParameter
              (Standard.leviToParabolic i ν J.roots) (cw t) π' (e x)))) *
            (starRingEnd ℂ) (b' j' l' (weylParameter (Standard.leviToParabolic i ν J.roots)
              (cw t) π' (imaginaryParameter F _ (e x)))) *
            inducedInnerProduct K (hK J').isCompact (Standard.parabolicHom i ν J'.roots)
              (Standard.leviToParabolic i ν J'.roots) μM' e' β' (ψ t j a) (v' j' l')
        ∂(spectralMeasure n)))

/-- The transport of `TruncatedStandardWavePacketLimitStatement` to arbitrary presented
parabolic subgroups: it implies `TruncatedWavePacketSectionSomeCompactLimitStatement`. -/
def TruncatedWavePacketStandardizationStatement : Prop :=
  TruncatedStandardWavePacketLimitStatement → TruncatedWavePacketSectionSomeCompactLimitStatement

end Langlands.Global
