import Langlands.Global.LocalWavePacketSomeCompactReduction
import Langlands.Global.AdelicTruncatedEisensteinFamilyAsymptoticsStatement

/-! # The limit of the integrated main terms in Lapid's §8

Lapid 2011, §8, p.328: after the Fourier transform in the central variable and Proposition 1,
the truncated inner product of two wave packets has the same limit as the integral (18) of the
main terms of formula (2). Lapid then shows that the limit of (18) exists and equals the right
side of formula (4), using `(G, M)`-families (Arthur 1982, §§1–2) and Lemma 8.

* `WavePacketMainTermLimitStatement`: this limit, for standard parabolic subgroups `P = P_J`,
  `P' = P_{J'}`, holomorphic families of inducing vectors and every maximal compact `K` with
  `Q(𝔸)K = G(𝔸)` for every standard `Q`. The integral over `μ ∈ i𝔞_G^*`, `λ ∈ i(𝔞_P^G)^*`,
  `λ' ∈ i(𝔞_{P'}^G)^*` is written in linear coordinates adapted to the central parameter. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Filter
open scoped CategoryTheory.MonObj TensorProduct Topology Classical

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic
  ArthurTruncation ArthurParabolicSpaces

/-- **Lapid 2011, §8, p.328: the limit of (18) is the right side of (4).** Fix a number field
`F`, a connected reductive `G`, a maximal split torus `i : T → G`, a generic cocharacter `ν`, a
maximal compact `K` with `Q(𝔸)K = G(𝔸)` for every standard `Q`, and reflection data `D`.

The data are:

* the normalizations of the main term of formula (2), as in
  `LocalTruncatedEisensteinFamilyInnerProductStatement`: Levi projections `π S`, Haar measures
  `μM S` compatible with the Iwasawa decompositions, coordinates `eS S` with cutoffs `βS S`
  (`∫ βS S = 1`) for every standard `S`, and a basis `cd` of `𝔞_G = relativeCentralDirections i`;
* two standard parabolic subgroups `P = P_J`, `P' = P_{J'}` and the data of
  `TruncatedWavePacketSectionSomeCompactLimitStatement` for them: wave packets
  `Θ = ∫ ∑_j c_j(x) E_j(i e(x)) dx` and `Θ'` of holomorphic families, a Levi projection `π'`
  of `P'`, the inner product `(·,·)_{P'}` given by `μM'`, `e'`, `β'`, representatives of
  `Ω(P, P')` and the expansions of `∑_l b_{j,l}(λ) M(w, λ) v_{j,l}` in `A^2_{P'}`, which enter the
  right side of (4);
* for every standard `S`, representatives `wS S t` of `Ω(P, S)` and expansions of
  `∑_l b_{j,l}(λ) M(w, λ) v_{j,l}` in `A^2_S` with coefficients holomorphic on `DMS`, which
  contains the support of the packet; likewise for `P'`. These enter the main term;
* linear coordinates adapted to the central parameter: `A : ℝ^{n₁} × ℝ^m ≃ ℝ^n` carrying
  `ν₁ × dz` to Lebesgue measure such that the parameter `e(A(u, z))` pairs with `cd k` to
  `z k`, and likewise `A'` for `P'`; `u` parametrizes `(𝔞_P^G)^*` and `z` the central
  parameter;
* a direction `v₀` on which every simple root is positive.

For `T ∈ V T` let `mainTerm j j' T λ λ'` be the main term of formula (2) for the families `j` and
`j'`, and let `I(T)` be `(2π)^{m - n - n'}` times

`∫ z ∫ u ∫ u' ∑_{j, j'} c_j(A(u, z)) conj(c'_{j'}(A'(u', z)))
  mainTerm j j' T (i e(A(u, z))) (i e'(A'(u', z))) dν₁'(u') dν₁(u) dz`,

the integral (18) in these coordinates. The statement asserts that `I(j • v₀)` tends to
`∫ ∑_{w ∈ Ω(P, P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ` (written out in the data, as in
`TruncatedWavePacketSectionSomeCompactLimitStatement`) as `j → ∞`. -/
def WavePacketMainTermLimitStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
  ∀ (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
  ∀ (hK : ∀ S : StandardIndex hG hi ν, IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K)
    (D : RelativeRootReflectionData i),
  ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth), IsClosedSubgroup rho →
  ∀ (π : ∀ S : StandardIndex hG hi ν,
      Standard.parabolicScheme i ν S.roots ⟶ Standard.leviScheme i ν S.roots),
    (∀ S : StandardIndex hG hi ν,
      Standard.leviToParabolic i ν S.roots ≫ π S = 𝟙 (Standard.leviScheme i ν S.roots)) →
  ∀ (μM : ∀ S : StandardIndex hG hi ν,
      Measure (AdelicGroupPoints F (Standard.leviScheme i ν S.roots))),
    (∀ S : StandardIndex hG hi ν, (μM S).IsHaarMeasure ∧
      IsIwasawaCompatibleMeasure K (hK S).isCompact (Standard.parabolicHom i ν S.roots)
        (Standard.unipotentToParabolic i ν S.roots) (Standard.leviToParabolic i ν S.roots)
        (μM S)) →
  ∀ (nS : StandardIndex hG hi ν → ℕ)
    (eS : ∀ S : StandardIndex hG hi ν, (Fin (nS S) → ℝ) ≃ₗ[ℝ]
      RealCharacterParameter F (Standard.parabolicScheme i ν S.roots))
    (βS : ∀ S : StandardIndex hG hi ν, (Fin (nS S) → ℝ) → ℝ),
    (∀ S : StandardIndex hG hi ν,
      Continuous (βS S) ∧ HasCompactSupport (βS S) ∧ ∫ y, βS S y = 1) →
  ∀ (m : ℕ) (cd : Fin m → V T), LinearIndependent ℝ cd →
    Submodule.span ℝ (Set.range cd) = relativeCentralDirections i →
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
  ∀ (mψ : ℕ) (ψ : Ω → Fin k → Fin mψ → AdelicGroupPoints F G → ℂ)
    (coeff : Ω → Fin k → Fin mψ →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ)
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
  ∀ (ΩS : StandardIndex hG hi ν → Type) [∀ S : StandardIndex hG hi ν, Fintype (ΩS S)]
    (wS : ∀ S : StandardIndex hG hi ν, ΩS S → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cwS : ∀ S : StandardIndex hG hi ν, ΩS S →
      (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J.roots)),
    (∀ (S : StandardIndex hG hi ν) t, IsWeylConjugation (Standard.parabolicHom i ν J.roots)
      (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (wS S t) (cwS S t)) →
    (∀ S : StandardIndex hG hi ν, Function.Injective
      (fun t => weylParameter (Standard.leviToParabolic i ν J.roots) (cwS S t) (π S))) →
    (∀ S : StandardIndex hG hi ν, ∀ σ ∈ weylParameterSet (Standard.parabolicHom i ν J.roots)
        (Standard.leviToParabolic i ν J.roots) (Standard.parabolicHom i ν S.roots)
        (Standard.leviToParabolic i ν S.roots) (π S),
      ∃ t, weylParameter (Standard.leviToParabolic i ν J.roots) (cwS S t) (π S) = σ) →
  ∀ (mS : ℕ) (ψS : ∀ S : StandardIndex hG hi ν, ΩS S → Fin k → Fin mS →
      AdelicGroupPoints F G → ℂ)
    (coeffS : ∀ S : StandardIndex hG hi ν, ΩS S → Fin k → Fin mS →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ)
    (DMS : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))),
    (∀ (S : StandardIndex hG hi ν) t j a,
      IsSquareIntegrableInducedForm K (hK S).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν S.roots) (Standard.unipotentToParabolic i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (ψS S t j a)) →
    (fun x => imaginaryParameter F _ (e x)) '' Sx ⊆ DMS →
    (∀ (S : StandardIndex hG hi ν) t j a, IsMeromorphicInCoordinatesOn (coeffS S t j a) DMS) →
    (∀ (S : StandardIndex hG hi ν) t j, ∃ R : ℝ,
      ∀ lam, IsStandardRegularParameter D J.roots R lam → ∀ g,
      ∑ l, b j l lam * (hK J).intertwiningOperator (hK S)
          (Standard.unipotentToParabolic i ν J.roots)
          (Standard.leviToParabolic i ν J.roots) (Standard.unipotentToParabolic i ν S.roots)
          (cwS S t) (π S) (wS S t) (v j l) lam g =
        ∑ a, coeffS S t j a lam * ψS S t j a g) →
  ∀ (ΩS' : StandardIndex hG hi ν → Type) [∀ S : StandardIndex hG hi ν, Fintype (ΩS' S)]
    (wS' : ∀ S : StandardIndex hG hi ν, ΩS' S → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (cwS' : ∀ S : StandardIndex hG hi ν, ΩS' S →
      (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J'.roots)),
    (∀ (S : StandardIndex hG hi ν) t, IsWeylConjugation (Standard.parabolicHom i ν J'.roots)
      (Standard.leviToParabolic i ν J'.roots) (Standard.parabolicHom i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (wS' S t) (cwS' S t)) →
    (∀ S : StandardIndex hG hi ν, Function.Injective
      (fun t => weylParameter (Standard.leviToParabolic i ν J'.roots) (cwS' S t) (π S))) →
    (∀ S : StandardIndex hG hi ν, ∀ σ ∈ weylParameterSet (Standard.parabolicHom i ν J'.roots)
        (Standard.leviToParabolic i ν J'.roots) (Standard.parabolicHom i ν S.roots)
        (Standard.leviToParabolic i ν S.roots) (π S),
      ∃ t, weylParameter (Standard.leviToParabolic i ν J'.roots) (cwS' S t) (π S) = σ) →
  ∀ (mS' : ℕ) (ψS' : ∀ S : StandardIndex hG hi ν, ΩS' S → Fin k' → Fin mS' →
      AdelicGroupPoints F G → ℂ)
    (coeffS' : ∀ S : StandardIndex hG hi ν, ΩS' S → Fin k' → Fin mS' →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) → ℂ)
    (DMS' : Set (ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots))),
    (∀ (S : StandardIndex hG hi ν) t j a,
      IsSquareIntegrableInducedForm K (hK S).isCompact rho hsmooth hcalc
      (Standard.parabolicHom i ν S.roots) (Standard.unipotentToParabolic i ν S.roots)
      (Standard.leviToParabolic i ν S.roots) (ψS' S t j a)) →
    (fun x => imaginaryParameter F _ (e' x)) '' Sx' ⊆ DMS' →
    (∀ (S : StandardIndex hG hi ν) t j a, IsMeromorphicInCoordinatesOn (coeffS' S t j a) DMS') →
    (∀ (S : StandardIndex hG hi ν) t j, ∃ R : ℝ,
      ∀ lam, IsStandardRegularParameter D J'.roots R lam → ∀ g,
      ∑ l, b' j l lam * (hK J').intertwiningOperator (hK S)
          (Standard.unipotentToParabolic i ν J'.roots)
          (Standard.leviToParabolic i ν J'.roots) (Standard.unipotentToParabolic i ν S.roots)
          (cwS' S t) (π S) (wS' S t) (v' j l) lam g =
        ∑ a, coeffS' S t j a lam * ψS' S t j a g) →
  ∀ (n₁ n₁' : ℕ) (ν₁ : Measure (Fin n₁ → ℝ)) (ν₁' : Measure (Fin n₁' → ℝ))
    (A : ((Fin n₁ → ℝ) × (Fin m → ℝ)) ≃ₗ[ℝ] (Fin n → ℝ))
    (A' : ((Fin n₁' → ℝ) × (Fin m → ℝ)) ≃ₗ[ℝ] (Fin n' → ℝ)),
    MeasurePreserving A (ν₁.prod (volume : Measure (Fin m → ℝ))) volume →
    MeasurePreserving A' (ν₁'.prod (volume : Measure (Fin m → ℝ))) volume →
    (∀ u z (r : Fin m), pair T (restrictToTorus F i ν J.roots (e (A (u, z)))) (cd r) = z r) →
    (∀ u z (r : Fin m), pair T (restrictToTorus F i ν J'.roots (e' (A' (u, z)))) (cd r) = z r) →
  ∀ v₀ : V T, (∀ β ∈ simpleRelativeRoots i ν, 0 < eval T β v₀) →
  let Λ (S : StandardIndex hG hi ν) (t : ΩS S) (t' : ΩS' S)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) :
      ComplexCharacterParameter F (Standard.parabolicScheme i ν S.roots) :=
    weylParameter (Standard.leviToParabolic i ν J.roots) (cwS S t) (π S) lam +
      weylParameter (Standard.leviToParabolic i ν J'.roots) (cwS' S t') (π S)
        (parameterConj F _ lam')
  let denom (S : StandardIndex hG hi ν) (t : ΩS S) (t' : ΩS' S)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) : ℂ :=
    ∏ α ∈ simpleFinset ν hG hi \ S.1,
      complexParameterPairing F _ (Λ S t t' lam lam')
        (toCharacterDual F i ν S.roots (corootVector D α))
  let mainTerm (j : Fin k) (j' : Fin k') (Tp : V T)
      (lam : ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots))
      (lam' : ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots)) : ℂ :=
    ∑ S : StandardIndex hG hi ν, ∑ t : ΩS S, ∑ t' : ΩS' S,
      (corootCovolume hG hi ν D S (eS S) cd : ℂ) *
        Complex.exp (complexParameterPairing F _ (Λ S t t' lam lam')
          (toCharacterDual F i ν S.roots Tp)) *
        (∑ a, ∑ a', coeffS S t j a lam * (starRingEnd ℂ) (coeffS' S t' j' a' lam') *
          inducedInnerProduct K (hK S).isCompact (Standard.parabolicHom i ν S.roots)
            (Standard.leviToParabolic i ν S.roots) (μM S) (eS S) (βS S)
            (ψS S t j a) (ψS' S t' j' a')) /
        denom S t t' lam lam'
  let I (Tp : V T) : ℂ :=
    (((2 * Real.pi) ^ m / ((2 * Real.pi) ^ n * (2 * Real.pi) ^ n') : ℝ) : ℂ) *
      ∫ z, ∫ u, ∫ u', ∑ j, ∑ j', c j (A (u, z)) * (starRingEnd ℂ) (c' j' (A' (u', z))) *
        mainTerm j j' Tp (imaginaryParameter F _ (e (A (u, z))))
          (imaginaryParameter F _ (e' (A' (u', z)))) ∂ν₁' ∂ν₁ ∂(volume : Measure (Fin m → ℝ))
  Tendsto (fun j : ℕ => I ((j : ℝ) • v₀)) atTop
    (𝓝 (∫ x, ∑ t, ∑ j, ∑ a, ∑ j', ∑ l',
        c j x * coeff t j a (imaginaryParameter F _ (e x)) *
          (starRingEnd ℂ) (c' j' (e'.symm (realWeylParameter
            (Standard.leviToParabolic i ν J.roots) (cw t) π' (e x)))) *
          (starRingEnd ℂ) (b' j' l' (weylParameter (Standard.leviToParabolic i ν J.roots)
            (cw t) π' (imaginaryParameter F _ (e x)))) *
          inducedInnerProduct K (hK J').isCompact (Standard.parabolicHom i ν J'.roots)
            (Standard.leviToParabolic i ν J'.roots) μM' e' β' (ψ t j a) (v' j' l')
      ∂(spectralMeasure n)))

end Langlands.Global
