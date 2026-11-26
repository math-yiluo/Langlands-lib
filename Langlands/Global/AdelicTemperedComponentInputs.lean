import Langlands.Global.AdelicCyclicDistributionVectorReduction

/-! # Summability of the logarithmic height and local smoothing on `G(𝔸)`

Three propositions about a connected reductive group `G` over a number field `F`, for the
construction of irreducible representations with tempered `G(F)`-invariant distribution vectors in
`CyclicIrreducibleDistributionVectorStatement`.

The first proposition bounds a weighted conjugation count on the rational quotient. The other
two give a local Sobolev identity for smooth vectors and a Gårding approximation on `G(𝔸)`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Archimedean

/-- Counting form of log-height summability on `[G]`, derived from Bernstein 1988, §§3.2–3.4,
and Delorme 2023, (2.10) and Remark 3.4. There is a single `m : ℕ` such that for every compact
`C ⊆ G(𝔸)` the lower integral of `#{q ∈ G(F) : x⁻¹ q x ∈ C} · σ_{[G]}(y)^{-2m}` over `[G]`
is finite. Here `x = y.out`, the count is `Set.encard`, and
`σ_{[G]} = rationalLogHeight F G rho`. Unfolding relates the count to the reciprocal volume
of a quotient ball, the density of Bernstein's standard measure. -/
def RationalQuotientSummableLogHeightStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N : ℕ} (rho : MatrixRepresentation G (Fin N)),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    let μG : Measure (RationalQuotient F G) :=
      LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
        (isDiscrete_rationalSubgroup F G) Measure.haar
    ∃ m : ℕ, ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
      ∫⁻ y, (({q : AdelicGroupPoints F G | q ∈ rationalSubgroup F G ∧
          y.out⁻¹ * q * y.out ∈ C}.encard : ℕ∞) : ℝ≥0∞) *
        ENNReal.ofReal ((rationalLogHeight F G rho y ^ (2 * m))⁻¹) ∂μG < ∞

/-- A local Sobolev identity on `G(𝔸)`, derived using the one-parameter method of Dixmier and
Malliavin 1978, §§2 and 3, and related to Bernstein 1988, §3.4, Key Lemma.
For every open subgroup `L` of `G(𝔸_f)` there are a finite set `S` of words
`[X₁, …, Xₖ]` in the model space of `G(F_∞)` and bounded measurable compactly supported functions
`φ_a : G(𝔸) → ℂ` (`a ∈ S`) such that for every jointly continuous representation `ρ` of `G(𝔸)` on
a complex Banach space `E` and every `v ∈ E` that is a smooth vector of the restriction of `ρ` to
`G(F_∞)` and is fixed by `ρ(L)`, one has
`v = ∑_{a ∈ S} ∫_{G(𝔸)} φ_a(g) ρ(g) (dρ(a) v) dg`, where `dρ(a) v` is
`Langlands.Archimedean.iteratedLieDerivative` and `dg` is `Measure.haar`. -/
def AdelicSmoothVectorParametrixStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    ∀ L : Subgroup (FiniteAdelicGroupPoints F G), IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
    ∃ (S : Finset (List (InfiniteAdelicGroupPoints.smoothModel F d)))
      (φ : List (InfiniteAdelicGroupPoints.smoothModel F d) → AdelicGroupPoints F G → ℂ),
      (∀ a ∈ S, Measurable (φ a) ∧ (∃ C : ℝ, ∀ g, ‖φ a g‖ ≤ C) ∧ HasCompactSupport (φ a)) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
        (ρ : AdelicGroupPoints F G →* (E →L[ℂ] E)), IsContinuousRepresentation ρ →
        ∀ v ∈ Langlands.Archimedean.smoothVectors
            𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) (ρ.comp (ofInfinite F G).toMonoidHom),
          (∀ l ∈ L, ρ (ofFinite F G l) v = v) →
          v = ∑ a ∈ S, ∫ g, φ a g • ρ g (Langlands.Archimedean.iteratedLieDerivative
            𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) (ρ.comp (ofInfinite F G).toMonoidHom)
            a v) ∂(Measure.haar : Measure (AdelicGroupPoints F G))

/-- Gårding's smoothing on `G(𝔸)` (L. Gårding, *Note on continuous representations of Lie
groups*, 1947, with the idempotents of open compact subgroups of `G(𝔸_f)`). There is a sequence
of bounded measurable compactly supported functions `ψ_n : G(𝔸) → ℂ` such that for every jointly
continuous representation `ρ` of `G(𝔸)` on a complex Banach space `E` and every `u ∈ E`: each
`ρ(ψ_n) u = ∫ ψ_n(g) ρ(g) u dg` is a smooth vector of the restriction of `ρ` to `G(F_∞)` and is
fixed by `ρ(L)` for some open subgroup `L` of `G(𝔸_f)`, and `ρ(ψ_n) u → u`. -/
def AdelicGardingApproximationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    ∃ ψ : ℕ → AdelicGroupPoints F G → ℂ,
      (∀ n, Measurable (ψ n) ∧ (∃ C : ℝ, ∀ g, ‖ψ n g‖ ≤ C) ∧ HasCompactSupport (ψ n)) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
        (ρ : AdelicGroupPoints F G →* (E →L[ℂ] E)), IsContinuousRepresentation ρ → ∀ u : E,
        (∀ n, (∫ g, ψ n g • ρ g u ∂(Measure.haar : Measure (AdelicGroupPoints F G))) ∈
            Langlands.Archimedean.smoothVectors
              𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d)
              (ρ.comp (ofInfinite F G).toMonoidHom) ∧
          ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
            IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧ ∀ l ∈ L,
              ρ (ofFinite F G l) (∫ g, ψ n g • ρ g u
                ∂(Measure.haar : Measure (AdelicGroupPoints F G))) =
              ∫ g, ψ n g • ρ g u ∂(Measure.haar : Measure (AdelicGroupPoints F G))) ∧
        Filter.Tendsto (fun n => ∫ g, ψ n g • ρ g u
          ∂(Measure.haar : Measure (AdelicGroupPoints F G))) Filter.atTop (nhds u)

end Langlands.Global
