import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalTemperedInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientCutoff
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalTranslation
import Langlands.Representation.Plancherel.CentralSubgroupCoefficients
import Langlands.Representation.Plancherel.RationalNormKernelTopology

/-! # Corollary III.1.2 and III.7 of Waldspurger on actual rational points

For a connected reductive group `G` over a nonarchimedean local field `F`, this module states
Waldspurger's Corollary III.1.2 for the actual `G(F)`: the coefficients of a representation that
is square integrable modulo the split centre `A_G(F)` decrease rapidly on `G¹` relative to
`Ξ = rationalXi` and `σ = rationalHeight ρ` (`RationalSquareIntegrableRapidDecayStatement`,
conditional on the structural inputs of Renard V.5.1 and V.5.2, as Lemma II.1.5). It proves
Lemma II.1.2 for the actual `Ξ` and the translation bound for `σ` (`rationalTranslationWeights`),
the independence of rapid decay from the closed matrix representation, and the second paragraph
of III.7 on actual points: a coefficient with rapidly decreasing coefficients, multiplied by a
compactly supported function on `G(F)/G¹`, lies in `C(G)`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section Abstract

variable {X : Type*} [Group X] {Ξ σ σ' : X → ℝ}

/-- For `x, y > 0` with `x ≤ D y` and `y ≤ D x` (`D ≥ 1`), `y ^ t ≤ D ^ |t| x ^ t` for every
real `t`. -/
theorem rpow_le_rpow_abs_mul_of_le {x y D : ℝ} (hx : 0 < x) (hy : 0 < y) (hD : 1 ≤ D)
    (hxy : x ≤ D * y) (hyx : y ≤ D * x) (t : ℝ) : y ^ t ≤ D ^ |t| * x ^ t := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht, ← Real.mul_rpow hD0.le hx.le]
    exact Real.rpow_le_rpow hy.le hyx ht
  · have h1 : x / D ≤ y := by rw [div_le_iff₀ hD0]; linarith
    have h2 : y ^ t ≤ (x / D) ^ t :=
      Real.rpow_le_rpow_of_nonpos (div_pos hx hD0) h1 ht.le
    rw [Real.div_rpow hx.le hD0.le, div_eq_mul_inv, ← Real.rpow_neg hD0.le] at h2
    rw [abs_of_neg ht, mul_comm]
    exact h2

/-- Rapid decay on `N` does not change when the height `σ'` is replaced by a comparable height
`σ`: `1 + σ' ≤ C (1 + σ)` and `1 + σ ≤ C (1 + σ')`. -/
theorem IsRapidlyDecreasingOn.of_one_add_le {N : Subgroup X} {f : X → ℂ}
    (hΞ : ∀ g, 0 ≤ Ξ g) (hσ : ∀ g, 0 ≤ σ g) (hσ' : ∀ g, 0 ≤ σ' g) {C : ℝ}
    (hC : ∀ g, 1 + σ' g ≤ C * (1 + σ g)) (hC' : ∀ g, 1 + σ g ≤ C * (1 + σ' g))
    (h : IsRapidlyDecreasingOn Ξ σ' N f) : IsRapidlyDecreasingOn Ξ σ N f := by
  intro r
  obtain ⟨c, hc⟩ := h r
  set D := max C 1
  have hD : 1 ≤ D := le_max_right _ _
  refine ⟨max c 0 * D ^ |(-r)|, fun n hn => ?_⟩
  have hx : 0 < 1 + σ n := by linarith [hσ n]
  have hy : 0 < 1 + σ' n := by linarith [hσ' n]
  have hxy : 1 + σ n ≤ D * (1 + σ' n) :=
    (hC' n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hy.le)
  have hyx : 1 + σ' n ≤ D * (1 + σ n) :=
    (hC n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx.le)
  have key := rpow_le_rpow_abs_mul_of_le hx hy hD hxy hyx (-r)
  have hc0 : 0 ≤ max c 0 := le_max_right _ _
  calc ‖f n‖ ≤ c * Ξ n * (1 + σ' n) ^ (-r) := hc n hn
    _ ≤ max c 0 * Ξ n * (1 + σ' n) ^ (-r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (hΞ n))
          (Real.rpow_nonneg hy.le _)
    _ ≤ max c 0 * Ξ n * (D ^ |(-r)| * (1 + σ n) ^ (-r)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hc0 (hΞ n))
    _ = max c 0 * D ^ |(-r)| * Ξ n * (1 + σ n) ^ (-r) := by ring

end Abstract

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance rationalDecaySecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalDecayT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance rationalDecayNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

section Translation

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n)

include hKo in
/-- **Waldspurger, Lemma II.1.2** (printed p. 251) for the actual `Ξ`, with exponent `d = 0`:
for all `g₁, g₂ ∈ G(F)` there is `C` with `Ξ(g₁ g g₂) ≤ C Ξ(g)` for all `g` (the Library's
`xi_uniformTranslationBound`). -/
theorem rationalXi_uniformTranslationBound :
    UniformTranslationBound (rationalXi hKc hPK) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact xi_uniformTranslationBound (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp)
    hKo

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Two-sided translations change `1 + σ` by a bounded factor, since `σ` is subadditive. -/
theorem rationalHeightTranslationBound :
    HeightTranslationBound (rationalHeight (F := F) ρ) :=
  heightTranslationBound_of_le_add (rationalHeight_nonneg ρ) (rationalHeight_mul_le ρ)

include hKo in
/-- The actual `Ξ` and `σ` satisfy the Library's `TranslationWeights`: `Ξ > 0`, `σ ≥ 0`,
Lemma II.1.2 and the translation bound for `σ`. -/
theorem rationalTranslationWeights :
    TranslationWeights (rationalXi hKc hPK) (rationalHeight (F := F) ρ) :=
  ⟨rationalXi_pos hKo hKc hPK, rationalHeight_nonneg ρ,
    (rationalXi_uniformTranslationBound hKo hKc hPK).translationBound _,
    rationalHeightTranslationBound ρ⟩

end Translation

section Decay

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)

/-- **Independence of the matrix representation**: for closed matrix representations `ρ` and
`ρ'`, the coefficients of `A` decrease rapidly on a subgroup `N` for `σ_ρ` if and only if they
do for `σ_{ρ'}`. -/
theorem hasRapidlyDecreasingCoefficientsOn_rationalHeight_iff {N N' : ℕ} [Nonempty (Fin N)]
    [Nonempty (Fin N')] (ρ : MatrixRepresentation G (Fin N))
    (ρ' : MatrixRepresentation G (Fin N')) (hρ : IsClosedSubgroup ρ)
    (hρ' : IsClosedSubgroup ρ') (L : Subgroup (rationalPoints G))
    (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) :
    HasRapidlyDecreasingCoefficientsOn (rationalXi hKc hPK) (rationalHeight (F := F) ρ) L
        A.representation ↔
      HasRapidlyDecreasingCoefficientsOn (rationalXi hKc hPK) (rationalHeight (F := F) ρ') L
        A.representation := by
  obtain ⟨C₁, hC₁⟩ := exists_one_add_rationalHeight_le ρ' hρ' ρ
  obtain ⟨C₂, hC₂⟩ := exists_one_add_rationalHeight_le ρ hρ ρ'
  have hΞ := rationalXi_nonneg hKc hPK
  set C := max C₁ C₂
  have h₁ : ∀ g, 1 + rationalHeight (F := F) ρ g ≤ C * (1 + rationalHeight (F := F) ρ' g) :=
    fun g => (hC₁ g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by linarith [rationalHeight_nonneg (F := F) ρ' g]))
  have h₂ : ∀ g, 1 + rationalHeight (F := F) ρ' g ≤ C * (1 + rationalHeight (F := F) ρ g) :=
    fun g => (hC₂ g).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by linarith [rationalHeight_nonneg (F := F) ρ g]))
  constructor
  · intro h v ℓ
    exact (h v ℓ).of_one_add_le hΞ (rationalHeight_nonneg ρ') (rationalHeight_nonneg ρ) h₁ h₂
  · intro h v ℓ
    exact (h v ℓ).of_one_add_le hΞ (rationalHeight_nonneg ρ) (rationalHeight_nonneg ρ') h₂ h₁

include hKo in
/-- **Waldspurger III.7** (printed p. 273), second paragraph, on actual rational points: if the
coefficients of the smooth representation `A` of `G(F)` decrease rapidly on `G¹` (the conclusion
of Corollary III.1.2), then for every `f ∈ A(π)` (the range of the coefficient map) and every
compactly supported `φ` on `G(F)/G¹`, the product `g ↦ f(g) φ(g G¹)` lies in `C(G)`. -/
theorem mul_mem_rationalSchwartz {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) {A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)}
    (hD : HasRapidlyDecreasingCoefficientsOn (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
      (Plancherel.rationalCommonNormKernel G) A.representation)
    {f : LocallyConstant (rationalPoints G) ℂ}
    (hf : f ∈ LinearMap.range (Plancherel.coefficientTensorMap A))
    {φ : rationalPoints G ⧸ Plancherel.rationalCommonNormKernel G → ℂ}
    (hφ : HasCompactSupport φ) :
    (fun g => f g * φ g) ∈
      schwartzSubmodule (rationalXi hKc hPK) (rationalHeight (F := F) ρ) := by
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨⟨K, hKo⟩, hKc⟩⟩
  exact (rationalTranslationWeights hKo hKc hPK ρ).mul_mem_schwartzSubmodule
    (Plancherel.isOpen_rationalCommonNormKernel G) hD hf hφ

end Decay

/-- **Waldspurger, Corollaire III.1.2** (printed p. 263) on actual rational points (statement).
Let `F` be a nonarchimedean local field, `G` a connected reductive group over `F` with a maximal
split torus `i : S → G` and a generic cocharacter `ν` (the minimal standard parabolic
`P₀ = P_∅`). Assume, for one compact open subgroup `K0`, Renard's V.5.2 simultaneous standard
basis (`SimultaneousStandardBasisAt`) and the covering clause of the Cartan decomposition of
Renard V.5.1 (4) (`FiniteCartanCovering`), both external structural inputs. Let `K` be a compact
open subgroup with `G(F) = P₀(F) K`, `ρ` a closed matrix representation, `s : T → G` a split
component (image `A_G(F)`) and `mu` a Haar measure on `G(F)/A_G(F)`. Then for every smooth
representation `A` of `G(F)` that is square integrable modulo `A_G(F)` (admissible, with a
unitary central character, every coefficient square integrable on `G(F)/A_G(F)`), every
coefficient `g ↦ ℓ(π(g) v)` decreases rapidly on `G¹`: for every `r` there is `c` with
`|ℓ(π(g) v)| ≤ c Ξ(g) (1 + σ(g))^{-r}` for all `g ∈ G¹`, where `Ξ = rationalXi`,
`σ = rationalHeight ρ` and `G¹ = rationalCommonNormKernel G`. -/
def RationalSquareIntegrableRapidDecayStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ K0 : Subgroup (rationalPoints G), IsOpen (K0 : Set (rationalPoints G)) →
      IsCompact (K0 : Set (rationalPoints G)) → SimultaneousStandardBasisAt i ν K0 →
      Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0 →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s),
      letI := (rationalPoints.map s).range.normal_of_le_center
        hs.isCentralSplitTorus.isCentral.range_le_center
      letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
      ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
        (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
        Plancherel.IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
            hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
          HasRapidlyDecreasingCoefficientsOn (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
            (Plancherel.rationalCommonNormKernel G) A.representation

/-- `RationalSquareIntegrableRapidDecayStatement` applied to one group: under its structural
hypotheses, the coefficients of every representation of `G(F)` that is square integrable modulo
`A_G(F)` decrease rapidly on `G¹`. -/
theorem RationalSquareIntegrableRapidDecayStatement.hasRapidlyDecreasingCoefficientsOn
    (h : RationalSquareIntegrableRapidDecayStatement.{u, uV}) (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)} (hρ : IsClosedSubgroup ρ)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      Plancherel.IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
        HasRapidlyDecreasingCoefficientsOn (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
          (Plancherel.rationalCommonNormKernel G) A.representation :=
  h F G hG S i hi ν hν K0 hK0o hK0c hbasis hcover K hKo hKc hPK N ρ hρ T s hs

/-- **Waldspurger III.7** (printed p. 273), second paragraph, on actual rational points, given
`RationalSquareIntegrableRapidDecayStatement` (Corollary III.1.2) and its structural hypotheses:
for a representation `A` of `G(F)` square integrable modulo `A_G(F)`, every `f ∈ A(π)` and every
compactly supported `φ` on `G(F)/G¹`, the product `g ↦ f(g) φ(g G¹)` lies in `C(G)`. -/
theorem RationalSquareIntegrableRapidDecayStatement.mul_mem_rationalSchwartz
    (h : RationalSquareIntegrableRapidDecayStatement.{u, uV}) (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)} (hρ : IsClosedSubgroup ρ)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      Plancherel.IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
      ∀ {f : LocallyConstant (rationalPoints G) ℂ},
        f ∈ LinearMap.range (Plancherel.coefficientTensorMap A) →
      ∀ {φ : rationalPoints G ⧸ Plancherel.rationalCommonNormKernel G → ℂ},
        HasCompactSupport φ →
        (fun g => f g * φ g) ∈
          schwartzSubmodule (rationalXi hKc hPK) (rationalHeight (F := F) ρ) := by
  intro mu _ A hA f hf φ hφ
  exact _root_.Langlands.HarishChandraSchwartz.mul_mem_rationalSchwartz hKo hKc hPK ρ
    (h.hasRapidlyDecreasingCoefficientsOn hG hi hν hK0o hK0c hbasis hcover hKo hKc hPK hρ hs
      mu A hA) hf hφ

end Langlands.HarishChandraSchwartz
