import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalInverse
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrability
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Convolution
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.L2
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionStatement
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Aubert.General.RationalStandardParabolicTransport
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.Representation.Plancherel.RationalTwistStabilizer

/-! # Lemmas II.1.4 and II.1.5 of Waldspurger on actual rational points

For a connected reductive group `G` over a nonarchimedean local field `F`, a maximal split torus,
a generic cocharacter and a compact open subgroup `K` with `G(F) = P₀(F) K`, the spherical
function `Ξ = rationalXi` of `RationalWeights` satisfies `Ξ(g⁻¹) = Ξ(g)` (Lemma II.1.4,
`rationalXi_inv`). `RationalXiSquareIntegrableStatement` states Lemma II.1.5 for `Ξ` and the
height `σ = rationalHeight ρ` of a closed matrix representation, conditionally on the structural
inputs of Renard V.5.1 (covering clause of the Cartan decomposition) and V.5.2 (simultaneous
standard basis). Given its conclusion, the actual weights satisfy the Library's hypotheses
`L2Weights` and `ConvolutionWeights` (when `ρ(K) ⊆ GL_n(𝒪)`), so the generic `L²` pairing and
the convolution of Lemma III.6.1 apply to the actual `C(G)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- **Waldspurger, Lemme II.1.5** (printed p. 252) on actual rational points (statement). Let
`F` be a nonarchimedean local field and `G` a connected reductive group over `F`, with a maximal
split torus `i : S → G` and a generic cocharacter `ν` (the minimal standard parabolic
`P₀ = P_∅`). Assume, for one compact open subgroup `K0`, Renard's V.5.2 simultaneous standard
basis (`SimultaneousStandardBasisAt`) and the covering clause of the Cartan decomposition of
Renard V.5.1 (4) (`FiniteCartanCovering`), both external structural inputs. Let `K` be a compact
open subgroup with `G(F) = P₀(F) K` and `ρ` a closed matrix representation. Then there is `d ∈ ℕ`
with `∫_G Ξ(g)² (1 + σ(g))^{-d} dμ(g) < ∞` for every Haar measure `μ` of `G(F)`, where
`Ξ = rationalXi` and `σ = rationalHeight ρ`. -/
def RationalXiSquareIntegrableStatement : Prop :=
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
    ∀ (mu : Measure (rationalPoints G)) [mu.IsHaarMeasure],
      SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSquareSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalSquareT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance rationalSquareNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

section Inverse

/-- The actual rational points of a connected reductive group are unimodular (the Library's
`rationalReductiveUnimodularity`). -/
theorem rationalPoints_modularCharacter_eq_one (hG : IsConnectedReductive G)
    (g : rationalPoints G) : Measure.modularCharacter g = 1 :=
  Aubert.General.RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual minimal standard parabolic `P₀(F)` is closed. -/
theorem isClosed_standardParabolicPoints_empty (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    IsClosed (standardParabolicPoints i ν ∅ : Set (rationalPoints G)) := by
  have := hi.isSplitSubtorus.mono
  have h := Aubert.General.RationalPointFamily.isClosed_standard_parabolic i ν
    standardCocharacter hG hi hν ∅
  change IsClosed (standardParabolicPoints i ν
    (Aubert.General.RationalPointFamily.rootSet i ν ∅) : Set (rationalPoints G)) at h
  rwa [Aubert.General.RationalPointFamily.rootSet_empty] at h

/-- Transport of an identity between the modular character of `P_J(F)` and the Haar modulus of
conjugation on `U_J(F)` along an equality `J = ∅`. -/
theorem rationalMinimalModulus_eq_of_eq_empty {J : Set (characterLattice S)} (hJ : J = ∅)
    (hU : IsClosed (standardUnipotentPoints i ν J : Set (rationalPoints G)))
    (hle : standardParabolicPoints i ν J ≤
      Subgroup.normalizer (standardUnipotentPoints i ν J : Set (rationalPoints G)))
    (hLC : LocallyCompactSpace (standardParabolicPoints i ν J))
    (h : ∀ p : standardParabolicPoints i ν J, Measure.modularCharacter p =
      (HaarModulus.closedRestrictCharacter (standardUnipotentPoints i ν J) hU
        (standardParabolicPoints i ν J) hle p : ℝ≥0))
    [LocallyCompactSpace (standardParabolicPoints i ν ∅)]
    (p : standardParabolicPoints i ν ∅) :
    (rationalMinimalModulus i ν p : ℝ≥0) = Measure.modularCharacter p := by
  subst hJ
  exact (h p).symm

/-- For connected reductive `G`, `δ₀` is Mathlib's modular character of the locally compact
group `P₀(F)`: the case `I = ∅` of the Library's `RationalParabolicModulusStatement`, proved by
`rationalParabolicModulus_of_reductiveUnimodularity`. -/
theorem rationalMinimalModulus_eq_modularCharacter (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    [LocallyCompactSpace (standardParabolicPoints i ν ∅)]
    (p : standardParabolicPoints i ν ∅) :
    (rationalMinimalModulus i ν p : ℝ≥0) = Measure.modularCharacter p := by
  have := hi.isSplitSubtorus.mono
  have hmod := Aubert.General.RationalPointFamily.rationalParabolicModulus_of_reductiveUnimodularity
    Aubert.General.RationalPointFamily.rationalReductiveUnimodularity
    GroupScheme.dynamicCentralizerReductive
  have hU := isClosed_standardUnipotentPoints i ν
    (Aubert.General.RationalPointFamily.rootSet i ν ∅)
  have hP := Aubert.General.RationalPointFamily.isClosed_standard_parabolic i ν
    standardCocharacter hG hi hν ∅
  have hc := Aubert.General.RationalPointFamily.continuous_standard_projection i ν
    standardCocharacter hG hi hν ∅
  have h := (hmod F G hG S i hi ν hν standardCocharacter ∅ hU hP hc).2
  exact rationalMinimalModulus_eq_of_eq_empty
    (Aubert.General.RationalPointFamily.rootSet_empty i ν) hU _ hP.locallyCompactSpace h p

/-- **Waldspurger, Lemme II.1.4** (printed p. 252) on actual rational points: `Ξ(g⁻¹) = Ξ(g)`
for connected reductive `G`. The Library's generic `xi_inv` applies, since `G(F)` is unimodular
and `δ₀` is the modular character of `P₀(F)`. -/
theorem rationalXi_inv (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {K : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K) (g : rationalPoints G) :
    rationalXi hKc hPK g⁻¹ = rationalXi hKc hPK g := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hP := isClosed_standardParabolicPoints_empty hG hi hν
  have : LocallyCompactSpace (standardParabolicPoints i ν ∅) := hP.locallyCompactSpace
  exact xi_inv (rationalPoints_modularCharacter_eq_one hG) hP hKo
    (rationalMinimalModulus_eq_modularCharacter hG hi hν) g

end Inverse

section Weights

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n)

include hKo in
/-- The conclusion of Lemma II.1.5 gives the Library's `L2Weights` for the actual `Ξ` and `σ`:
the `L²` pairing `(f₁, f₂)_G = ∫_G conj(f₁) f₂` converges on `C(G)`
(`L2Weights.integrable_conj_mul`). -/
theorem rationalL2Weights {mu : Measure (rationalPoints G)}
    (hsq : SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ)) :
    L2Weights mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ) := by
  obtain ⟨d, hd⟩ := hsq
  exact ⟨rationalXi_pos hKo hKc hPK, rationalHeight_nonneg ρ, ⟨d, hd⟩⟩

include hKo in
/-- For connected reductive `G` and `ρ(K) ⊆ GL_n(𝒪)` (Waldspurger's `τ(K) ⊂ GL_n(𝒪)`, I.1), the
conclusion of Lemma II.1.5 gives the Library's `ConvolutionWeights` for the actual `Ξ` and `σ`,
the hypotheses of the convolution theorem III.6.1 on `C(G)`: positivity and continuity,
`1 + σ(g) ≤ (1 + σ(h))(1 + σ(h⁻¹ g))`, left `K`-invariance, Lemma II.1.4 (`rationalXi_inv`),
Lemma II.1.3 (`integral_rationalXi_mul_mul`) and Lemma II.1.5. -/
theorem rationalConvolutionWeights (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) [CompactSpace K]
    (hKρ : K ≤ rationalHeightSubgroup (F := F) ρ) {mu : Measure (rationalPoints G)}
    (hsq : SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ)) :
    ConvolutionWeights mu K (rationalXi hKc hPK) (rationalHeight (F := F) ρ) where
  pos := rationalXi_pos hKo hKc hPK
  nonneg := rationalHeight_nonneg ρ
  continuous_xi := continuous_rationalXi hKo hKc hPK
  continuous_sigma := continuous_rationalHeight ρ
  one_add_le := one_add_le_of_le_add (rationalHeight_nonneg ρ) (rationalHeight_mul_le ρ)
  xi_mul_left k hk g := by
    simpa only [mul_one] using rationalXi_mul_mul hKo hKc hPK hk K.one_mem g
  sigma_mul_left k hk g := by
    simpa only [mul_one] using
      rationalHeight_mul_mul ρ (hKρ hk) (rationalHeightSubgroup (F := F) ρ).one_mem g
  xi_inv := rationalXi_inv hG hi hν hKo hKc hPK
  integral_xi := integral_rationalXi_mul_mul hKo hKc hPK
  square := hsq

end Weights

/-- `RationalXiSquareIntegrableStatement` in the Library's `L2Weights` form, for every Haar
measure `μ` of `G(F)`. -/
theorem RationalXiSquareIntegrableStatement.l2Weights
    (h : RationalXiSquareIntegrableStatement.{u}) (hG : IsConnectedReductive G)
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
    (mu : Measure (rationalPoints G)) [mu.IsHaarMeasure] :
    L2Weights mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ) :=
  rationalL2Weights hKo hKc hPK ρ
    (h F G hG S i hi ν hν K0 hK0o hK0c hbasis hcover K hKo hKc hPK N ρ hρ mu)

/-- `RationalXiSquareIntegrableStatement` in the Library's `ConvolutionWeights` form, for every
Haar measure `μ` of `G(F)`, when `ρ(K) ⊆ GL_n(𝒪)`. -/
theorem RationalXiSquareIntegrableStatement.convolutionWeights
    (h : RationalXiSquareIntegrableStatement.{u}) (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {K0 : Subgroup (rationalPoints G)}
    (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G))) [CompactSpace K]
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)} (hρ : IsClosedSubgroup ρ)
    (hKρ : K ≤ rationalHeightSubgroup (F := F) ρ)
    (mu : Measure (rationalPoints G)) [mu.IsHaarMeasure] :
    ConvolutionWeights mu K (rationalXi hKc hPK) (rationalHeight (F := F) ρ) :=
  rationalConvolutionWeights hKo hKc hPK ρ hG hi hν hKρ
    (h F G hG S i hi ν hν K0 hK0o hK0c hbasis hcover K hKo hKc hPK N ρ hρ mu)

end Langlands.HarishChandraSchwartz
