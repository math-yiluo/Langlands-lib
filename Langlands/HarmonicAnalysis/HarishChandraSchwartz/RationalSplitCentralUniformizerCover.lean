import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCenterCompactRemainder
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelCartanCover
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # The actual split-central uniformizer cover from the joint structural input -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise BigOperators
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact Langlands.QuotientIntegration
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (s : T.toGrp ⟶ G)

/-- The required quotient cover with actual dominant uniformizer powers in
`G¹`, one compact open left factor, and one compact right factor. -/
def RationalSplitCentralUniformizerCover : Prop :=
  ∃ H : OpenSubgroup (rationalPoints G), IsCompact (H : Set (rationalPoints G)) ∧
    ∃ Y : Set (rationalPoints G), IsCompact Y ∧
      ∀ q : LeftQuotient (rationalPoints.map s).range,
        ∃ y : cocharacterLattice S,
          (∀ β : SimpleRoot i ν, 0 ≤ simpleRootPairing i ν β y) ∧
          uniformizerPowers i (.ofAdd y) ∈ Plancherel.rationalCommonNormKernel G ∧
          q ∈ leftQuotientMap (rationalPoints.map s).range ''
            ((H : Set (rationalPoints G)) * {uniformizerPowers i (.ofAdd y)} * Y)

variable {i ν s}

/-- The joint geometric existence statement supplies the actual split-central
cover. The joint structural premise is retained rather than inferred from the
simultaneous basis alone. -/
theorem rationalSplitCentralUniformizerCover_of_jointSpecialCompactBasis
    [LocallyOfFiniteType G.X.hom]
    (hjoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hs : IsSplitComponent s) :
    RationalSplitCentralUniformizerCover i ν s := by
  classical
  let := hi.isSplitSubtorus.mono
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype (SimpleRoot i ν) := hfinite.fintype
  obtain ⟨d⟩ := nonempty_normKernelFundamentalCocharacters hG hi hν standardCocharacter
    (relativeRootSystem F G hG S i hi)
  obtain ⟨D, x, Z, j, s0, -, -, hsj, h, -, hprops, -, -, hcartan, -, hcompat, -⟩ :=
    hjoint F G hG S i hi ν hν
  have hlat := hcartan.2
  obtain ⟨F0, hF0, -⟩ := hlat.2.2.2.1
  obtain ⟨R, hR, hfactor⟩ := d.exists_finite_centralCartanFactorization
    hG hi hν standardCocharacter D x j s0 h hsj hcompat hF0
  let H : OpenSubgroup (rationalPoints G) := ⟨D.specialCompactSubgroup x, hprops.2.1.2.1⟩
  have hH : IsCompact (H : Set (rationalPoints G)) := hprops.2.1.1
  let a : (SimpleRoot i ν → ℕ) → rationalPoints G :=
    fun n => (d.orthantHom (.ofAdd n)).val
  have hcover : ∀ g : rationalPoints G, ∃ n : SimpleRoot i ν → ℕ,
      ∃ k ∈ (H : Set (rationalPoints G)),
      ∃ y ∈ R * (H : Set (rationalPoints G)),
      ∃ z ∈ Subgroup.center (rationalPoints G), g = k * a n * y * z := by
    intro g
    obtain ⟨n, k1, hk1, t, ht, k2, hk2, z, hz, hg⟩ := hfactor g
    exact ⟨n, k1, hk1, t * k2, ⟨t, ht, k2, hk2, rfl⟩, z, hz,
      by simpa only [mul_assoc] using hg⟩
  obtain ⟨Y, hY, hQcover⟩ := exists_rationalSplitCentralQuotient_cover_of_central_cover
    hG s hs a (H : Set (rationalPoints G)) (hR.isCompact.mul hH) hcover
  refine ⟨H, hH, Y, hY, fun q => ?_⟩
  obtain ⟨n, hn⟩ := hQcover q
  refine ⟨d.orthantCocharacter n, ?_, d.orthant_mem_normKernel n, hn⟩
  intro β
  change 0 ≤ latticePairing S β.val (d.orthantCocharacter n)
  rw [d.pair_orthantCocharacter]
  exact mul_nonneg (Nat.cast_nonneg _) (d.pair_pos β).le

end Langlands.HarishChandraSchwartz
