import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalRankZeroFourierInjectivityProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardModularNormalizationProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceQuotientHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets

/-! # Fourier injectivity by rank at the source compact and measures -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

open RationalSemistandard RationalSemistandard.FourierInversion

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

set_option maxRecDepth 4096 in
/-- The zero case of VIII.1 (2) at a single source special compact and its
Haar measures, using a closed matrix height. This scope is stable under
restriction to an actual semistandard Levi. -/
def RationalLocalSourceFourierInjectivityStatement
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] : Prop :=
  ∀ (hG : IsConnectedReductive G) (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup),
    WeakExpansion.IsSpecialVertexCompact ν hi K →
    ∀ (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∀ (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
        (rationalXi hK hPK) (rationalHeight (F := F) ρ))
      (T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F)))
      (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme) (ha : ∀ p, IsSplitComponent (a p))
      [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
      [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
      [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
      (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
      [∀ p, (mu p).IsHaarMeasure] [∀ p, (mu p).IsInvInvariant]
      (d : ∀ p : SemistandardSpectralIndex i, CompactData p),
      (∀ p, (d p).compact = K) →
      (∀ p, mu p = (chosenLeviModel p).sourceQuotientHaar (a p) K hK) →
      ∀ (hT : ∀ (p : SemistandardSpectralIndex i)
        (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
        IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
          ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (mu p) →
        HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) ρ)
          ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation),
        letI := sourceAmbientHaar_isMulRightInvariant hG hK
        FourierInjectivityStatement hG hi hν hK hPK ρ hsw a ha mu d
          (rationalSemistandardModularNormalization hG hi) hT

/-- The source-normalized zero case holds on all connected reductive
groups of strictly smaller relative semisimple rank. -/
def RationalStrictlyLowerRankSourceFourierInjectivityStatement (n : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    relativeRootRank i < n → RationalLocalSourceFourierInjectivityStatement.{u, uV} G

set_option maxRecDepth 4096 in
/-- Specialize the existing injectivity statement to the source Haar,
compact pictures and closed matrix height. -/
theorem RationalLocalFourierInjectivityStatement.atSource
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (h : RationalLocalFourierInjectivityStatement.{u, uV} G) :
    RationalLocalSourceFourierInjectivityStatement.{u, uV} G := by
  intro hG S i hi ν hν K hK hPK _ N _ ρ _ hsw T a ha _ _ _ mu _ _ d _ _ hT
  let := sourceAmbientHaar_isMulRightInvariant hG hK
  exact h hG S i hi ν hν K hK hPK N ρ (RationalDynamicSource.ambientHaar K hK)
    hsw T a ha mu d (rationalSemistandardModularNormalization hG hi) hT

/-- Rank zero opens the induction at source normalization. -/
theorem rationalStrictlyLowerRankSourceFourierInjectivity_one :
    RationalStrictlyLowerRankSourceFourierInjectivityStatement.{u, uV} 1 := by
  intro F _ _ _ _ G _ _ hG S i hi hlt
  exact RationalLocalFourierInjectivityStatement.atSource
    (rationalRankZeroFourierInjectivity F G hG S i hi (Nat.lt_one_iff.mp hlt))

end Langlands.HarishChandraSchwartz
