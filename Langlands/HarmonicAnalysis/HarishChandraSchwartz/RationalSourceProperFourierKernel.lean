import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierDetection
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSourceFourierRank

/-! # The proper Fourier kernel at source normalization -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact
open Langlands.GroupScheme Langlands.Haar Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

open RationalSemistandard RationalSemistandard.FourierInversion

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {ν : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ r, (Z r).toGrp ⟶ (chosenLeviModel r).scheme) (ha : ∀ r, IsSplitComponent (a r))
  [∀ r, ((chosenLeviModel r).splitCenter (a r)).Normal]
  [∀ r, MeasurableSpace (levi r ⧸ (chosenLeviModel r).splitCenter (a r))]
  (μR : ∀ r, Measure (levi r ⧸ (chosenLeviModel r).splitCenter (a r)))
  [∀ r, (μR r).IsHaarMeasure] [∀ r, (μR r).IsInvInvariant]
  (d : ∀ r : SemistandardSpectralIndex i, CompactData r)

set_option maxRecDepth 4096 in
/-- The proper Fourier truncation at the source compact has the intrinsic
cuspidal kernel, given Fourier injectivity on strictly smaller ranks. -/
def SourceProperFourierKernelStatement
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) [∀ r, BorelSpace (levi r ⧸ (chosenLeviModel r).splitCenter (a r))]
    (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
      (rationalXi hK hPK) (rationalHeight (F := F) ρ))
    (hT : ∀ (r : SemistandardSpectralIndex i)
      (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi r)),
      IsSquareIntegrableModCentralSubgroup ((chosenLeviModel r).splitCenter (a r))
        ((chosenLeviModel r).splitCenter_le_center (a r) (ha r)) A.obj.representation (μR r) →
        HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) ρ)
          ((normalizedInductionFunctor (decomposition r) (isClosed_radical r)).obj A.obj).representation) : Prop :=
  IsClosedSubgroup ρ → WeakExpansion.IsSpecialVertexCompact ν hi K →
  (∀ r, (d r).compact = K) →
  (∀ r, μR r = (chosenLeviModel r).sourceQuotientHaar (a r) K hK) →
  RationalStrictlyLowerRankSourceFourierInjectivityStatement.{u, uV} (relativeRootRank i) →
  letI := sourceAmbientHaar_isMulRightInvariant hG hK
  ∀ f : RationalSchwartzSpace hK hPK ρ,
    rationalSemistandardProperFourier hG hi hν hK hPK ρ hsw a ha μR d
        (rationalSemistandardModularNormalization hG hi) hT f = 0 ↔
      f ∈ rationalCuspidalSubmodule hK hPK ρ

end Langlands.HarishChandraSchwartz
