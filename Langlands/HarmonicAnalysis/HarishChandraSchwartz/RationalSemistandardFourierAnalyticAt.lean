import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacket

/-! # Analytic inputs for semistandard Fourier evaluation at the source compact -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact
open Langlands.GroupScheme Langlands.Haar Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

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
  {p : SemistandardSpectralIndex i} (m : LeviModel p) (d : CompactData p)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (C : Subgroup (levi p)) [C.Normal] (hC : C ≤ Subgroup.center (levi p))
  [MeasurableSpace (levi p ⧸ C)]
  (μC : Measure (levi p ⧸ C)) [μC.IsHaarMeasure]

/-- The analytic input package for the actual semistandard Fourier evaluation
exists at the source compact for every square-integrable inducing orbit. The
Levi and radical measures are normalized on their literal compact traces. -/
def FourierAnalyticAtStatement [BorelSpace (levi p ⧸ C)] : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
  SpecialCompactProperties F i ν K.toSubgroup → IsClosedSubgroup ρ → d.compact = K →
  IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μC →
    ∃ ΞL : levi p → ℝ,
      RationalSemistandardFourierAnalyticInputs (muG := RationalDynamicSource.ambientHaar K hK)
        hK hPK ρ p m d π (subgroupCompactOpenHaar K hK (levi p) (isClosed_levi_of_model m))
        (subgroupCompactOpenHaar K hK (radical p) (isClosed_radical p)) ΞL
        (fun x => rationalHeight (F := F) ρ (x : rationalPoints G))

end Langlands.HarishChandraSchwartz.RationalSemistandard
