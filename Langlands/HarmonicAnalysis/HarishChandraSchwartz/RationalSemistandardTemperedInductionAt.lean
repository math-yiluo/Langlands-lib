import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardTemperedInduction
import Langlands.BruhatTits.SpecialCompact.SemistandardParabolicSplitting

/-! # Tempered induction at the prescribed semistandard compact -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact
open Langlands.GroupScheme Langlands.Plancherel

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
  {p : SemistandardSpectralIndex i}
  (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (C : Subgroup (levi p)) [C.Normal] (hC : C ≤ Subgroup.center (levi p))
  [MeasurableSpace (levi p ⧸ C)] (μC : Measure (levi p ⧸ C)) [μC.IsHaarMeasure]

/-- Square-integrability modulo a central subgroup gives tempered
coefficients after induction from the actual semistandard parabolic, at the
prescribed special compact and closed matrix height. -/
def TemperedInductionAtStatement [BorelSpace (levi p ⧸ C)] : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
  SpecialCompactProperties F i ν K.toSubgroup → IsClosedSubgroup ρ →
  IsSquareIntegrableModCentralSubgroup C hC A.obj.representation μC →
  HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) ρ)
    ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation

end Langlands.HarishChandraSchwartz.RationalSemistandard
