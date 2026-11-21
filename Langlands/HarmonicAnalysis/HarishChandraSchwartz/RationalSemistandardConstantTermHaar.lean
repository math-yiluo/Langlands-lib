import Mathlib.MeasureTheory.Measure.Haar.Unique
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSemistandardComparison

/-! # Haar normalization in the constant-term detection of VIII.2.1 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2

private theorem semistandardConstantTermInd_eq_zero_of_haar
    (p : SemistandardSpectralIndex i) (f : rationalPoints G → ℂ)
    (g : rationalPoints G × rationalPoints G)
    (muU nuU : Measure p.radical.rationalPointSubgroup) [muU.IsHaarMeasure] [nuU.IsHaarMeasure]
    (h : constantTermInd muU (semistandardUnipotentModulus p) f g = 0) :
    constantTermInd nuU (semistandardUnipotentModulus p) f g = 0 := by
  let : LocallyCompactSpace p.radical.rationalPointSubgroup :=
    (isClosed_semistandardRadicalPoints p).locallyCompactSpace
  let : SecondCountableTopology p.radical.rationalPointSubgroup :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hscale := Measure.isMulLeftInvariant_eq_smul nuU muU
  funext m
  have hm := congrFun h m
  rw [Pi.zero_apply] at hm ⊢
  unfold constantTermInd constantTerm at hm ⊢
  rw [hscale, integral_smul_nnreal_measure, mul_smul_comm, hm, smul_zero]

variable {nu : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))

/-- In the constant-term detection step it suffices to use one radical Haar
measure per proper parabolic, for all translates at that parabolic. -/
def RationalSemistandardCuspidalFromConstantTermHaarStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i nu →
  RationalCuspidalSemistandardComparisonStatement.{u} → IsClosedSubgroup rho →
  ∀ f : RationalSchwartzSpace hKc hPK rho,
    (∀ p : SemistandardSpectralIndex i, p.parabolic ≠ ⊤ →
      ∃ muU : Measure p.radical.rationalPointSubgroup, muU.IsHaarMeasure ∧
        ∀ g : rationalPoints G × rationalPoints G,
          constantTermInd muU (semistandardUnipotentModulus p) f g = 0) →
    f ∈ rationalCuspidalSubmodule hKc hPK rho

theorem rationalSemistandardCuspidalFromConstantTermHaar :
    RationalSemistandardCuspidalFromConstantTermHaarStatement hKc hPK rho := by
  intro hG hi hnu hcompare hrho f hvanish
  apply (hcompare F G hG S i hi nu hnu K hKc hPK N rho hrho f).mpr
  intro p hp nuU hnuU g
  obtain ⟨muU, hmuU, hterm⟩ := hvanish p hp
  let := hmuU
  let := hnuU
  exact semistandardConstantTermInd_eq_zero_of_haar p f g muU nuU (hterm g)

end Langlands.HarishChandraSchwartz
