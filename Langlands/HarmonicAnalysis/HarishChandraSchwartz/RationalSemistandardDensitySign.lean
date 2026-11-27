import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm

/-! # Sign of the Plancherel density on the semistandard spectrum -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

open GlobalForm

set_option maxRecDepth 4096 in
/-- The scalar density used in the actual semistandard packets is nonnegative
everywhere and strictly positive on a dense subset of each unitary orbit. -/
def RationalSemistandardDensitySignStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
    (hG : IsConnectedReductive G), IsMaximalSplitTorus i →
    ∀ {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
      (a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme)
      (ha : ∀ p, IsSplitComponent (a p))
      [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
      [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
      [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
      (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
      [∀ p, (mu p).IsHaarMeasure]
      (rs : ∀ p : SemistandardSpectralIndex i, CocharacterPresentation hG p)
      (Q : ∀ θ : RationalSemistandardTheta.{u, uV} a ha mu,
        OrbitPacketData (rs θ.1)
          (orbitRepresentative (chosenLeviModel θ.1) (a θ.1) (ha θ.1) (mu θ.1) θ.2)),
      DensityNonnegative hG a ha mu rs Q ∧ DensityPositiveDense hG a ha mu rs Q

end Langlands.HarishChandraSchwartz.RationalSemistandard
