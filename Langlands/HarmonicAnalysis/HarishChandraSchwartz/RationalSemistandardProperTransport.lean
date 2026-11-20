import Langlands.GroupScheme.Rational.SemistandardProperSplitComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaParts

/-! # Preservation of the proper Fourier cutoff under the actual Weyl transports -/

noncomputable section

universe u uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.Association

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ t, (T t).toGrp ⟶ (chosenLeviModel t).scheme)
  (ha : ∀ t, IsSplitComponent (a t))
  [∀ t, ((chosenLeviModel t).splitCenter (a t)).Normal]
  [∀ t, MeasurableSpace (levi t ⧸ (chosenLeviModel t).splitCenter (a t))]
  (mu : ∀ t, Measure (levi t ⧸ (chosenLeviModel t).splitCenter (a t)))
  [∀ t, (mu t).IsHaarMeasure]

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "Section" => RationalSemistandardThetaSection.{u, uV} a ha mu
set_option hygiene false in
local notation "properPart" => rationalSemistandardThetaProperPart.{u, uV} a ha mu

variable (hsplit : SemistandardProperSplitComparisonStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

include hsplit hG hi in
/-- The group-parabolic condition is preserved by an actual full-index
Weyl transport, since it supplies rational conjugacy of the literal Levis. -/
theorem WeylTransports.parabolic_eq_top_iff
    {s t : Theta} {w : relativeWeylGroup i} (h : WeylTransports a ha mu w s t) :
    s.1.parabolic = ⊤ ↔ t.1.parabolic = ⊤ := by
  obtain ⟨n, _, hLevi, _⟩ := h
  exact hsplit F G hG S i hi s.1 t.1 ⟨n.val, hLevi⟩

include hsplit hG hi in
/-- The actual association relation preserves the proper spectral part. -/
theorem Associated.isProper_iff {s t : Theta} (h : Associated a ha mu s t) :
    s.1.IsProper ↔ t.1.IsProper := by
  obtain ⟨w, hw⟩ := h
  exact not_congr (WeylTransports.parabolic_eq_top_iff a ha mu hsplit hG hi hw)

/-- At a pair of associated actual indices, taking the proper part
preserves equality after any two linear evaluations into a common fiber. -/
def ProperPartTransportStatement : Prop :=
  SemistandardProperSplitComparisonStatement.{u} →
    IsConnectedReductive G → IsMaximalSplitTorus i →
    ∀ {s t : Theta}, Associated a ha mu s t →
    ∀ {V : Type uW} [AddCommMonoid V] [Module ℂ V]
      (L : Section s →ₗ[ℂ] V) (R : Section t →ₗ[ℂ] V)
      (q : RationalSemistandardThetaSections.{u, uV} a ha mu),
      L (q s) = R (q t) →
        L (properPart q s) = R (properPart q t)

theorem properPart_transport :
    ProperPartTransportStatement.{u, uV, uW} a ha mu := by
  intro hSplit hRed hMax s t h V _ _ L R q hq
  have hp := Associated.isProper_iff a ha mu hSplit hRed hMax h
  by_cases hs : s.1.IsProper
  · rw [rationalSemistandardThetaProperPart_apply_of_mem hs,
      rationalSemistandardThetaProperPart_apply_of_mem (hp.mp hs)]
    exact hq
  · rw [rationalSemistandardThetaProperPart_apply_of_not_mem hs,
      rationalSemistandardThetaProperPart_apply_of_not_mem (mt hp.mpr hs), map_zero, map_zero]

end Langlands.HarishChandraSchwartz.RationalSemistandard.Association
