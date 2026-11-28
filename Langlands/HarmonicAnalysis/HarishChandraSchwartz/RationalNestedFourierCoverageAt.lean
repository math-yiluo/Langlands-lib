import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardLeviFourierVanishing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceQuotientHaar
import Langlands.GroupScheme.Rational.SemistandardProperLeviRank

/-! # The nested Fourier coverage at the two source compacts -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact
open Langlands.GroupScheme Langlands.Haar Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift

open RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (p : SemistandardSpectralIndex i) (m : LeviModel p)

local instance coverageLeviAffine : IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom
local instance coverageLeviFiniteType : LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

set_option hygiene false in
local notation "iM" => semistandardLeviSplitTorus p m.represents

variable {ν νM : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {KM : OpenSubgroup (rationalPoints m.scheme)}
  (hKM : IsCompact (KM : Set (rationalPoints m.scheme)))
  (hPMK : IsIwasawaPair (standardParabolicPoints iM νM ∅) KM.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ r, (Z r).toGrp ⟶ (chosenLeviModel r).scheme) (ha : ∀ r, IsSplitComponent (a r))
  [∀ r, ((chosenLeviModel r).splitCenter (a r)).Normal]
  [∀ r, MeasurableSpace (levi r ⧸ (chosenLeviModel r).splitCenter (a r))]
  [∀ r, BorelSpace (levi r ⧸ (chosenLeviModel r).splitCenter (a r))]
  (μR : ∀ r, Measure (levi r ⧸ (chosenLeviModel r).splitCenter (a r)))
  [∀ r, (μR r).IsHaarMeasure] [∀ r, (μR r).IsInvInvariant]
  (d : ∀ r : SemistandardSpectralIndex i, CompactData r)
  {ZM : SemistandardSpectralIndex iM → CommGroupScheme (Spec (CommRingCat.of F))}
  (aM : ∀ q, (ZM q).toGrp ⟶ (chosenLeviModel q).scheme) (haM : ∀ q, IsSplitComponent (aM q))
  [∀ q, ((chosenLeviModel q).splitCenter (aM q)).Normal]
  [∀ q, MeasurableSpace (levi q ⧸ (chosenLeviModel q).splitCenter (aM q))]
  [∀ q, BorelSpace (levi q ⧸ (chosenLeviModel q).splitCenter (aM q))]
  (μQ : ∀ q, Measure (levi q ⧸ (chosenLeviModel q).splitCenter (aM q)))
  [∀ q, (μQ q).IsHaarMeasure] [∀ q, (μQ q).IsInvInvariant]
  (dM : ∀ q : SemistandardSpectralIndex iM, CompactData q)

/-- The normalized cover of all actual inner orbits in the III.6 and
VIII.2.1 diagram at the inherited split torus and compact trace. -/
def SourceNestedFourierCoverageStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i →
  IsGenericCocharacter i ν → IsGenericCocharacter iM νM →
  SpecialCompactProperties F i ν K.toSubgroup → SpecialCompactProperties F iM νM KM.toSubgroup →
  IsClosedSubgroup ρ →
  (∀ x : rationalPoints m.scheme, x ∈ KM ↔ rationalPoints.map m.inclusion x ∈ K) →
  (∀ r, (d r).compact = K) → (∀ q, (dM q).compact = KM) →
  (∀ r, μR r = (chosenLeviModel r).sourceQuotientHaar (a r) K hK) →
  (∀ q, μQ q = (chosenLeviModel q).sourceQuotientHaar (aM q) KM hKM) →
  RationalSemistandardNestedFourierCoverage.{u, uV}
    (muG := RationalDynamicSource.ambientHaar K hK)
    (muLevi := RationalDynamicSource.ambientHaar KM hKM)
    hK hPK ρ p m hKM hPMK (subgroupCompactOpenHaar K hK (radical p) (isClosed_radical p))
    a ha μR d aM haM μQ dM

end Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift
