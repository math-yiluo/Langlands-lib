import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionIdentityDensity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWeakTermParameterContinuity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialCompactConstantTermPremises
import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.BruhatTits.SpecialCompact.StandardComponentBasisTransport

/-! # Continuity of the weak constant term on the unitary orbit

This module proves `RationalOrbitWeakTermContinuityStatement`: for every section `Φ` of the
induced orbit family and every `m' ∈ M'(F)`, the weak constant term `ω ↦ (f_ω)^w_{P'}(m')` is
continuous on the unitary orbit `O`.
-/

noncomputable section

set_option maxRecDepth 8000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section WeakTermContinuity

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I J : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "M₁" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M₁))
  (C : Subgroup M₁) [C.Normal] (hC : C ≤ Subgroup.center M₁)
  [MeasurableSpace (M₁ ⧸ C)] (mu : Measure (M₁ ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- **Continuity of the weak constant term on the unitary orbit.** For every section `Φ` of the
induced orbit family and every `m' ∈ M'(F)`, the weak constant term `ω ↦ (f_ω)^w_{P'}(m')` is
continuous on `O`. -/
theorem rationalOrbitWeakTermContinuity :
    RationalOrbitWeakTermContinuityStatement hG hi hν I J hKc hPK π C hC mu hsq hA := by
  intro _ Φ m
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨K0, -, hK0c, -, hbasis, -, hcover⟩ := exists_constantTermPremises_of_joint
    jointSpecialCompactBasisExistence hG hi hν
  obtain ⟨B, hB, hBJ⟩ := id hbasis
  have hJ := RationalPointFamily.rootSet_subset i ν J
  obtain ⟨-, A', q', hA', hmem'⟩ := hBJ _ hJ
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG S i hi ν hν _ hJ).1
  exact rationalOrbitWeakTermParameterContinuity hG hi hν I J hKc hPK π C hC mu hsq hA hζ
    hK0c hbasis (hcover _ (RationalPointFamily.rootSet_subset i ν I)).1 hB
    (fun L hL => (hmem' L hL).of_compatibleComponent i ν hA hA' hG hi hν hJ) Φ m

end WeakTermContinuity

end Langlands.HarishChandraSchwartz
