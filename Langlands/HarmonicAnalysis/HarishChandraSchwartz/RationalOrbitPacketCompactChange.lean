import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket
import Langlands.Representation.Plancherel.CompactCoefficientNormalizationComparison

/-! # Compact probability normalization of actual rational orbit packets -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K L : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hLc : IsCompact (L : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) (L : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I

set_option hygiene false in
local notation "decomp" => isSemidirectDecomposition_standard hG hi hν
  (RationalPointFamily.rootSet_subset i ν I)
set_option hygiene false in
local notation "closedU" => isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)

private theorem exists_pos_rationalInducedCoefficientMap_eq_mul_of_compact :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : SmoothRep.{0, u, uV} ℂ 𝐌) (hA : A.IsAdmissible)
      (v : productInducedCoefficientObject decomp closedU A) (g : rationalPoints G),
        rationalInducedCoefficientMap hG hi hν I hKc hPK A hA v g =
          (c : ℂ) * rationalInducedCoefficientMap hG hi hν I hLc hPL A hA v g := by
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  obtain ⟨c, hc, hcoeff⟩ := CompactInduction.exists_pos_coefficientMap_eq_mul_of_compact.{u, uV}
    (G := rationalPoints G)
    (P := standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I))
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (U := standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    decomp closedU (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) decomp)
    K L hKc hLc
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPL)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
  refine ⟨c, hc, fun A hA v g => ?_⟩
  rw [rationalInducedCoefficientMap_eq_coefficientMap, rationalInducedCoefficientMap_eq_coefficientMap]
  with_reducible_and_instances exact hcoeff A hA v g

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "sectionK" => rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π
set_option hygiene false in
local notation "sectionL" => rationalInducedSmoothOrbitSections hG hi hν I hLc hPL π

/-- The same actual section gives the same orbit coefficient up to the fixed
positive compact-Haar normalization factor. -/
theorem exists_pos_rationalInducedOrbitCoefficientMap_eq_mul_of_compact :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : sectionK) (q' : sectionL), q.val = q'.val →
      ∀ (ω : Oπ) (g : rationalPoints G),
        rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq q ω g =
          (c : ℂ) * rationalInducedOrbitCoefficientMap hG hi hν I hLc hPL π C hC mu hsq q' ω g := by
  obtain ⟨c, hc, heq⟩ :=
    exists_pos_rationalInducedCoefficientMap_eq_mul_of_compact.{u, uV} hG hi hν I hKc hLc hPK hPL
  refine ⟨c, hc, fun q q' hq ω g => ?_⟩
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective νM π C hC mu hsq ω
  have hk := congrArg (fun f : LocallyConstant (rationalPoints G) ℂ => f g)
    (rationalInducedOrbitCoefficientMap_representative hG hi hν I hKc hPK π C hC mu hsq q A)
  have hl := congrArg (fun f : LocallyConstant (rationalPoints G) ℂ => f g)
    (rationalInducedOrbitCoefficientMap_representative hG hi hν I hLc hPL π C hC mu hsq q' A)
  have hv := congrArg (fun v => rationalInducedCoefficientMap hG hi hν I hKc hPK
    A.val.obj A.val.property.2 v g) (congrFun hq A)
  exact hk.trans (hv.trans ((heq A.val.obj A.val.property.2 (q'.val A) g).trans
    (congrArg (fun z : ℂ => (c : ℂ) * z) hl.symm)))

variable [Finite (discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq))]

/-- The same positive scalar compares the original weighted orbit integrals
for all weights and character measures. -/
theorem exists_pos_rationalInducedOrbitWavePacket_eq_mul_of_compact :
    ∃ c : ℝ, 0 < c ∧
      ∀ (rhoX : Measure (unitaryUnramifiedCharacters νM)) (w : Oπ → ℂ)
        (q : sectionK) (q' : sectionL), q.val = q'.val → ∀ g : rationalPoints G,
          rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq rhoX w q g =
            (c : ℂ) * rationalInducedOrbitWavePacket hG hi hν I hLc hPL π C hC mu hsq rhoX w q' g := by
  obtain ⟨c, hc, hcoeff⟩ := exists_pos_rationalInducedOrbitCoefficientMap_eq_mul_of_compact
    hG hi hν I hKc hLc hPK hPL π C hC mu hsq
  refine ⟨c, hc, fun rhoX w q q' hq g => ?_⟩
  rw [rationalInducedOrbitWavePacket_apply, rationalInducedOrbitWavePacket_apply, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    dsimp only
    rw [hcoeff q q' hq ω g, mul_left_comm]

end Langlands.HarishChandraSchwartz
