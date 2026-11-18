import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalUnitKernel
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralKernelLocalStep
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvergenceReductions

/-! # Proposition VIII.4.1 from a degree-zero operator and four analytic statements

This module composes the cuspidal unit `°e = P(1_H)` of an operator `P` with the degree-zero laws
(`IsRationalDegreeZeroOperator`) with the local kernel step of
`RationalCuspidalCentralKernelLocalStep`. For one group `G` with its structural data, one Haar
measure `μG` and one such `P`, both conclusions of Proposition VIII.4.1 hold for every Haar
measure on `A_G(F)`, every continuous unitary character and every compact open subgroup `H`,
given four Library statements: the split-centre heights, Lemma II.1.5, the special-vertex compact
inputs and Corollary VIII.3.2. The closed target `RationalCuspidalCentralProjectionFiniteStatement`
follows from the same four statements and the existence of such a `P` for every structural choice
(`RationalDegreeZeroOperatorExistenceStatement`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- **The local kernel step at `°e`.** For connected reductive `G`, a Haar measure `μG`, an
operator `P` with the degree-zero laws, a compact open subgroup `H`, the central and `L²` weights
and the VIII.3.2 integrability form at `°e = P(1_H)`, the actual central level span of `H` is
finite dimensional, for every unitary `χ`. -/
theorem IsRationalDegreeZeroOperator.finiteDimensional_levelSpan_of_conjugationIntegrable
    (hG : IsConnectedReductive G) (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (χ : (rationalPoints.map s).range →* ℂˣ) (hχ : IsUnitaryCharacter χ)
    {μG : Measure (rationalPoints G)} [μG.IsHaarMeasure]
    {P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ}
    (hP : IsRationalDegreeZeroOperator hKc hPK ρ μG P)
    (H : CompactOpenSubgroup (rationalPoints G))
    (hw : CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hL : L2Weights μG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (h32 : RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA μG
      (P (rationalSubgroupIndicator hKc hPK ρ μG H))) :
    FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup) :=
  (hP.isRationalCuspidalLevelKernel hKc hPK ρ H).finiteDimensional_levelSpan_of_conjugationIntegrable
    hKc hPK ρ hG hs muA χ hχ μG H.1 H.2 hw hL h32

/-- **Proposition VIII.4.1 for one group, from a degree-zero operator.** Let `G` be connected
reductive with the structural data of `RationalCuspidalCentralProjectionFiniteStatement`, `μG` a
Haar measure on `G(F)` and `P` an operator with the degree-zero laws for `μG`. Assume the
split-centre heights, Lemma II.1.5, the special-vertex compact inputs and Corollary VIII.3.2.
Then for every Haar measure `muA` on `A_G(F)`, every continuous unitary character `χ` and every
compact open subgroup `H`, the actual central level span equals the raw level image and is
finite dimensional. -/
theorem IsRationalDegreeZeroOperator.centralLevelSpan_eq_image_and_finiteDimensional
    (hcen : RationalSplitCenterHeightStatement.{u})
    (hsq : RationalXiSquareIntegrableStatement.{u})
    (hSV : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u})
    (h32 : RationalCuspidalConjugationIntegrabilityStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hρ : IsClosedSubgroup ρ) (hs : IsSplitComponent s)
    {μG : Measure (rationalPoints G)} [μG.IsHaarMeasure]
    {P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ}
    (hP : IsRationalDegreeZeroOperator hKc hPK ρ μG P)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (χ : (rationalPoints.map s).range →* ℂˣ) (hχc : Continuous χ) (hχ : IsUnitaryCharacter χ)
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G))) :
    (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup :
        Set (rationalPoints G → ℂ)) =
        rationalCuspidalCentralLevelImage hKc hPK ρ muA χ H.toSubgroup ∧
      FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup) := by
  refine ⟨coe_schwartzCentralIntegralSpan_eq_image _ muA χ
    (CentralIntegralConvergesOn.mono_of_le le_top
      (hcen.schwartzCentralConvergence F G hG S i hi ν hν K hKc hPK N ρ hρ T s hs muA χ hχc hχ)),
    ?_⟩
  obtain ⟨D, x, -, -, hbasis, -⟩ := hSV F G hG S i hi ν hν
  exact RationalCuspidalLevelKernelFiniteStatement.of_statements hcen hsq hSV F G hG S i hi ν hν
    K hKc hPK N ρ hρ T s hs muA χ hχ H hHc μG _
    (hP.isRationalCuspidalLevelKernel hKc hPK ρ ⟨H, hHc⟩)
    (hP.levelKernelConjugationIntegrable hKc hPK ρ h32 hG hi hν hbasis hρ hs muA ⟨H, hHc⟩)

end Rational

/-- **Existence of a degree-zero operator.** For every structural choice of
`RationalCuspidalCentralProjectionFiniteStatement` except the split component and the central
data, there are a Haar measure `μG` on `G(F)` and a complex-linear operator `P` on the actual
rational Schwartz space with the degree-zero laws for `μG` (`IsRationalDegreeZeroOperator`). In
the source, `P` is the degree-zero projection `f ↦ °f` of VIII.2. -/
def RationalDegreeZeroOperatorExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (K : OpenSubgroup (rationalPoints G))
      (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
    ∃ μG : Measure (rationalPoints G), μG.IsHaarMeasure ∧
      ∃ P : RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ] RationalSchwartzSpace hKc hPK ρ,
        IsRationalDegreeZeroOperator hKc hPK ρ μG P

/-- **Proposition VIII.4.1 from a degree-zero operator and four analytic statements.** -/
theorem RationalDegreeZeroOperatorExistenceStatement.centralProjectionFinite
    (hdeg : RationalDegreeZeroOperatorExistenceStatement.{u})
    (hcen : RationalSplitCenterHeightStatement.{u})
    (hsq : RationalXiSquareIntegrableStatement.{u})
    (hSV : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u})
    (h32 : RationalCuspidalConjugationIntegrabilityStatement.{u}) :
    RationalCuspidalCentralProjectionFiniteStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs muA _ χ hχc hχ H hHc
  obtain ⟨μG, hμG, P, hP⟩ := hdeg F G hG S i hi ν hν K hKc hPK N ρ hρ
  exact hP.centralLevelSpan_eq_image_and_finiteDimensional hKc hPK ρ hcen hsq hSV h32 hG hi hν hρ
    hs muA χ hχc hχ H hHc

end Langlands.HarishChandraSchwartz
