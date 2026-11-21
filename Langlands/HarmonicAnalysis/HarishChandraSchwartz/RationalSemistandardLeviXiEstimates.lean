import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GlobalSquareIntegrableCoefficientBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviTempered
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardLeviConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrableOfUpperBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundProof
import Langlands.Representation.Plancherel.SquareIntegrableCentralPullback

/-! # Xi estimates on a literal semistandard Levi -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean modelAffine modelTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} (m : LeviModel p)

local instance xiEstimateModelAffine : IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom
local instance xiEstimateModelFiniteType : LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

variable {SM T : CommGroupScheme (Spec (CommRingCat.of F))}
  {iM : SM.toGrp ⟶ m.scheme} (s : T.toGrp ⟶ m.scheme)
  {νM : cocharacterLattice SM} {KM : OpenSubgroup (rationalPoints m.scheme)}
  (hKMc : IsCompact (KM : Set (rationalPoints m.scheme)))
  (hPMK : IsIwasawaPair (standardParabolicPoints iM νM ∅) KM.toSubgroup)
  {K₀M : CompactOpenSubgroup (rationalPoints m.scheme)}
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (muL : Measure (levi p)) [muL.IsHaarMeasure]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (C : Subgroup (levi p)) [C.Normal] (hC : C ≤ Subgroup.center (levi p))
  [MeasurableSpace (levi p ⧸ C)] [BorelSpace (levi p ⧸ C)]
  (muC : Measure (levi p ⧸ C)) [muC.IsHaarMeasure]

set_option hygiene false in
local notation "ΞM" => fun x : levi p => rationalXi hKMc hPMK (m.pointHomeomorph.symm x)
set_option hygiene false in
local notation "σM" => fun x : levi p => rationalHeight (F := F) ρ (x : rationalPoints G)

/-- Levi versions of II.1.5 and III.1.2 with the actual Xi and restricted matrix
height, from the Cartan cover and simultaneous basis on the Levi scheme. -/
def SemistandardLeviXiEstimatesStatement : Prop :=
  IsMaximalSplitTorus iM → IsGenericCocharacter iM νM → IsSplitComponent s →
    IsClosedSubgroup ρ → SimultaneousStandardBasisAt iM νM K₀M.toSubgroup →
    RationalPointFamily.FiniteCartanCovering F iM νM K₀M.toSubgroup →
    IsSquareIntegrableModCentralSubgroup C hC π.obj.representation muC →
    SquareIntegrableWeight muL ΞM σM ∧ HasXiBoundedCoefficients ΞM π.obj.representation

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Transport the integral and the inducing representation along the same
actual Levi identification. The central quotient keeps its Haar scale. -/
theorem semistandardLeviXiEstimates :
    SemistandardLeviXiEstimatesStatement m s hKMc hPMK (K₀M := K₀M) ρ muL π C hC muC := by
  intro hiM hνM hs hρ hbasis hcover hsq
  let e := m.pointHomeomorph
  let muM := muL.map e.symm
  let : muM.IsHaarMeasure := e.symm.isHaarMeasure_map muL
  have hheight : (fun x : levi p => rationalHeight (F := F) (ρ.restrict m.inclusion) (e.symm x)) = σM := by
    funext x
    rw [rationalHeight_restrict_semistandardLevi ρ p m, e.apply_symm_apply]
  constructor
  · have hw := rationalXiSquareIntegrable_of_upperBound rationalXiUpperBound F m.scheme m.reductive
      SM iM hiM νM hνM K₀M.toSubgroup K₀M.1.isOpen K₀M.2 hbasis hcover KM.toSubgroup
      KM.isOpen hKMc hPMK N (ρ.restrict m.inclusion)
      (isClosedSubgroup_restrict_semistandardLevi ρ p m hρ) muM
    have hpull := (squareIntegrableWeight_map_equiv_iff e.symm.toHomeomorph.toMeasurableEquiv muL
      (rationalXi hKMc hPMK) (rationalHeight (F := F) (ρ.restrict m.inclusion))).mp hw
    change SquareIntegrableWeight muL ΞM (fun x => rationalHeight (F := F) (ρ.restrict m.inclusion) (e.symm x)) at hpull
    rwa [hheight] at hpull
  · let CM := C.comap e.toMonoidHom
    let : MeasurableSpace (rationalPoints m.scheme ⧸ CM) := borel _
    let : BorelSpace (rationalPoints m.scheme ⧸ CM) := ⟨rfl⟩
    let πM := IrreducibleAdmissibleRep.pullback e π
    let muCM := centralSubgroupPullbackMeasure e C muC
    have hCM := centralSubgroup_comap_le_center e C hC
    have hsqM : IsSquareIntegrableModCentralSubgroup CM hCM πM.obj.representation muCM :=
      isSquareIntegrableModCentralSubgroup_pullback e C muC hC π.obj.representation hsq
    have hbound := hasXiBoundedCoefficients_of_centralSubgroupSquareIntegrable
      KM.isOpen hKMc hPMK m.reductive hiM hνM K₀M.2 hbasis hcover hs πM CM hCM muCM hsqM
    refine (hasXiBoundedCoefficients_comp_continuousMulEquiv_iff ΞM π.obj.representation e).mp ?_
    have hΞ : ΞM ∘ e = rationalXi hKMc hPMK :=
      funext fun x => congrArg (rationalXi hKMc hPMK) (e.symm_apply_apply x)
    rw [hΞ]
    exact hbound

end Langlands.HarishChandraSchwartz.RationalSemistandard
