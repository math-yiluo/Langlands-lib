import Langlands.Global.AdelicSpaceWeilRestrictionStatement
import Langlands.Global.NumberFieldSpaceWeilGenericFiber
import Langlands.Global.CurvePlaceSpaceWeilGenericFiber
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionProof
import Langlands.Global.CurvePlacePrincipalSIntegerFiniteType

/-! # Conrad's Proposition 5.14 for separated algebraic spaces -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct AlgebraicCurve.CurveModel
  IntermediateField.algebraAdjoinAdjoin Langlands.Global
  Langlands.Global.NumberFieldSIntegers Langlands.Global.CurvePlacePrincipalSIntegers

namespace Langlands.Global

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open AdelicSpaceSpreadIndependenceProof

set_option backward.isDefEq.respectTransparency false

namespace AdelicSpaceWeilRestrictionProof

/-- Conrad's Proposition 5.14 over number fields, for all separated finite-type spreads. -/
theorem numberFieldSpaceWeilRestriction : NumberFieldSpaceWeilRestrictionStatement.{u} := by
  intro K L _ _ _ _ _ Y hYsep hYft
  let : Module.Free K L := Module.Free.of_divisionRing K L
  obtain ⟨hY, -, hWft, hWsep, -⟩ := spaceWeilRestriction K L Y
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hYsep) hYft
  refine ⟨hY, hWsep hYsep, hWft, ?_⟩
  classical
  obtain ⟨U, Z₀, hZ₀sep, hZ₀ft, ⟨e₀⟩⟩ := numberFieldSpaceSpreadExistence L Y hYsep hYft
  let V : Finset (FinitePlace K) := U.image (HeightOneSpectrum.under (NumberField.RingOfIntegers K))
  have hUV : U ⊆ numberFieldExceptionalPreimage (L := L) V := by
    intro q hq
    exact (mem_numberFieldExceptionalPreimage V q).mpr (Finset.mem_image_of_mem _ hq)
  let Z := numberFieldSpaceLevelBaseChange L hUV Z₀
  have hZsep : IsSeparated Z := hZ₀sep.baseChange
  have hZft : FiniteTypeOverRing (NumberFieldSIntegerSpaceWeilTopology.upperCoefficients K L V) Z :=
    hZ₀ft.baseChange
  let eZ : numberFieldSpaceGenericFiber L (numberFieldExceptionalPreimage (L := L) V) Z ≅ Y :=
    (AdelicSpaceSpreadInitialSet.numberFieldGenericFiberIso L hUV Z₀).trans e₀
  obtain ⟨hZ, -, hWZft, hWZsep, -⟩ := spaceWeilRestriction
    (NumberFieldSIntegerSpaceWeilTopology.lowerCoefficients K V)
    (NumberFieldSIntegerSpaceWeilTopology.upperCoefficients K L V) Z
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hZsep) hZft
  let WZ := ringWeilRestrictionSpace
    (NumberFieldSIntegerSpaceWeilTopology.lowerCoefficients K V)
    (NumberFieldSIntegerSpaceWeilTopology.upperCoefficients K L V) Z hZ
  let eWZ : numberFieldSpaceGenericFiber K V WZ ≅ ringWeilRestrictionSpace K L Y hY :=
    NumberFieldSpaceWeilGenericFiber.genericFiberIsoOfIso K L V Z hZ Y hY eZ
  let H := NumberFieldSpaceWeilGenericFiber.adelicPointHomeomorphOfIso K L V Z hZ Y hY eZ
    hZsep hZft (hWZsep hZsep) hWZft
  intro S S' X X' hXsep hXft hX'sep hX'ft e e'
  rw [numberField_spreadTopology_independent S V X WZ hXsep hXft
      (hWZsep hZsep) hWZft (ringWeilRestrictionSpace K L Y hY) e eWZ,
    numberField_spreadTopology_independent S' (numberFieldExceptionalPreimage (L := L) V)
      X' Z hX'sep hX'ft hZsep hZft Y e' eZ]
  let := numberFieldSpaceSpreadTopology K V WZ (ringWeilRestrictionSpace K L Y hY) eWZ
  let := numberFieldSpaceSpreadTopology L (numberFieldExceptionalPreimage (L := L) V) Z Y eZ
  have hfun : (fun x => RingPoints.changeRing (numberFieldAdeleTensorMap K L)
      (ringWeilRestrictionPointsEquiv K L (Adeles K) Y hY x)) = H := by
    funext x
    exact (NumberFieldSpaceWeilGenericFiber.adelicPointHomeomorphOfIso_apply
      K L V Z hZ Y hY eZ hZsep hZft (hWZsep hZsep) hWZft x).symm
  rw [hfun]
  exact H.isHomeomorph

set_option maxHeartbeats 800000 in
/-- Conrad's Proposition 5.14 over global function fields, including inseparable extensions. -/
theorem curvePlaceSpaceWeilRestriction : CurvePlaceSpaceWeilRestrictionStatement.{u} := by
  intro k K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y hYsep hYft
  let : Module.Free K L := Module.Free.of_divisionRing K L
  obtain ⟨hY, -, hWft, hWsep, -⟩ := spaceWeilRestriction K L Y
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hYsep) hYft
  refine ⟨hY, hWsep hYsep, hWft, ?_⟩
  classical
  obtain ⟨U, Z₀, hU, hZ₀sep, hZ₀ft, ⟨e₀⟩⟩ := curvePlaceSpaceSpreadExistence k L Y hYsep hYft
  let s : K := algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)
  let : FiniteDimensional k⟮s⟯ K := FunctionField.FiniteDimensional.adjoin_algebraMap_X
  let V₀ : Finset (Place k K) := U.image (curvePlaceRestriction (K := K))
  obtain ⟨t, ht, hV₀⟩ := exists_curvePlacePrincipalExceptional_superset k K s V₀
  let : Fact (t ≠ 0) := ⟨ht⟩
  let V := curvePlacePrincipalExceptional k K s (t : K)
  have hV : V.Nonempty := (hU.image (curvePlaceRestriction (K := K))).mono hV₀
  have hUV : U ⊆ curvePlaceExceptionalPreimage (L := L) V := by
    intro q hq
    exact (mem_curvePlaceExceptionalPreimage V q).mpr (hV₀ (Finset.mem_image_of_mem _ hq))
  let Z := curvePlaceSpaceLevelBaseChange k L hUV Z₀
  have hZsep : IsSeparated Z := hZ₀sep.baseChange
  have hZft : FiniteTypeOverRing
      (CurvePlacePrincipalSIntegerSpaceWeilTopology.upperCoefficients k K L s t) Z :=
    hZ₀ft.baseChange
  let eZ : curvePlaceSpaceGenericFiber k L (curvePlaceExceptionalPreimage (L := L) V) Z ≅ Y :=
    (AdelicSpaceSpreadInitialSet.curveGenericFiberIso k L hUV Z₀).trans e₀
  obtain ⟨hZ, -, hWZft, hWZsep, -⟩ := spaceWeilRestriction
    (CurvePlacePrincipalSIntegerSpaceWeilTopology.lowerCoefficients k K s t)
    (CurvePlacePrincipalSIntegerSpaceWeilTopology.upperCoefficients k K L s t) Z
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hZsep) hZft
  let WZ := ringWeilRestrictionSpace
    (CurvePlacePrincipalSIntegerSpaceWeilTopology.lowerCoefficients k K s t)
    (CurvePlacePrincipalSIntegerSpaceWeilTopology.upperCoefficients k K L s t) Z hZ
  let eWZ : curvePlaceSpaceGenericFiber k K V WZ ≅ ringWeilRestrictionSpace K L Y hY :=
    CurvePlaceSpaceWeilGenericFiber.genericFiberIsoOfIso k K L s t Z hZ Y hY eZ
  let H := CurvePlaceSpaceWeilGenericFiber.adelicPointHomeomorphOfIso k K L s t Z hZ Y hY eZ
    hZsep hZft (hWZsep hZsep) hWZft hV
  have hV' : (curvePlaceExceptionalPreimage (L := L) V).Nonempty :=
    CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup.upperSupport_nonempty k K L s t hV
  intro S S' hS hS' X X' hXsep hXft hX'sep hX'ft e e'
  rw [curve_spreadTopology_independent S V hS hV X WZ hXsep hXft
      (hWZsep hZsep) hWZft (ringWeilRestrictionSpace K L Y hY) e eWZ,
    curve_spreadTopology_independent S' (curvePlaceExceptionalPreimage (L := L) V)
      hS' hV' X' Z hX'sep hX'ft hZsep hZft Y e' eZ]
  let := curvePlaceSpaceSpreadTopology k K V WZ (ringWeilRestrictionSpace K L Y hY) eWZ
  let := curvePlaceSpaceSpreadTopology k L (curvePlaceExceptionalPreimage (L := L) V) Z Y eZ
  have hfun : (fun x => RingPoints.changeRing (curvePlaceAdeleTensorMap k K L)
      (ringWeilRestrictionPointsEquiv K L (CurvePlaceAdeleRing k K) Y hY x)) = H := by
    funext x
    exact (CurvePlaceSpaceWeilGenericFiber.adelicPointHomeomorphOfIso_apply
      k K L s t Z hZ Y hY eZ hZsep hZft (hWZsep hZsep) hWZft hV x).symm
  rw [hfun]
  exact H.isHomeomorph

end AdelicSpaceWeilRestrictionProof

/-- Conrad's Proposition 5.14: the original full adelic map of the Weil restriction
of any separated finite-type algebraic space is a homeomorphism in both characteristics. -/
theorem adelicSpaceWeilRestriction : AdelicSpaceWeilRestrictionStatement.{u} :=
  ⟨AdelicSpaceWeilRestrictionProof.curvePlaceSpaceWeilRestriction,
    AdelicSpaceWeilRestrictionProof.numberFieldSpaceWeilRestriction⟩

end Langlands.Global
