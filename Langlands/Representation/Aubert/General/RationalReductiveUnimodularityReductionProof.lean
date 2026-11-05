import Langlands.Representation.Aubert.General.RationalParabolicModulusAssemblyStatement
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.Representation.Aubert.General.RationalCartanFiniteCover
import Langlands.Representation.Aubert.General.RationalTorusModularReductionProof

/-! # From actual Cartan and Iwahori inputs to ambient unimodularity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.BruhatTits.SpecialCompact Langlands.Haar
open Langlands.AlgebraicGeometry.PointTopology

/-- The explicit structural inputs imply the exact general ambient statement. -/
theorem rationalReductiveUnimodularity_of_structural_inputs
    (hProduct : IwahoriHaarProductStatement.{u})
    (hReciprocity : RationalOppositeHaarReciprocityStatement.{u})
    (hCentralizer : GenericCentralizerStatement.{u})
    (hJoint : JointSpecialCompactBasisExistenceStatement.{u})
    (hFinite : FiniteCoverCharacterStatement.{u})
    (hRegularity : ModularCharacterRegularityStatement.{u}) :
    RationalReductiveUnimodularityStatement.{u} := by
  intro k _ _ _ _ G hG
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ hStandard
  obtain ⟨T, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  let := hi.isSplitSubtorus.mono
  obtain ⟨D, x, Z, j, s, _, _, hs, h, _, hK, _, _, hCartan, _, _, hBasis⟩ :=
    hJoint k G hG T i hi ν hν
  have hTorus := rationalTorusModularReduction hProduct hReciprocity hCentralizer
    k G hG T i hi ν hν hStandard (D.specialCompactSubgroup x) hBasis
  obtain ⟨E, hE, hCover⟩ := exists_finite_torus_product_cover D x ν hs hCartan
  exact hFinite (RationalPoint k G.X) modularCharacter (D.specialCompactSubgroup x)
    (torusPoints i) E hE
    ((hRegularity (RationalPoint k G.X)).2.2.2 _ hK.2.1.1) hTorus hCover

/-- The structural propositions imply the original target with its original premises. -/
theorem rationalParabolicModulusAssembly : RationalParabolicModulusAssemblyStatement.{u} := by
  intro hProduct hReciprocity hCentralizer hJoint hFinite hRegularity hDynamic
  exact rationalParabolicModulus_of_reductiveUnimodularity
    (rationalReductiveUnimodularity_of_structural_inputs
      hProduct hReciprocity hCentralizer hJoint hFinite hRegularity) hDynamic

end Langlands.Aubert.General.RationalPointFamily
