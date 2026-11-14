import Langlands.Representation.Geometric.GeometricLemmaProof
import Langlands.AllField.Representation.Geometric.ConditionalAssembly
import Langlands.AllField.Representation.Geometric.ParabolicSupportGradedProof
/-! The normalized geometric lemma for actual p-adic general linear groups. -/

noncomputable section

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicOrbitJacquetComparison PadicParabolicSupportGradedTheorem PadicParabolicSupportJacquetComparison PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricLemma_of_orderedCosets geometricLemma_of_supportGraded geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicGeometricLemma padicParabolicBruhat padicParabolicOrbitJacquetComparison padicParabolicSupportGradedTheorem padicParabolicSupportJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor parabolicSupportGradedCompactSmoothIso refinedLeviModulus_of_diagonal supportCoinvariantsImageHom_injective supportCoinvariantsImageIso supportImageNatIso supportImageQuotientHom supportImageQuotientHom_bijective supportImageQuotientIso supportImageToQuotient supportImageToQuotient_ker supportImageToQuotient_on_support supportImageToQuotient_surjective
open Langlands.AllField.Geometric

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV

/-- The actual normalized induction-Jacquet composite has the natural filtration
and standard-intersection geometric pieces in the published statement. -/
theorem padicGeometricLemma : PadicGeometricLemmaTheorem.{uF, uV} := by
  intro F _ T n hn B C
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearT2Space n
  let := T.generalLinearSigmaCompactSpace n
  have hBruhat := padicParabolicBruhat.{uF} F n hn B C
  have hfinite : Finite (DoubleCoset.Quotient
      (B.parabolic F : Set (GeneralLinear n F))
      (C.parabolic F : Set (GeneralLinear n F))) :=
    Finite.of_surjective _ hBruhat.surjective
  obtain ⟨m, ⟨s⟩⟩ :=
    (closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
      Langlands.Topology.finiteOrbitOrdering) (GeneralLinear n F)
        (B.parabolic F) (C.parabolic F)
        (B.isClosed_parabolic F) (C.isClosed_parabolic F) hfinite
  choose S hS using fun w =>
    (padicStandardIntersectionsTheorem.{uF} F n hn B C w).1
  choose R hR using fun w =>
    (padicStandardIntersectionsTheorem.{uF} F n hn B C w).2
  apply geometricLemma_of_orderedCosets.{uF, uV} T B C s hBruhat S R hS hR
  intro e t ht
  exact padicParabolicSupportGradedTheorem.{uF, uV}
    F T n hn B C m e t ht S R hS hR

end Langlands.AllField.Geometric
