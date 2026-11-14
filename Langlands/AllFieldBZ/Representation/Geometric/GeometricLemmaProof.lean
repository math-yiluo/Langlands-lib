import Langlands.AllFieldBZ.Representation.Geometric.ConditionalAssembly
import Langlands.AllFieldBZ.Representation.Geometric.CosetOrbitOrdering
import Langlands.AllFieldBZ.Representation.Geometric.PadicParabolicBruhatProof
import Langlands.AllFieldBZ.Representation.Geometric.ParabolicSupportGradedProof
import Langlands.Representation.Geometric.GeometricLemmaProof

/-!
# All-field port of `Langlands.Representation.Geometric.GeometricLemmaProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.GeometricLemmaProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicParabolicOrbitJacquetComparison PadicParabolicSupportGradedTheorem PadicParabolicSupportJacquetComparison PadicStandardIntersectionsTheorem closedSubgroupOrbitOrdering_of_finiteOrbitOrdering correctionSubgroupDiagonalHaar geometricLemma_of_orderedCosets geometricLemma_of_supportGraded geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicBruhatMatrixExistence padicBruhatWeylReflection padicGeometricLemma padicParabolicBruhat padicParabolicOrbitJacquetComparison padicParabolicSupportGradedTheorem padicParabolicSupportJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor parabolicSupportGradedCompactSmoothIso refinedLeviModulus_of_diagonal supportCoinvariantsImageHom_injective supportCoinvariantsImageIso supportImageNatIso supportImageQuotientHom supportImageQuotientHom_bijective supportImageQuotientIso supportImageToQuotient supportImageToQuotient_ker supportImageToQuotient_on_support supportImageToQuotient_surjective
open Langlands.GeneralLinear
universe uF uV

/-- The actual normalized induction-Jacquet composite has the natural filtration
and standard-intersection geometric pieces in the published statement. -/
theorem padicGeometricLemma : PadicGeometricLemmaTheorem.{uF, uV} := by
  intro F T n hn B C
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
      (B.parabolic F.Carrier : Set (GeneralLinear n F.Carrier))
      (C.parabolic F.Carrier : Set (GeneralLinear n F.Carrier))) :=
    Finite.of_surjective _ hBruhat.surjective
  obtain ⟨m, ⟨s⟩⟩ :=
    (closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
      Langlands.Topology.finiteOrbitOrdering) (GeneralLinear n F.Carrier)
        (B.parabolic F.Carrier) (C.parabolic F.Carrier)
        (B.isClosed_parabolic F.Carrier) (C.isClosed_parabolic F.Carrier) hfinite
  choose S hS using fun w =>
    (padicStandardIntersectionsTheorem.{uF} F n hn B C w).1
  choose R hR using fun w =>
    (padicStandardIntersectionsTheorem.{uF} F n hn B C w).2
  apply geometricLemma_of_orderedCosets.{uF, uV} T B C s hBruhat S R hS hR
  intro e t ht
  exact padicParabolicSupportGradedTheorem.{uF, uV}
    F T n hn B C m e t ht S R hS hR

end Langlands.AllFieldBZ.Geometric
