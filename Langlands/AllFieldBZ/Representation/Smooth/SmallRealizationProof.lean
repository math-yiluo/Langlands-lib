import Langlands.AllFieldBZ.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalContragredientStatement
import Langlands.AllFieldBZ.Representation.Smooth.SmallRealizationStatement
import Langlands.Representation.Smooth.SmallRealizationProof

/-!
# All-field port of `Langlands.Representation.Smooth.SmallRealizationProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Smooth.SmallRealizationProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open TopologicalSpace
namespace Langlands.AllFieldBZ
universe uF uG uW uV

section Transport
variable {k : Type*} {G : Type*} {V : Type*} {W : Type*}
variable [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

end Transport
section Orbit
variable {k : Type*} [Field k] {G : Type uG} [Group G]
  {V : Type uW} [AddCommGroup V] [Module k V]

variable [TopologicalSpace G] [IsTopologicalGroup G] [SeparableSpace G]

end Orbit
section Realization
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SeparableSpace G]

end Realization
/-- The general linear group of an actual p-adic field, with the topology of a
supplied realization, is second countable. -/
theorem LocalFieldPackage.TopologicalData.generalLinearSecondCountableTopology
    {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    SecondCountableTopology (GeneralLinear n F.Carrier) := by
  let := T.topology
  have := T.secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

/-- Irreducible smooth complex representations of an actual p-adic general
linear group have equivalent irreducible smooth realizations in every carrier
universe. -/
theorem padicIrreducibleSmoothSmallRealization :
    PadicIrreducibleSmoothSmallRealizationStatement.{uF, uW, uV} := by
  intro F T n
  let := T.topology
  intro π hπ
  have : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
    T.generalLinearTopologicalGroup n
  have : SecondCountableTopology (GeneralLinear n F.Carrier) :=
    T.generalLinearSecondCountableTopology n
  exact exists_irreducible_smoothRep_equiv_of_separable.{uF, uW, uV} π hπ

end Langlands.AllFieldBZ
