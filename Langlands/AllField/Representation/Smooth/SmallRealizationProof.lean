import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.AllField.Representation.Smooth.SmallRealizationStatement
/-! Proof that irreducible smooth complex representations of an actual local-field
general linear group have equivalent realizations in every carrier universe.
The orbit of a nonzero vector is countable and spans, so a basis chosen inside
it is countable and can be reindexed by a type in the prescribed universe. -/

open TopologicalSpace

namespace Langlands.AllField

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

/-- The general linear group of an actual nonarchimedean local field, with the topology of a
supplied realization, is second countable. -/
theorem _root_.Langlands.LocalFieldData.generalLinearSecondCountableTopology
    {F : Type uF} [Field F] (T : LocalFieldData F) (n : ℕ) :
    letI := T.generalLinearTopology n
    SecondCountableTopology (GeneralLinear n F) := by
  let := T.topology
  have := T.secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

/-- Irreducible smooth complex representations of an actual local-field general
linear group have equivalent irreducible smooth realizations in every carrier
universe. -/
theorem padicIrreducibleSmoothSmallRealization :
    PadicIrreducibleSmoothSmallRealizationStatement.{uF, uW, uV} := by
  intro F _ T n
  let := T.topology
  intro π hπ
  have : IsTopologicalGroup (GeneralLinear n F) :=
    T.generalLinearTopologicalGroup n
  have : SecondCountableTopology (GeneralLinear n F) :=
    T.generalLinearSecondCountableTopology n
  exact exists_irreducible_smoothRep_equiv_of_separable.{uF, uW, uV} π hπ

end Langlands.AllField
