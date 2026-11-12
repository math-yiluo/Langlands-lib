import Langlands.Automorphic.GeneralLinearUniformCuspidalRealization
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # The `GL_n` uniform comparisons with every hypothesis discharged

For rank `n > 0`, the standard representation, the canonical reductive smooth atlas, the proved
scalar commutator, the proved connected reductivity and the proved parabolic dynamic statement
instantiate the uniform-form and uniform-cusp-form comparisons. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local notation "std" =>
  GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of F)

local instance canonicalGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance canonicalGeneralLinearSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local instance canonicalPlotAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
  Module.addCommMonoidToAddCommGroup ℂ

omit [NumberField F] in
/-- The standard representation of `GL_n` is a closed embedding. -/
theorem generalLinearStandard_isClosedSubgroup : GroupScheme.IsClosedSubgroup std := by
  change IsClosedImmersion (𝟙 (GLG).X.left)
  infer_instance

/-- The actual uniform forms of `GL_n` for the canonical data. -/
abbrev CanonicalUniformGeneralLinearAdelicForms (hn : 0 < n) :
    Submodule ℂ (FinitePlotSmoothRationalFunctions F GLG) :=
  UniformGeneralLinearAdelicForms F n std
    (isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec
    (adelicDifferentialCommutator_of_smooth F GLG
      (isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec)
    (generalLinearStandard_isClosedSubgroup F n) hn (isConnectedReductive_generalLinear F (Fin n))

/-- The actual uniform forms of `GL_n` are linearly equivalent to the space of the uniform
operator realization, with no remaining hypothesis beyond `0 < n`. -/
def canonicalUniformAdelicAutomorphicRealizationEquiv (hn : 0 < n) :
    CanonicalUniformGeneralLinearAdelicForms F n hn ≃ₗ[ℂ]
      (uniformGeneralLinearOperatorRealization F n std hn).Space :=
  uniformAdelicAutomorphicRealizationEquiv F n std _ _ (generalLinearStandard_isClosedSubgroup F n)
    hn (isConnectedReductive_generalLinear F (Fin n))

@[simp]
theorem canonicalUniformAdelicAutomorphicRealizationEquiv_val (hn : 0 < n)
    (f : CanonicalUniformGeneralLinearAdelicForms F n hn) :
    ((canonicalUniformAdelicAutomorphicRealizationEquiv F n hn f).val).val =
      finitePlotSmoothGeneralLinearEquiv F n f.val := rfl

/-- The actual uniform cusp forms of `GL_n` for the canonical data. -/
abbrev CanonicalUniformGeneralLinearAdelicCuspidalForms (hn : 0 < n) :
    Submodule ℂ (FinitePlotSmoothRationalFunctions F GLG) :=
  UniformGeneralLinearAdelicCuspidalForms F n std hn
    (isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec
    (adelicDifferentialCommutator_of_smooth F GLG
      (isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec)
    (generalLinearStandard_isClosedSubgroup F n) (isConnectedReductive_generalLinear F (Fin n))
    parabolicDynamic

/-- An actual uniform form of `GL_n` is a uniform cusp form exactly when its original matrix
function is cuspidal. -/
theorem mem_canonicalUniformGeneralLinearAdelicCuspidalForms_iff [CompactSpace (AdeleQuotient F)]
    (hn : 0 < n) (f : FinitePlotSmoothRationalFunctions F GLG) :
    f ∈ CanonicalUniformGeneralLinearAdelicCuspidalForms F n hn ↔
      f ∈ CanonicalUniformGeneralLinearAdelicForms F n hn ∧
        Langlands.Automorphic.IsCuspidal F n (continuousGeneralLinearEquiv F n f.val) :=
  mem_uniformAdelicCuspidal_iff_generalLinear F n std hn _ _
    (generalLinearStandard_isClosedSubgroup F n) (isConnectedReductive_generalLinear F (Fin n))
    parabolicDynamic f

/-- A cuspidal operator realization inside the uniform realization maps injectively into the
canonical actual uniform cusp forms. -/
def canonicalUniformRealizationAdelicCuspidalFormMap [CompactSpace (AdeleQuotient F)]
    (hn : 0 < n) (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n std hn) (hc : S.IsCuspidal) :
    S.Space →ₗ[ℂ] CanonicalUniformGeneralLinearAdelicCuspidalForms F n hn :=
  uniformRealizationAdelicCuspidalFormMap _ _ (generalLinearStandard_isClosedSubgroup F n)
    (isConnectedReductive_generalLinear F (Fin n)) parabolicDynamic S hS hc

theorem canonicalUniformRealizationAdelicCuspidalFormMap_injective
    [CompactSpace (AdeleQuotient F)] (hn : 0 < n)
    (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n std hn) (hc : S.IsCuspidal) :
    Function.Injective (canonicalUniformRealizationAdelicCuspidalFormMap F n hn S hS hc) :=
  uniformRealizationAdelicCuspidalFormMap_injective _ _ (generalLinearStandard_isClosedSubgroup F n)
    (isConnectedReductive_generalLinear F (Fin n)) parabolicDynamic S hS hc

end Langlands.Automorphic.GroupSchemeFunctions
