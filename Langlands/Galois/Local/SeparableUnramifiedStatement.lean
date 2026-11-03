import Langlands.Galois.Local.SeparableInertiaDefinitions

noncomputable section

open IsLocalRing ValuativeRel
open scoped NNReal

namespace Langlands.LocalGalois.Separable

universe u

section Arithmetic

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F
local instance : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

/-- Arithmetic unramifiedness in the actual spectral integer and residue rings.
This predicate makes no reference to inertia or its fixed field. -/
def ArithmeticUnramified (E : IntermediateField F (SeparableClosure F)) : Prop :=
  Ideal.map (algebraMap (baseIntegers F) (extensionIntegers F E))
      (maximalIdeal (baseIntegers F)) = maximalIdeal (extensionIntegers F E) ∧
    Algebra.IsSeparable (ResidueField (baseIntegers F))
      (ResidueField (extensionIntegers F E))

/-- A finite intermediate field is contained in the actual inertia fixed field
exactly when its spectral integer and residue extension is unramified. -/
def FiniteUnramifiedMaximality : Prop :=
  ∀ (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E],
    E ≤ inertiaFixedField F ↔ ArithmeticUnramified F E

/-- Every finite set in the actual inertia fixed field lies in a finite Galois
unramified intermediate field of the same separable closure. -/
def FiniteUnramifiedGaloisExhaustion : Prop :=
  ∀ s : Finset (inertiaFixedField F),
    ∃ E : IntermediateField F (SeparableClosure F),
      FiniteDimensional F E ∧ IsGalois F E ∧ E ≤ inertiaFixedField F ∧
        ArithmeticUnramified F E ∧
          ∀ x ∈ s, fixedFieldToSepClosure F x ∈ E

end Arithmetic

/-- Characteristic-uniform finite maximality and Galois exhaustion targets. -/
def SeparableUnramifiedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
      FiniteUnramifiedMaximality F ∧ FiniteUnramifiedGaloisExhaustion F

end Langlands.LocalGalois.Separable
