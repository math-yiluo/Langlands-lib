import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityFiniteReduction
import Langlands.ClassFieldTheory.Local.UpperReciprocityProof

/-! # Absolute upper ramification compatibility of local reciprocity -/

namespace Langlands.LocalClassField

universe u

/-- Absolute local reciprocity identifies unit images with inertia and upper
ramification groups and gives conductor criteria for complex quasicharacters. -/
theorem absoluteUpperReciprocityTheorems : AbsoluteUpperReciprocityTheorems.{u} :=
  absoluteUpperReciprocityTheorems_of_finiteRealImages
    finiteUpperReciprocityTheorems.{u}.2.1

end Langlands.LocalClassField
