import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilSlicingStatement
import Langlands.AlgebraicGeometry.LangWeil.Slicing.Core
import Langlands.AlgebraicGeometry.LangWeil.Slicing.Reduction

/-!
# Proof of the hyperplane-slicing induction step of the uniform Lang–Weil estimate

The ring-level slicing estimate for affine families over integral bases
(`Slicing.affineFamilyLangWeil_slicing`) gives `Slicing.AffineFamilyLangWeil (d + 2)`, and the
reduction to affine families (`Slicing.familyLangWeil_of_affine`) turns it into
`FamilyLangWeilInDimension (d + 2)`.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- **The slicing step.** Bertini's theorem for the generic hyperplane section and the uniform
point-count upper bound imply that the uniform Lang–Weil estimate in fibre dimension `d + 1`
implies it in fibre dimension `d + 2`. -/
theorem familyLangWeilSlicing : FamilyLangWeilSlicingStatement.{u} :=
  fun hB hUB d hLW =>
    Slicing.familyLangWeil_of_affine hUB (d + 1) (Slicing.affineFamilyLangWeil_slicing hB hUB d hLW)

end Langlands.AlgebraicGeometry.LangWeil
