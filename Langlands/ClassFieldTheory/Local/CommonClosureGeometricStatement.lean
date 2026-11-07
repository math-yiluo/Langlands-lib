import Langlands.ClassFieldTheory.Local.ReciprocityTransport
import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
import Langlands.Correspondence.BaseReciprocityCandidate

/-!
# Normalized common-closure reciprocity families are geometric

Statement only; no proof is claimed. The components of a geometrically normalized
coherent reciprocity family in the common closure of a p-adic field `F`, transported to
`F` and to every standalone finite extension of `F`, are geometric Weil reciprocity maps.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u v

/-- For a normalized coherent reciprocity family `eC` of `F` in its common closure:
(1) every candidate of `F` compatible with the bottom component of `eC` is a geometric
Weil reciprocity map of `F`, and (2) for every finite p-adic extension `E` of `F`, given by
`g : F → E`, the component of `eC` at the image of `E`, transported to `E`, is a geometric
Weil reciprocity map of `E`. -/
def CommonClosureGeometricStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily F),
    LocalFactor.CommonClosure.NormalizedReciprocity F eC →
    (∀ e : LocalFactor.RankOne.ReciprocityCandidate F, Correspondence.IsBaseReciprocity F e eC →
      GeometricWeilReciprocityRelation F F.canonicalTopologicalData e) ∧
    ∀ (E : PadicField.{v} p) (g : F.Carrier →ₐ[Padic p] E.Carrier),
      GeometricWeilReciprocityRelation E E.canonicalTopologicalData
        (extensionReciprocityCandidate F E g eC)

end Langlands.LocalClassField
