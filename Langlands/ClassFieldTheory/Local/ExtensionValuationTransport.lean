import Langlands.ClassFieldTheory.Local.ExtensionFieldTransport
import Langlands.LocalField.CanonicalTransport

/-! # Canonical residue and valuation transport to the image field -/

noncomputable section

namespace Langlands.LocalClassField

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The actual residue-field equivalence induced by the canonical image-field equivalence. -/
def extensionIntermediateResidueEquiv : E.canonicalTopologicalData.ResidueField ≃+*
    (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).ResidueField := by
  letI := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
  exact PadicField.CanonicalTransport.residueEquiv E
    ((extensionFiniteIntermediate F E f).asPadicField (p := p))
    (extensionIntermediatePadicEquiv F E f)

/-- The image field and the standalone extension have identical residue cardinalities. -/
theorem extensionIntermediate_residueCardinality :
    (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).residueCardinality =
      E.canonicalTopologicalData.residueCardinality :=
  (Nat.card_congr (extensionIntermediateResidueEquiv F E f).toEquiv).symm

/-- The image-field comparison preserves integer order, also at zero. -/
theorem extensionIntermediate_ord (x : E.Carrier) :
    (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).ord
      (extensionIntermediatePadicEquiv F E f x) = E.canonicalTopologicalData.ord x := by
  let := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
  exact PadicField.CanonicalTransport.ord_map E
    ((extensionFiniteIntermediate F E f).asPadicField (p := p))
    (extensionIntermediatePadicEquiv F E f) x

/-- The image-field comparison preserves the normalized discrete valuation. -/
theorem extensionIntermediate_discreteValuation (x : E.Carrier) :
    (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).discreteValuation
      (extensionIntermediatePadicEquiv F E f x) = E.canonicalTopologicalData.discreteValuation x := by
  let := ((extensionFiniteIntermediate F E f).asPadicField (p := p)).algebra
  exact PadicField.CanonicalTransport.discreteValuation_map E
    ((extensionFiniteIntermediate F E f).asPadicField (p := p))
    (extensionIntermediatePadicEquiv F E f) x

/-- The existing comparison on units preserves discrete valuation. -/
theorem extensionIntermediateUnitsEquiv_discreteValuation (x : E.Carrierˣ) :
    letI := E.canonicalTopologicalData.topology
    letI := (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).topology
    (CommonClosure.canonicalData F (extensionFiniteIntermediate F E f)).discreteValuation
      ((extensionIntermediateUnitsEquiv F E f x :
        (extensionFiniteIntermediate F E f).fieldˣ) :
        (extensionFiniteIntermediate F E f).field) =
      E.canonicalTopologicalData.discreteValuation (x : E.Carrier) :=
  extensionIntermediate_discreteValuation F E f (x : E.Carrier)

end Langlands.LocalClassField
