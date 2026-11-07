import Langlands.Weil.Local.ExtensionWeil
import Langlands.LocalFactor.RankOne
import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
import Langlands.WeilDeligne.InductionAlong
import Mathlib.GroupTheory.Transfer

/-!
# Local Weil transfer and field inclusion

The genuine finite-index transfer along an embedding of p-adic fields
corresponds to inclusion of multiplicative groups under geometric reciprocity.
This module states the square without proving or assuming it.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u v

/-- Geometric local Weil reciprocity carries the actual coset-product transfer
along a field embedding to inclusion of field units. -/
def ExtensionWeilTransferReciprocityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier)
    (eF : LocalFactor.RankOne.ReciprocityCandidate F)
    (eE : LocalFactor.RankOne.ReciprocityCandidate E),
    GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF →
    GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE →
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    haveI := Weil.Local.extensionWeilMap_range_finiteIndex F E f
    ∀ y : Weil.Local.localWeilGroup F,
      MonoidHom.transfer
          ((LocalFactor.RankOne.reciprocityUnits E eE).toMonoidHom.comp
            (InductionAlong.rangeInverse (Weil.Local.extensionWeilMap F E f).toMonoidHom
              (Weil.Local.extensionWeilMap_injective F E f))) y =
        Units.map f.toRingHom.toMonoidHom (LocalFactor.RankOne.reciprocityUnits F eF y)

end Langlands.LocalClassField
