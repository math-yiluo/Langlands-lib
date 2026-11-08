import Langlands.ClassField.Global.RelativeWeilLocalTransfer
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionSum
import Langlands.ClassField.Global.IdeleClassPlaceProduct
import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityTower

/-!
# The local restriction formula from the local transfer square

`LocalInducedRestrictionStatement` follows from the published local transfer square
`ExtensionWeilTransferReciprocityStatement` at equal universes. The local maps are
`localPlaceMap u`.
-/

noncomputable section

set_option autoImplicit false

universe uV u

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField Langlands.VirtualRepresentation
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

/-- The local restriction formula, assuming the local transfer square for one embedding of
p-adic fields. -/
theorem localInducedRestriction_of_extensionSquare
    (hsq : LocalClassField.ExtensionWeilTransferReciprocityStatement.{u, u}) :
    LocalInducedRestrictionStatement.{uV, u} := by
  intro c F K E _ _ _ _ _ _ _ _ _ _ _ h z w _ e ι hι
  have : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
  have hι' : ∀ (g : Weil.Local.localWeilGroup (padicField z)) (y : E),
      closurePlaceEmbedding z w (projection c F E (discreteLocalMap ι g) y) =
        AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
          (closurePlaceEmbedding z w y) := fun g y => hι.2.1 g y
  refine ⟨fun u => localPlaceMap c K z w h (discreteLocalMap ι) hι' u, ?_,
    continuousRestrict_continuousInduceAlong_restrictionInclusion c F K E h z w
      (discreteLocalMap ι) hι'⟩
  intro u eu heu y
  refine transfer_localPlaceMap_of_local c K z w u h (discreteLocalMap ι) hι' e
    (fun y => hι.2.2 y) y _ ?_ (prod_ofAdicCompletion_eq_ideleClassInclusion u.1 _)
  let := (padicField z).algebra
  let := (towerPadicField z u.1).algebra
  let := (towerPadicField z w).algebra
  have := towerPadicField_isScalarTower z u.1
  have := towerPadicField_isScalarTower z w
  exact LocalClassField.extensionWeilTransferReciprocity_tower (padicField z)
    (towerPadicField z u.1) (towerPadicField z w)
    (completionPadicAlgHom z u.1) (completionPadicAlgHom z w)
    ((twistedMap c K z w u).restrictScalars (Padic (residuePrime z))) hsq
    (completionClosureEmbedding_twistedMap c K z w u) eu e heu hι.1 y

end Langlands.ClassField.Global.RelativeWeilGroup
