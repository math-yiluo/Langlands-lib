import Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationStatement
import Langlands.Geometry.Building.TwistedFixedTranslationAveraging
import Langlands.Geometry.Building.TwistedFixedTranslationSplitDescent
import Langlands.LocalField.ValuativeInfinite

/-! # Proof that twisted-fixed translations of the special apartment are split directions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- **Derived form of KP 9.3.13 (first paragraph of the proof), in the reduced translation
space.** KP's `V(T′)^Γ = V(S′)` concerns the subtori in `G_der`; this theorem instead
concludes membership in `splitTranslationDirections`, the image of `V(S_K)` modulo the root
annihilator. Over `K = inertiaFixedField F` (Galois over `F`,
infinite), every twisted-fixed cocharacter of `T_K` comes from `S_K`
(`TwistedFixedTranslationSplitDescent.exists_split_of_twisted_fixed`), and the
finite-image averaging argument
(`TwistedFixedTranslationAveraging.mem_splitTranslationDirections_of_inv_mul_conjugate`)
passes from twisted-fixed cocharacters to twisted-fixed reduced translations. -/
theorem unramifiedTwistedFixedTranslation :
    UnramifiedTwistedFixedTranslationStatement.{u} := by
  intro F _ _ _ _ G hG S iS hS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  intro hiT
  let : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro h hh n hn v hv
  have : Infinite F := LocalField.infinite_of_isNonarchimedeanLocalField F
  have : Infinite (inertiaFixedField F) :=
    Infinite.of_injective (algebraMap F (inertiaFixedField F))
      (algebraMap F (inertiaFixedField F)).injective
  have hfix := fun lam hlam => TwistedFixedTranslationSplitDescent.exists_split_of_twisted_fixed
      F (inertiaFixedField F) iT hS hf h hh n hn lam hlam
  exact TwistedFixedTranslationAveraging.mem_splitTranslationDirections_of_inv_mul_conjugate
    iT f hiT h n hn hfix v hv

end Langlands.Geometry.Building
