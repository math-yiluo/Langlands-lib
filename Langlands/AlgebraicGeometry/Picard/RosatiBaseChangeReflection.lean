import Langlands.AbelianScheme.BaseChangeSurjectiveRigidity
import Langlands.AbelianScheme.PolarizedFiniteLevel.Data
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof
import Langlands.AlgebraicGeometry.Picard.DualRationalBaseChange

/-! # Reflection of the rational involution equation by surjective base change -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open PolarizedFiniteLevel

variable (P : Prerequisites.{u}) {S T : Scheme.{u}} (b : T ⟶ S)
  {B : AbelianScheme S} (U : DualWitness B) (V : DualWitness ((baseChange b).obj B))
  (addU : DualSchemeMapAdditivity P.preservation P.stability B B U.hasDual U.hasDual)
  (addV : DualSchemeMapAdditivity P.preservation P.stability ((baseChange b).obj B)
    ((baseChange b).obj B) V.hasDual V.hasDual)

local notation "pull" => rationalDualBaseChangeHom P.preservation P.stability P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.universality P.compatibility b B
  U.hasDual U.geometry U.inverseBundle U.evaluation V.hasDual V.geometry V.inverseBundle
  V.evaluation
local notation "dualU" => dualHom0 P.preservation P.composition P.unitCoherence P.associativity
  P.comparison P.symmetry P.stability U.hasDual U.hasDual addU U.inverseBundle U.evaluation
  U.inverseBundle U.evaluation U.geometry U.geometry
local notation "dualV" => dualHom0 P.preservation P.composition P.unitCoherence P.associativity
  P.comparison P.symmetry P.stability V.hasDual V.hasDual addV V.inverseBundle V.evaluation
  V.inverseBundle V.evaluation V.geometry V.geometry

/-- Equality of the rational Rosati composites can be checked on a base
change surjective on points. -/
theorem IsInvolutionCompatible.of_surjective_baseChange [Surjective b]
    {A : Type v} [Ring A] [StarRing A] (i : A →+* End0 B)
    (lam : Hom0 B (U.dual P))
    (h : IsInvolutionCompatible P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability V.hasDual addV V.inverseBundle
      V.evaluation V.geometry ((rationalBaseChangeEnd b B).toRingHom.comp i) (pull lam)) :
    IsInvolutionCompatible P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability U.hasDual addU U.inverseBundle U.evaluation
      U.geometry i lam := by
  intro a
  let e : (baseChange b).obj (U.dual P) ≅ V.dual P :=
    dualAbelianBaseChangeIso P.preservation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.universality P.compatibility b B
    U.hasDual U.geometry U.inverseBundle U.evaluation V.hasDual V.geometry V.inverseBundle
    V.evaluation
  let e₀ : Rationalization.of ((baseChange b).obj (U.dual P)) ≅
      Rationalization.of (V.dual P) := (rationalization T).mapIso e
  have hnat := dualHom0_baseChange_of_naturality P.preservation P.stability P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.universality P.compatibility
    b B U.hasDual U.geometry U.inverseBundle U.evaluation V.hasDual V.geometry
    V.inverseBundle V.evaluation B U.hasDual U.geometry U.inverseBundle U.evaluation
    V.hasDual V.geometry V.inverseBundle V.evaluation addU addV dualAbelianBaseChangeNaturality
    (i (star a)).asHom
  change comp0 _ _ _ (rationalBaseChangeHom b (dualU (i (star a)).asHom)) e₀.hom =
    comp0 _ _ _ e₀.hom (dualV (rationalBaseChangeHom b (i (star a)).asHom)) at hnat
  apply rationalBaseChangeIsFaithful_of_surjective b B (U.dual P)
  apply (cancel_mono e₀.hom).mp
  change comp0 _ _ _
     (rationalBaseChangeHom b (comp0 _ _ _ (i a).asHom lam)) e₀.hom =
    comp0 _ _ _ (rationalBaseChangeHom b (comp0 _ _ _ lam (dualU (i (star a)).asHom))) e₀.hom
  have hl : rationalBaseChangeHom b (comp0 B B (U.dual P) (i a).asHom lam) =
      comp0 _ _ _ (rationalBaseChangeHom b (i a).asHom) (rationalBaseChangeHom b lam) :=
    rationalBaseChangeHom_comp b (A := B) (B := B) (C := U.dual P) (i a).asHom lam
  have hr : rationalBaseChangeHom b
      (comp0 B (U.dual P) (U.dual P) lam (dualU (i (star a)).asHom)) =
      comp0 _ _ _ (rationalBaseChangeHom b lam)
        (rationalBaseChangeHom b (dualU (i (star a)).asHom)) :=
    rationalBaseChangeHom_comp b (A := B) (B := U.dual P) (C := U.dual P)
      lam (dualU (i (star a)).asHom)
  calc
    _ = comp0 _ _ _ (rationalBaseChangeHom b (i a).asHom) (pull lam) := by
      exact (congrArg (fun x => comp0 _ _ _ x e₀.hom) hl).trans (comp0_assoc _ _ _)
    _ = comp0 _ _ _ (pull lam) (dualV (rationalBaseChangeHom b (i (star a)).asHom)) := h a
    _ = _ := by
      change comp0 _ _ _ (comp0 _ _ _ (rationalBaseChangeHom b lam) e₀.hom)
          (dualV (rationalBaseChangeHom b (i (star a)).asHom)) = _
      exact (comp0_assoc _ _ _).trans
        ((congrArg (comp0 _ _ _ (rationalBaseChangeHom b lam)) hnat.symm).trans
          ((comp0_assoc _ _ _).symm.trans (congrArg (fun x => comp0 _ _ _ x e₀.hom) hr.symm)))

end Langlands.AbelianScheme
