import Langlands.Shimura.PEL.HarrisTaylorCMDvrPolarization
import Langlands.Shimura.PEL.PolarizedWeilLevelClasses
import Langlands.AlgebraicGeometry.Picard.DualRationalBaseChange

/-! # Extending a faithful polarized rational action over a DVR -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

section Comparison

variable (P : Prerequisites.{0}) {S T : Scheme.{0}} (b : T ⟶ S) (B : AbelianScheme S)
    (W : DualWitness B) (WK : DualWitness ((baseChange b).obj B))
    (addS : DualSchemeMapAdditivity P.preservation P.stability B B W.hasDual W.hasDual)
    (addK : DualSchemeMapAdditivity P.preservation P.stability
      ((baseChange b).obj B) ((baseChange b).obj B) WK.hasDual WK.hasDual)

local notation "BK" => Functor.obj (baseChange b) B
local notation "DA" => DualWitness.dual P W
local notation "DB" => Functor.obj (baseChange b) DA
local notation "DK" => DualWitness.dual P WK
local notation "cmp" => DualWitness.baseChangeIso P W b WK
local notation "dualS" => dualHom0 P.preservation P.composition P.unitCoherence P.associativity
  P.comparison P.symmetry P.stability W.hasDual W.hasDual addS W.inverseBundle W.evaluation
  W.inverseBundle W.evaluation W.geometry W.geometry
local notation "dualK" => dualHom0 P.preservation P.composition P.unitCoherence P.associativity
  P.comparison P.symmetry P.stability WK.hasDual WK.hasDual addK WK.inverseBundle WK.evaluation
  WK.inverseBundle WK.evaluation WK.geometry WK.geometry
local notation "pull" => rationalDualBaseChangeHom P.preservation P.stability P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.universality P.compatibility b B
  W.hasDual W.geometry W.inverseBundle W.evaluation
  WK.hasDual WK.geometry WK.inverseBundle WK.evaluation
local notation "CompatibleS" => IsInvolutionCompatible P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability W.hasDual addS W.inverseBundle W.evaluation W.geometry
local notation "CompatibleK" => IsInvolutionCompatible P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability WK.hasDual addK WK.inverseBundle WK.evaluation WK.geometry

private theorem cancel_comp0_iso {X Y Z : AbelianScheme T} (e : Y ≅ Z) :
    Function.Injective (fun f : Hom0 X Y => comp0 X Y Z f (homToHom0 e.hom)) := by
  intro f g h
  have h' := congrArg (fun k => comp0 X Z Y k (homToHom0 e.inv)) h
  simpa only [comp0_assoc, comp0_homToHom0, Iso.hom_inv_id, homToHom0_id, comp0_id0] using h'

set_option maxHeartbeats 1600000 in
private theorem involutionCompatible_of_faithful_restriction
    (naturality : DualAbelianBaseChangeNaturalityStatement.{0})
    (hinj : Function.Injective (rationalBaseChangeHom (A := B) (B := DA) b))
    {R : Type} [Ring R] [StarRing R] (i : R →+* End0 B) (lam : Hom0 B DA)
    (h : CompatibleK ((rationalBaseChangeEnd b B).toRingHom.comp i) (pull lam)) :
    CompatibleS i lam := by
  intro r
  change comp0 B B DA (i r).asHom lam = comp0 B DA DA lam (dualS (i (star r)).asHom)
  apply hinj
  have hleft : rationalBaseChangeHom b (comp0 B B DA (i r).asHom lam) =
      comp0 BK BK DB (rationalBaseChangeHom b (i r).asHom) (rationalBaseChangeHom b lam) :=
    rationalBaseChangeHom_comp b (i r).asHom lam
  have hright : rationalBaseChangeHom b (comp0 B DA DA lam (dualS (i (star r)).asHom)) =
      comp0 BK DB DB (rationalBaseChangeHom b lam)
        (rationalBaseChangeHom b (dualS (i (star r)).asHom)) :=
    rationalBaseChangeHom_comp b lam (dualS (i (star r)).asHom)
  rw [hleft, hright]
  apply cancel_comp0_iso cmp
  have hnat : comp0 DB DB DK (rationalBaseChangeHom b (dualS (i (star r)).asHom))
        (homToHom0 (cmp).hom) =
      comp0 DB DK DK (homToHom0 (cmp).hom) (dualK (rationalBaseChangeHom b (i (star r)).asHom)) :=
    dualHom0_baseChange_of_naturality P.preservation P.stability P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.universality P.compatibility b B
      W.hasDual W.geometry W.inverseBundle W.evaluation WK.hasDual WK.geometry
      WK.inverseBundle WK.evaluation B W.hasDual W.geometry W.inverseBundle W.evaluation
      WK.hasDual WK.geometry WK.inverseBundle WK.evaluation addS addK naturality (i (star r)).asHom
  calc
    _ = comp0 BK BK DK (rationalBaseChangeHom b (i r).asHom) (pull lam) :=
      comp0_assoc _ _ _
    _ = comp0 BK DK DK (pull lam) (dualK (rationalBaseChangeHom b (i (star r)).asHom)) := h r
    _ = _ := by
      change comp0 BK DK DK
        (comp0 BK DB DK (rationalBaseChangeHom b lam) (homToHom0 (cmp).hom)) _ = _
      rw [comp0_assoc, ← hnat, ← comp0_assoc]

end Comparison

section Extension

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    (P : Prerequisites.{0}) (naturality : DualAbelianBaseChangeNaturalityStatement.{0})
    {R : Type} [Ring R] [Algebra ℚ R] [StarRing R]

local notation "j" => Spec.algebraMap V K
local notation "Action" => Langlands.Shimura.PEL.PolarizedWeilLevel.PolarizedAction
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality (Spec (CommRingCat.of V)) R

set_option maxHeartbeats 2400000 in
/-- Extend the rational action and doubled polarization on the given good model.
The generic faithfulness and involution equation give the same conditions over the DVR. -/
def extendDvrPolarizedAction (B : AbelianScheme (Spec (.of V))) (W : DualWitness B)
    (addS : DualSchemeMapAdditivity P.preservation P.stability B B W.hasDual W.hasDual)
    (addK : DualSchemeMapAdditivity P.preservation P.stability ((baseChange j).obj B)
      ((baseChange j).obj B) (W.pullback P j).hasDual (W.pullback P j).hasDual)
    (i : R →ₐ[ℚ] End0 ((baseChange j).obj B)) (hi : Function.Injective i)
    (lam : (baseChange j).obj B ⟶ (W.pullback P j).dual P)
    (hlam : (W.pullback P j).IsPolarization P lam)
    (h : IsInvolutionCompatible P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability (W.pullback P j).hasDual addK
      (W.pullback P j).inverseBundle (W.pullback P j).evaluation (W.pullback P j).geometry
      i.toRingHom (homToHom0 lam)) : Action := by
  let WK := W.pullback P j
  let i₀ : R →ₐ[ℚ] End0 B := extendDvrRationalAction (V := V) (A := R) K B i
  let lam₀ := extendDvrPolarizationDouble (V := V) K P B W lam hlam
  have hi₀ := rationalBaseChangeEnd_extendDvrRationalAction (V := V) (A := R) K B i
  refine
    { actionObj := RationalAlgebraAction.of B i₀
      hasDual := W.hasDual
      geometry := W.geometry
      inversePoincare := W.inverseBundle
      evaluation := W.evaluation
      dualEndAdditivity := addS
      polarization := lam₀.val
      isPolarization := lam₀.property
      faithful := ?_
      involutionCompatible := ?_ }
  · intro r s hrs
    apply hi
    have hm := congrArg (fun f : End0 B => rationalBaseChangeEnd j B f) hrs
    change ((rationalBaseChangeEnd j B).comp i₀) r = ((rationalBaseChangeEnd j B).comp i₀) s at hm
    rw [hi₀] at hm
    exact hm
  · apply involutionCompatible_of_faithful_restriction P j B W WK addS addK naturality
      (dvrGenericRationalHom_bijective (V := V) K B (W.dual P)).1
    erw [rationalDualBaseChangeHom_homToHom0]
    change IsInvolutionCompatible P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability WK.hasDual addK WK.inverseBundle WK.evaluation WK.geometry
      ((rationalBaseChangeEnd j B).comp i₀).toRingHom
      (homToHom0 (W.pullbackMap P j WK lam₀.val))
    rw [hi₀, show W.pullbackMap P j WK lam₀.val = 2 • lam from
      pullbackMap_extendDvrPolarizationDouble (V := V) K P B W lam hlam]
    rw [two_nsmul, map_add]
    erw [← two_smul ℚ (homToHom0 lam)]
    exact IsInvolutionCompatible.smul P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability WK.hasDual addK
      WK.inverseBundle WK.evaluation WK.geometry h 2

end Extension

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
