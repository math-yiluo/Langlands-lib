import Langlands.Shimura.PEL.PolarizedWeilOrderModel
import Langlands.Shimura.PEL.PolarizedWeilLevelClasses
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport
import Langlands.AlgebraicGeometry.Picard.IntegralDualPullback
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeMapAdditivityProof
import Mathlib.CategoryTheory.Conj

/-! # Transporting the generic polarized action to a specified generic fibre -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

private def conjugateEnd0 {S : Scheme.{0}} {B C : AbelianScheme S} (e : B ≅ C) :
    End0 C ≃ₐ[ℚ] End0 B := by
  let eQ := (rationalization S).mapIso e
  let h := eQ.symm.conj
  refine { h with map_add' := ?_, commutes' := ?_ }
  · intro f g
    change comp0 B C B (homToHom0 e.hom) (comp0 C C B (f + g) (homToHom0 e.inv)) =
      comp0 B C B (homToHom0 e.hom) (comp0 C C B f (homToHom0 e.inv)) +
        comp0 B C B (homToHom0 e.hom) (comp0 C C B g (homToHom0 e.inv))
    simp only [map_add, LinearMap.add_apply]
  · intro q
    change comp0 B C B (homToHom0 e.hom)
        (comp0 C C B (algebraMap ℚ (End0 C) q) (homToHom0 e.inv)) =
      algebraMap ℚ (End0 B) q
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change comp0 B C B (homToHom0 e.hom)
        (comp0 C C B (q • id0 C) (homToHom0 e.inv)) = q • id0 B
    simp only [map_smul, LinearMap.smul_apply, id0_comp0, comp0_homToHom0,
      Iso.hom_inv_id, homToHom0_id]

private theorem conjugateEnd0_intertwines {S : Scheme.{0}} {B C : AbelianScheme S}
    (e : B ≅ C) (f : End0 C) :
    comp0 B B C (conjugateEnd0 e f) (homToHom0 e.hom) =
      comp0 B C C (homToHom0 e.hom) f := by
  change comp0 B B C
      (comp0 B C B (homToHom0 e.hom) (comp0 C C B f (homToHom0 e.inv)))
      (homToHom0 e.hom) = _
  simp only [comp0_assoc, comp0_homToHom0, Iso.inv_hom_id, homToHom0_id, comp0_id0]

variable (P : Prerequisites.{0}) {S : Scheme.{0}} [QuasiSeparatedSpace S]
  {R : Type} [Ring R] [Algebra ℚ R] [StarRing R]

local notation "PObj" => PolarizedWeilLevel.PolarizedAction P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality S R

set_option maxHeartbeats 2200000 in
/-- Transport the actual polarized rational action to an isomorphic abelian
scheme with specified dual witnesses. The polarization is the actual dual pullback. -/
def transportDvrGenericPolarizedAction (Y : PObj) (B : AbelianScheme S)
    (W : DualWitness B) (e : B ≅ Y.actionObj.abelianScheme) : PObj := by
  let C := Y.actionObj.abelianScheme
  let WY := Langlands.Shimura.PEL.PolarizedWeilLevel.PolarizedAction.dualWitness P Y
  let i : R →ₐ[ℚ] End0 B := (conjugateEnd0 e).toAlgHom.comp Y.actionObj.action
  let addBB := relativeDualSchemeMapAdditivity P.preservation P.stability S B B W.hasDual W.hasDual
  let addBC := relativeDualSchemeMapAdditivity P.preservation P.stability S B C W.hasDual Y.hasDual
  let lam := integralDualPullbackHom P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability W.hasDual Y.hasDual W.geometry Y.geometry
    W.inverseBundle W.evaluation Y.inversePoincare Y.evaluation e.hom Y.polarization
  refine
    { actionObj := RationalAlgebraAction.of B i
      hasDual := W.hasDual
      geometry := W.geometry
      inversePoincare := W.inverseBundle
      evaluation := W.evaluation
      dualEndAdditivity := addBB
      polarization := lam
      isPolarization := ?_
      faithful := (conjugateEnd0 e).injective.comp Y.faithful
      involutionCompatible := ?_ }
  · exact isPolarization_integralDualPullbackHom P.preservation P.square P.universality
      P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      W.hasDual Y.hasDual W.geometry Y.geometry W.inverseBundle W.evaluation
      Y.inversePoincare Y.evaluation e.hom (isIsogeny_of_iso e)
      (isIsogeny_of_iso (W.mapIso P WY e)) Y.polarization Y.isPolarization
  · have htransport := IsInvolutionCompatible.rationalDualPullback P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual Y.hasDual
      W.geometry Y.geometry W.inverseBundle W.evaluation Y.inversePoincare Y.evaluation
      addBC addBB Y.dualEndAdditivity i.toRingHom Y.actionObj.action.toRingHom
      (homToHom0 e.hom) (fun r => conjugateEnd0_intertwines e (Y.actionObj.action r))
      (homToHom0 Y.polarization) Y.involutionCompatible
    have hl := homToHom0_integralDualPullback P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability W.hasDual Y.hasDual W.geometry Y.geometry
      W.inverseBundle W.evaluation Y.inversePoincare Y.evaluation addBC e.hom Y.polarization
    rw [← hl] at htransport
    exact htransport

set_option maxHeartbeats 1000000 in
/-- The transported action has the supplied underlying actual comparison in
the rational action category. -/
def transportDvrGenericActionIso (Y : PObj) (B : AbelianScheme S)
    (W : DualWitness B) (e : B ≅ Y.actionObj.abelianScheme) :
    (transportDvrGenericPolarizedAction P Y B W e).actionObj ≅ Y.actionObj :=
  RationalAlgebraAction.isoMk ((rationalization S).mapIso e)
    (fun r => conjugateEnd0_intertwines e (Y.actionObj.action r))

set_option maxHeartbeats 1000000 in
/-- The transported polarization is the rational dual pullback by the given
integral isomorphism after rationalization. -/
theorem homToHom0_transportDvrGenericPolarization (Y : PObj) (B : AbelianScheme S)
    (W : DualWitness B) (e : B ≅ Y.actionObj.abelianScheme) :
    homToHom0 (transportDvrGenericPolarizedAction P Y B W e).polarization =
      rationalDualPullbackHom0 P.preservation P.composition P.unitCoherence P.associativity
        P.comparison P.symmetry P.stability W.hasDual Y.hasDual W.geometry Y.geometry
        W.inverseBundle W.evaluation Y.inversePoincare Y.evaluation
        (relativeDualSchemeMapAdditivity P.preservation P.stability S B
          Y.actionObj.abelianScheme W.hasDual Y.hasDual)
        (homToHom0 e.hom) (homToHom0 Y.polarization) :=
  homToHom0_integralDualPullback P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability W.hasDual Y.hasDual W.geometry Y.geometry
    W.inverseBundle W.evaluation Y.inversePoincare Y.evaluation
    (relativeDualSchemeMapAdditivity P.preservation P.stability S B
      Y.actionObj.abelianScheme W.hasDual Y.hasDual)
    e.hom Y.polarization

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
