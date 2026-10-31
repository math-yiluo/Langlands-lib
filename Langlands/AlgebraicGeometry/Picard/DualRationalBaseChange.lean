import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityStatement
import Langlands.AlgebraicGeometry.Picard.RationalPolarizationCompatibility
import Langlands.AbelianScheme.RationalBaseChange

/-! # Rational canonical-dual base change and involution transport -/

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (compatibility : DualAbelianBaseChangeStatement.{u})
  {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (hA' : HasDualScheme ((baseChange b).obj A))
  (geometryA' : DualSchemeGeometry ((baseChange b).obj A) hA')
  (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hA')))
  (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
    MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "baseA" => Functor.obj (baseChange b) A
local notation "DA'" => dualAbelianSchemeFromEvaluation baseA hA' geometryA' preservation MA'
  evaluationA' stability composition unitCoherence associativity comparison symmetry
local notation "EA" => dualAbelianBaseChangeIso preservation stability composition unitCoherence
  associativity comparison symmetry universality compatibility b A
  hA geometryA MA evaluationA hA' geometryA' MA' evaluationA'

/-- Actual rational pullback followed by the canonical comparison of duals. -/
def rationalDualBaseChangeHom : Hom0 A DA →ₗ[ℚ] Hom0 baseA DA' :=
  ((comp0 baseA ((baseChange b).obj DA) DA').flip (homToHom0 (EA).hom)).comp
    (rationalBaseChangeHom b)

local notation "pullDual" => rationalDualBaseChangeHom preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b A
  hA geometryA MA evaluationA hA' geometryA' MA' evaluationA'

@[simp] theorem rationalDualBaseChangeHom_apply (lam : Hom0 A DA) :
    pullDual lam =
      comp0 baseA ((baseChange b).obj DA) DA'
        (rationalBaseChangeHom b lam) (homToHom0 (EA).hom) := rfl

/-- On an integral homomorphism the rational construction recovers the existing
actual integral dual-valued base-change map. -/
@[simp] theorem rationalDualBaseChangeHom_homToHom0 (lam : A ⟶ DA) :
    pullDual (homToHom0 lam) =
      homToHom0 (dualAbelianBaseChangeMap preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility b A
        hA geometryA MA evaluationA hA' geometryA' MA' evaluationA' lam) := by
  change comp0 _ _ _ (rationalBaseChangeHom b (homToHom0 lam)) (homToHom0 (EA).hom) = _
  rw [homToHom0_apply, rationalBaseChangeHom_tmul]
  change comp0 _ _ _ (homToHom0 ((baseChange b).map lam)) (homToHom0 (EA).hom) = _
  exact comp0_homToHom0 _ _

/-- The same rational unit multiplies the actual transported rational map. -/
@[simp] theorem rationalDualBaseChangeHom_rationalUnitMultiple
    (q : ℚˣ) (lam : Hom0 A DA) :
    pullDual (rationalUnitMultiple q lam) = rationalUnitMultiple q (pullDual lam) :=
  map_smul pullDual (q : ℚ) lam

section Naturality

variable (B : AbelianScheme S)
  (hB : HasDualScheme B) (geometryB : DualSchemeGeometry B hB)
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (hB' : HasDualScheme ((baseChange b).obj B))
  (geometryB' : DualSchemeGeometry ((baseChange b).obj B) hB')
  (MB' : LineBundle ((relativeSpace ((baseChange b).obj B).X.hom).obj
    (dualScheme ((baseChange b).obj B) hB')))
  (evaluationB' : tensorObj (poincareFamily ((baseChange b).obj B) hB').obj.carrier
    MB'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj B).X.hom).obj
      (dualScheme ((baseChange b).obj B) hB')))
  (additivityAB : DualSchemeMapAdditivity preservation stability A B hA hB)
  (additivityChanged : DualSchemeMapAdditivity preservation stability ((baseChange b).obj A)
    ((baseChange b).obj B) hA' hB')

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "baseB" => Functor.obj (baseChange b) B
local notation "DB'" => dualAbelianSchemeFromEvaluation baseB hB' geometryB' preservation MB'
  evaluationB' stability composition unitCoherence associativity comparison symmetry
local notation "EB" => dualAbelianBaseChangeIso preservation stability composition unitCoherence
  associativity comparison symmetry universality compatibility b B
  hB geometryB MB evaluationB hB' geometryB' MB' evaluationB'
local notation "dual0AB" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hB additivityAB MA evaluationA MB evaluationB geometryA geometryB
local notation "dual0Changed" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA' hB' additivityChanged MA' evaluationA' MB' evaluationB'
  geometryA' geometryB'

/-- Tensor extension of the named integral naturality square, using the actual
rational pullback and constructed rational dualization at both endpoints. -/
theorem dualHom0_baseChange_of_naturality
    (naturality : DualAbelianBaseChangeNaturalityStatement.{u}) (f : Hom0 A B) :
    comp0 ((baseChange b).obj DB) ((baseChange b).obj DA) DA'
        (rationalBaseChangeHom b (dual0AB f)) (homToHom0 (EA).hom) =
      comp0 ((baseChange b).obj DB) DB' DA'
        (homToHom0 (EB).hom) (dual0Changed (rationalBaseChangeHom b f)) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
      simp only [dualHom0_tmul, rationalBaseChangeHom_tmul, homToHom0_apply,
        comp0_tmul, mul_one, one_mul]
      exact congrArg (fun g => q ⊗ₜ[ℤ] g)
        (naturality preservation stability composition unitCoherence associativity
          comparison symmetry universality compatibility S S' b A B
          hA geometryA MA evaluationA hB geometryB MB evaluationB
          hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB' f)
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]

end Naturality

section Involution

variable (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
  (additivityChangedAA : DualSchemeMapAdditivity preservation stability
    ((baseChange b).obj A) ((baseChange b).obj A) hA' hA')
  {R : Type v} [Ring R] [StarRing R]

local notation "dual0" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hA additivityAA MA evaluationA MA evaluationA geometryA geometryA
local notation "dual0'" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA' hA' additivityChangedAA MA' evaluationA' MA' evaluationA'
  geometryA' geometryA'

/-- The actual transported rational action and dual-valued map retain the
involution equation under the named integral canonical-dual naturality theorem. -/
theorem IsInvolutionCompatible.baseChange_of_naturality
    (naturality : DualAbelianBaseChangeNaturalityStatement.{u})
    {i : R →+* End0 A} {lam : Hom0 A DA}
    (hlam : IsInvolutionCompatible preservation composition unitCoherence associativity
      comparison symmetry stability hA additivityAA MA evaluationA geometryA i lam) :
    IsInvolutionCompatible preservation composition unitCoherence associativity
      comparison symmetry stability hA' additivityChangedAA MA' evaluationA' geometryA'
      ((rationalBaseChangeEnd b A).toRingHom.comp i) (pullDual lam) := by
  intro r
  change comp0 baseA baseA DA' (rationalBaseChangeHom b (i r))
      (comp0 baseA ((baseChange b).obj DA) DA'
        (rationalBaseChangeHom b lam) (homToHom0 (EA).hom)) =
    comp0 baseA DA' DA'
      (comp0 baseA ((baseChange b).obj DA) DA'
        (rationalBaseChangeHom b lam) (homToHom0 (EA).hom))
      (dual0' (rationalBaseChangeHom b (i (star r))))
  have hleft :
      comp0 baseA baseA ((baseChange b).obj DA)
          (rationalBaseChangeHom b (i r)) (rationalBaseChangeHom b lam) =
        rationalBaseChangeHom b (comp0 A A DA (i r) lam) :=
    (rationalBaseChangeHom_comp b (i r) lam).symm
  have hright :
      rationalBaseChangeHom b (comp0 A DA DA lam (dual0 (i (star r)))) =
        comp0 baseA ((baseChange b).obj DA) ((baseChange b).obj DA)
          (rationalBaseChangeHom b lam)
          (rationalBaseChangeHom b (dual0 (i (star r)))) :=
    rationalBaseChangeHom_comp b lam (dual0 (i (star r)))
  rw [← comp0_assoc, hleft, hlam r, hright, comp0_assoc]
  rw [dualHom0_baseChange_of_naturality preservation stability composition unitCoherence
    associativity comparison symmetry universality compatibility b A hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' A hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' additivityAA additivityChangedAA naturality]
  exact (comp0_assoc _ _ _).symm

end Involution

end Langlands.AbelianScheme
