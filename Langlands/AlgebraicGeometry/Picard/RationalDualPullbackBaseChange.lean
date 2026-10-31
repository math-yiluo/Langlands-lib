import Langlands.AlgebraicGeometry.Picard.DualRationalBaseChange
import Langlands.AbelianScheme.Tate.WeilHom0PullbackCoherence

/-! # Canonical base change of the actual rational dual-pullback equation -/

universe u

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
  {S S' : Scheme.{u}} (b : S' ⟶ S) (A B : AbelianScheme S)
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (hB : HasDualScheme B) (geometryB : DualSchemeGeometry B hB)
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (hA' : HasDualScheme ((baseChange b).obj A))
  (geometryA' : DualSchemeGeometry ((baseChange b).obj A) hA')
  (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hA')))
  (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
    MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))
  (hB' : HasDualScheme ((baseChange b).obj B))
  (geometryB' : DualSchemeGeometry ((baseChange b).obj B) hB')
  (MB' : LineBundle ((relativeSpace ((baseChange b).obj B).X.hom).obj
    (dualScheme ((baseChange b).obj B) hB')))
  (evaluationB' : tensorObj (poincareFamily ((baseChange b).obj B) hB').obj.carrier
    MB'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj B).X.hom).obj
      (dualScheme ((baseChange b).obj B) hB')))
  (additivityAB : DualSchemeMapAdditivity preservation stability A B hA hB)
  (additivityChanged : DualSchemeMapAdditivity preservation stability
    ((baseChange b).obj A) ((baseChange b).obj B) hA' hB')

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "baseA" => Functor.obj (baseChange b) A
local notation "baseB" => Functor.obj (baseChange b) B
local notation "DA'" => dualAbelianSchemeFromEvaluation baseA hA' geometryA' preservation MA'
  evaluationA' stability composition unitCoherence associativity comparison symmetry
local notation "DB'" => dualAbelianSchemeFromEvaluation baseB hB' geometryB' preservation MB'
  evaluationB' stability composition unitCoherence associativity comparison symmetry
local notation "EA" => dualAbelianBaseChangeIso preservation stability composition unitCoherence
  associativity comparison symmetry universality compatibility b A
  hA geometryA MA evaluationA hA' geometryA' MA' evaluationA'
local notation "dual0" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hB additivityAB MA evaluationA MB evaluationB geometryA geometryB
local notation "pullA" => rationalDualBaseChangeHom preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b A
  hA geometryA MA evaluationA hA' geometryA' MA' evaluationA'
local notation "pullB" => rationalDualBaseChangeHom preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b B
  hB geometryB MB evaluationB hB' geometryB' MB' evaluationB'
local notation "oldPull" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB additivityAB
local notation "oldLinear" => rationalDualPullbackHom0Linear preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB additivityAB
local notation "changedLinear" => rationalDualPullbackHom0Linear preservation composition
  unitCoherence associativity comparison symmetry stability hA' hB' geometryA' geometryB'
  MA' evaluationA' MB' evaluationB' additivityChanged
local notation "oldMultiple" => IsRationalDualPullbackMultiple preservation composition
  unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
  MA evaluationA MB evaluationB additivityAB
local notation "changedMultiple" => IsRationalDualPullbackMultiple preservation composition
  unitCoherence associativity comparison symmetry stability hA' hB' geometryA' geometryB'
  MA' evaluationA' MB' evaluationB' additivityChanged

/-- Transport the dual-valued map canonically and pull it back by the actual
rational base change of the original homomorphism. -/
def rationalDualPullbackBaseChangeHom (f : Hom0 A B) : Hom0 B DB →ₗ[ℚ] Hom0 baseA DA' :=
  (changedLinear (rationalBaseChangeHom b f)).comp pullB

local notation "changedPull" => rationalDualPullbackBaseChangeHom preservation stability
  composition unitCoherence associativity comparison symmetry universality compatibility
  b A B hB geometryB MB evaluationB
  hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB' additivityChanged

/-- The two actual orders of base change and dual pullback agree under the named
integral canonical-dual naturality statement. -/
theorem rationalDualPullbackBaseChangeHom_commutes
    (naturality : DualAbelianBaseChangeNaturalityStatement.{u})
    (f : Hom0 A B) (lamB : Hom0 B DB) :
    pullA (oldPull f lamB) = changedPull f lamB := by
  have houter :
      rationalBaseChangeHom b (comp0 A DB DA (comp0 A B DB f lamB) (dual0 f)) =
        comp0 baseA ((baseChange b).obj DB) ((baseChange b).obj DA)
          (rationalBaseChangeHom b (comp0 A B DB f lamB))
          (rationalBaseChangeHom b (dual0 f)) :=
    rationalBaseChangeHom_comp b (comp0 A B DB f lamB) (dual0 f)
  have hinner :
      rationalBaseChangeHom b (comp0 A B DB f lamB) =
        comp0 baseA baseB ((baseChange b).obj DB)
          (rationalBaseChangeHom b f) (rationalBaseChangeHom b lamB) :=
    rationalBaseChangeHom_comp b f lamB
  have hnat := dualHom0_baseChange_of_naturality preservation stability composition unitCoherence
    associativity comparison symmetry universality compatibility b A hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' B hB geometryB MB evaluationB
    hB' geometryB' MB' evaluationB' additivityAB additivityChanged naturality f
  simp only [rationalDualPullbackBaseChangeHom, LinearMap.comp_apply,
    rationalDualPullbackHom0Linear_apply, rationalDualPullbackHom0,
    rationalDualBaseChangeHom_apply]
  rw [houter, hinner]
  simp only [comp0_assoc]
  rw [hnat]

/-- The constructed rational-linear maps form the same commuting square. -/
theorem rationalDualPullbackBaseChangeHom_square
    (naturality : DualAbelianBaseChangeNaturalityStatement.{u}) (f : Hom0 A B) :
    (pullA).comp (oldLinear f) = changedPull f := by
  apply LinearMap.ext
  intro lamB
  exact rationalDualPullbackBaseChangeHom_commutes preservation stability composition
    unitCoherence associativity comparison symmetry universality compatibility b A B
    hA geometryA MA evaluationA hB geometryB MB evaluationB
    hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB'
    additivityAB additivityChanged naturality f lamB

/-- The actual geometric multiplier equation survives canonical pullback with
the same rational multiplier, before taking any Tate realization. -/
theorem IsRationalDualPullbackMultiple.baseChange_of_naturality
    (naturality : DualAbelianBaseChangeNaturalityStatement.{u})
    (q : ℚ) (f : Hom0 A B) (lamA : Hom0 A DA) (lamB : Hom0 B DB)
    (hmultiple : oldMultiple q f lamA lamB) :
    changedMultiple q (rationalBaseChangeHom b f) (pullA lamA) (pullB lamB) := by
  change changedPull f lamB = q • pullA lamA
  rw [← rationalDualPullbackBaseChangeHom_commutes preservation stability composition
    unitCoherence associativity comparison symmetry universality compatibility b A B
    hA geometryA MA evaluationA hB geometryB MB evaluationB
    hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB'
    additivityAB additivityChanged naturality f lamB]
  change oldPull f lamB = q • lamA at hmultiple
  rw [hmultiple]
  exact map_smul pullA q lamA

/-- For integral dual-valued maps the multiplier equation uses exactly the
existing canonical integral base-change maps at both endpoints. -/
theorem IsRationalDualPullbackMultiple.integral_baseChange_of_naturality
    (naturality : DualAbelianBaseChangeNaturalityStatement.{u})
    (q : ℚ) (f : Hom0 A B) (lamA : A ⟶ DA) (lamB : B ⟶ DB)
    (hmultiple : oldMultiple q f (homToHom0 lamA) (homToHom0 lamB)) :
    changedMultiple q (rationalBaseChangeHom b f)
      (homToHom0 (dualAbelianBaseChangeMap preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility b A
        hA geometryA MA evaluationA hA' geometryA' MA' evaluationA' lamA))
      (homToHom0 (dualAbelianBaseChangeMap preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility b B
        hB geometryB MB evaluationB hB' geometryB' MB' evaluationB' lamB)) := by
  simpa only [rationalDualBaseChangeHom_homToHom0] using
    IsRationalDualPullbackMultiple.baseChange_of_naturality preservation stability composition
      unitCoherence associativity comparison symmetry universality compatibility b A B
      hA geometryA MA evaluationA hB geometryB MB evaluationB
      hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB'
      additivityAB additivityChanged naturality q f (homToHom0 lamA) (homToHom0 lamB) hmultiple

end Langlands.AbelianScheme
