import Langlands.AlgebraicGeometry.Picard.RationalDualPullbackBaseChange

/-! # Reflection of the rational dual-pullback equation along a faithful base change -/

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

local notation "changedPull" => rationalDualPullbackBaseChangeHom preservation stability
  composition unitCoherence associativity comparison symmetry universality compatibility
  b A B hB geometryB MB evaluationB
  hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB' additivityChanged


/-- If rational pullback along the base map is injective on rational homomorphisms
from `A` to its dual, the geometric multiplier equation descends: its canonical
pullback implies the original equation with the same multiplier. -/
theorem IsRationalDualPullbackMultiple.of_baseChange_of_naturality
    (naturality : DualAbelianBaseChangeNaturalityStatement.{u})
    (hinj : ∀ r : Hom0 A DA, rationalBaseChangeHom b r = 0 → r = 0)
    (q : ℚ) (f : Hom0 A B) (lamA : Hom0 A DA) (lamB : Hom0 B DB)
    (hchanged : changedMultiple q (rationalBaseChangeHom b f) (pullA lamA) (pullB lamB)) :
    oldMultiple q f lamA lamB := by
  change changedPull f lamB = q • pullA lamA at hchanged
  rw [← rationalDualPullbackBaseChangeHom_commutes preservation stability composition
    unitCoherence associativity comparison symmetry universality compatibility b A B
    hA geometryA MA evaluationA hB geometryB MB evaluationB
    hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB'
    additivityAB additivityChanged naturality f lamB] at hchanged
  change oldPull f lamB = q • lamA
  have h2 : pullA (oldPull f lamB - q • lamA) = 0 := by
    rw [map_sub, map_smul, hchanged, sub_self]
  rw [rationalDualBaseChangeHom_apply] at h2
  have h3 : rationalBaseChangeHom b (oldPull f lamB - q • lamA) = 0 := by
    have k := congrArg (fun t => comp0 _ _ _ t (homToHom0 (EA).inv)) h2
    simp only [comp0_assoc, comp0_homToHom0, Iso.hom_inv_id, homToHom0_id, comp0_id0,
      map_zero, LinearMap.zero_apply] at k
    exact k
  exact sub_eq_zero.mp (hinj _ h3)

/-- The integral form: reflection of the multiplier equation for integral
dual-valued maps, through the canonical integral base-change maps. -/
theorem IsRationalDualPullbackMultiple.integral_of_baseChange_of_naturality
    (naturality : DualAbelianBaseChangeNaturalityStatement.{u})
    (hinj : ∀ r : Hom0 A DA, rationalBaseChangeHom b r = 0 → r = 0)
    (q : ℚ) (f : Hom0 A B) (lamA : A ⟶ DA) (lamB : B ⟶ DB)
    (hchanged : changedMultiple q (rationalBaseChangeHom b f)
      (homToHom0 (dualAbelianBaseChangeMap preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility b A
        hA geometryA MA evaluationA hA' geometryA' MA' evaluationA' lamA))
      (homToHom0 (dualAbelianBaseChangeMap preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility b B
        hB geometryB MB evaluationB hB' geometryB' MB' evaluationB' lamB))) :
    oldMultiple q f (homToHom0 lamA) (homToHom0 lamB) := by
  apply IsRationalDualPullbackMultiple.of_baseChange_of_naturality preservation stability
    composition unitCoherence associativity comparison symmetry universality compatibility b A B
    hA geometryA MA evaluationA hB geometryB MB evaluationB
    hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB'
    additivityAB additivityChanged naturality hinj
  simpa only [rationalDualBaseChangeHom_homToHom0] using hchanged

end Langlands.AbelianScheme
