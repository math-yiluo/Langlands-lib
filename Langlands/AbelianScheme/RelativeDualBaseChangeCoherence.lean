import Langlands.AbelianScheme.RelativeIntegralActionComparison
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeCoherence

/-! # Actual dual-valued pullback along morphisms over a base -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- On a literal composite triangle, the relative comparison is the ordinary
composition comparison. -/
theorem relativeBaseChangeComparisonIso_homMk
    {S S' S'' : Scheme.{u}} (B : AbelianScheme S) (b : S' ⟶ S) (c : S'' ⟶ S') :
    relativeBaseChangeComparisonIso B
        (Over.homMk c rfl : Over.mk (c ≫ b) ⟶ Over.mk b) =
      baseChangeCompIso b c B := by
  apply Iso.ext_inv
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (Langlands.GroupScheme.Cartier.baseChangeCompIso_inv_fst
      B.toCommGroupScheme
      (Over.homMk c rfl : Over.mk (c ≫ b) ⟶ Over.mk b)).trans
      (Langlands.GroupScheme.baseChangeCompIso_inv_fst b c B.toGrp).symm
  · exact (Over.w
      (Langlands.GroupScheme.Cartier.baseChangeCompIso B.toCommGroupScheme
        (Over.homMk c rfl : Over.mk (c ≫ b) ⟶ Over.mk b)).inv.hom.hom).trans
      (Over.w (Langlands.GroupScheme.baseChangeCompIso b c B.toGrp).inv.hom.hom).symm

section Relative

variable
    (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (compatibility : DualAbelianBaseChangeStatement.{u})
    {S : Scheme.{u}} (B : AbelianScheme S)
    (hB : HasDualScheme B) (geometryB : DualSchemeGeometry B hB)
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    {T T' : Over S} (f : T' ⟶ T)
    (hT : HasDualScheme ((baseChange T.hom).obj B))
    (geometryT : DualSchemeGeometry ((baseChange T.hom).obj B) hT)
    (MT : LineBundle ((relativeSpace ((baseChange T.hom).obj B).X.hom).obj
      (dualScheme ((baseChange T.hom).obj B) hT)))
    (evaluationT : tensorObj (poincareFamily ((baseChange T.hom).obj B) hT).obj.carrier
      MT.obj ≅ structureSheaf ((relativeSpace ((baseChange T.hom).obj B).X.hom).obj
        (dualScheme ((baseChange T.hom).obj B) hT)))
    (hDirect : HasDualScheme ((baseChange T'.hom).obj B))
    (geometryDirect : DualSchemeGeometry ((baseChange T'.hom).obj B) hDirect)
    (MDirect : LineBundle ((relativeSpace ((baseChange T'.hom).obj B).X.hom).obj
      (dualScheme ((baseChange T'.hom).obj B) hDirect)))
    (evaluationDirect : tensorObj
      (poincareFamily ((baseChange T'.hom).obj B) hDirect).obj.carrier
      MDirect.obj ≅ structureSheaf ((relativeSpace ((baseChange T'.hom).obj B).X.hom).obj
        (dualScheme ((baseChange T'.hom).obj B) hDirect)))
    (hStep : HasDualScheme ((baseChange f.left).obj ((baseChange T.hom).obj B)))
    (geometryStep : DualSchemeGeometry
      ((baseChange f.left).obj ((baseChange T.hom).obj B)) hStep)
    (MStep : LineBundle
      ((relativeSpace ((baseChange f.left).obj ((baseChange T.hom).obj B)).X.hom).obj
        (dualScheme ((baseChange f.left).obj ((baseChange T.hom).obj B)) hStep)))
    (evaluationStep : tensorObj
      (poincareFamily ((baseChange f.left).obj ((baseChange T.hom).obj B)) hStep).obj.carrier
      MStep.obj ≅
      structureSheaf
        ((relativeSpace ((baseChange f.left).obj ((baseChange T.hom).obj B)).X.hom).obj
          (dualScheme ((baseChange f.left).obj ((baseChange T.hom).obj B)) hStep)))

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "mapT" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility T.hom B
  hB geometryB MB evaluationB hT geometryT MT evaluationT
local notation "mapDirect" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility T'.hom B
  hB geometryB MB evaluationB hDirect geometryDirect MDirect evaluationDirect
local notation "mapStep" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility f.left
  (Functor.obj (baseChange T.hom) B) hT geometryT MT evaluationT
  hStep geometryStep MStep evaluationStep
local notation "dualComparison" => dualAbelianSchemeMapFromEvaluation
  hDirect geometryDirect preservation MDirect evaluationDirect stability composition
  unitCoherence associativity comparison symmetry hStep geometryStep MStep evaluationStep

/-- The actual contravariant dual of the canonical relative comparison,
between the displayed evaluation constructions. -/
def relativeDualBaseChangeComparisonIso :
    dualAbelianSchemeFromEvaluation
        ((baseChange f.left).obj ((baseChange T.hom).obj B))
        hStep geometryStep preservation MStep evaluationStep stability composition
        unitCoherence associativity comparison symmetry ≅
      dualAbelianSchemeFromEvaluation ((baseChange T'.hom).obj B)
        hDirect geometryDirect preservation MDirect evaluationDirect stability composition
        unitCoherence associativity comparison symmetry :=
  dualAbelianSchemeIsoFromEvaluation preservation stability composition unitCoherence
    associativity comparison symmetry ((baseChange T'.hom).obj B)
    hDirect geometryDirect MDirect evaluationDirect
    hStep geometryStep MStep evaluationStep (relativeBaseChangeComparisonIso B f)

/-- Pulling the successive dual-valued map back through the canonical relative
comparison gives canonical direct pullback of the original fixed map. -/
theorem dualAbelianBaseChangeMap_relative_comp_pullback (lam : B ⟶ DB) :
    ((relativeBaseChangeComparisonIso B f).hom ≫ mapStep (mapT lam)) ≫
        dualComparison (relativeBaseChangeComparisonIso B f).hom =
      mapDirect lam := by
  obtain ⟨X, b, rfl⟩ := Over.mk_surjective T
  obtain ⟨Y, d, rfl⟩ := Over.mk_surjective T'
  obtain ⟨c, hc, rfl⟩ := Over.homMk_surjective f
  change Y ⟶ X at c
  change c ≫ b = d at hc
  subst d
  rw [relativeBaseChangeComparisonIso_homMk]
  exact dualAbelianBaseChangeMap_comp_pullback preservation stability composition
    unitCoherence associativity comparison symmetry universality compatibility B
    hB geometryB MB evaluationB b c hT geometryT MT evaluationT
    hDirect geometryDirect MDirect evaluationDirect hStep geometryStep MStep evaluationStep lam

end Relative

end Langlands.AbelianScheme
