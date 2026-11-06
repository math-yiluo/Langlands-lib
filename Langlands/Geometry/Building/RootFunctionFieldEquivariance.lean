import Langlands.Geometry.Building.RootFunctionFieldRestriction
import Langlands.Geometry.Building.SplitTorusNormalizerBaseChange
import Mathlib.GroupTheory.GroupAction.Hom

/-! # Equivariant restriction of actual root-function families -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.RootFunctionFamily

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G

/-- Actual restriction is equivariant for every upstairs real translation,
using the inverse of the actual split cocharacter base-change equivalence. -/
def fieldRestrictTranslationHom (hS : IsSplitTorus S.toGrp) :
    AddActionHom (splitCocharacterBaseChange (K := K) S hS).symm
      (RootFunctionFamily S_K G_K) (RootFunctionFamily S G) where
  toFun := fieldRestrict (k := k)
  map_vadd' v ψ := by
    simpa only [LinearEquiv.apply_symm_apply] using
      fieldRestrict_vadd hS ψ ((splitCocharacterBaseChange (K := K) S hS).symm v)

variable (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

/-- Actual field restriction intertwines the normalizer actions through the
actual extended rational point, with no action-comparison premise. -/
theorem fieldRestrict_normalizer (n : normalizerPoints i)
    (ψ : RootFunctionFamily S_K G_K) :
    fieldRestrict (k := k) (normalizerPointsFieldExtend (K := K) i n • ψ) =
      n • fieldRestrict (k := k) ψ := by
  ext a g
  rw [fieldRestrict_apply, smul_apply, smul_apply, fieldRestrict_apply,
    ← map_inv (normalizerPointsFieldExtend (K := K) i) n,
    ← characterBaseChange_weylAction]
  simp only [normalizerPointsFieldExtend_coe, map_mul, map_inv]

/-- Restrict the upstairs normalizer action along actual normalizer-point
extension, and package actual field restriction as an equivariant map. -/
def fieldRestrictNormalizerHom :
    letI : MulAction (normalizerPoints i) (RootFunctionFamily S_K G_K) :=
      MulAction.compHom _ (normalizerPointsFieldExtend (K := K) i)
    RootFunctionFamily S_K G_K →[normalizerPoints i] RootFunctionFamily S G :=
  letI : MulAction (normalizerPoints i) (RootFunctionFamily S_K G_K) :=
    MulAction.compHom _ (normalizerPointsFieldExtend (K := K) i)
  { toFun := fieldRestrict (k := k)
    map_smul' := fieldRestrict_normalizer (K := K) i }

end Langlands.Geometry.Building.RootFunctionFamily
