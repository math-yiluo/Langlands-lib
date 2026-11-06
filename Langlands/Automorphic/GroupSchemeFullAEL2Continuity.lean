import Langlands.Automorphic.GroupSchemeFullAEL2
import Langlands.Automorphic.GroupSchemeQuotientL2Continuity

/-! # Joint continuity on the original full AE cuspidal L2 space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "ρc" => fullAEL2CuspidalRightAction F G hPD hG T i hi I e hc

/-- Restrict the unchanged canonical joint action to the original full cusp subtype. -/
def fullAEL2CuspidalJointRightAction :
    C(AdelicGroupPoints F G × S, S) where
  toFun aφ := ρc aφ.1 aφ.2
  continuous_toFun := by
    exact ((haarQuotientL2JointRightAction F G T i hi I e hc).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

@[simp]
theorem fullAEL2CuspidalJointRightAction_apply (a : AdelicGroupPoints F G) (φ : S) :
    fullAEL2CuspidalJointRightAction F G hPD hG T i hi I e hc (a, φ) = ρc a φ := rfl

/-- Forgetting the full cusp subtype recovers the original canonical joint action exactly. -/
theorem fullAEL2CuspidalJointRightAction_val (a : AdelicGroupPoints F G) (φ : S) :
    (fullAEL2CuspidalJointRightAction F G hPD hG T i hi I e hc (a, φ)).val =
      haarQuotientL2JointRightAction F G T i hi I e hc (a, φ.val) := rfl

/-- Each original full AE cusp vector has a continuous orbit in the inherited L2 topology. -/
def fullAEL2CuspidalOrbitMap (φ : S) : C(AdelicGroupPoints F G, S) :=
  (fullAEL2CuspidalJointRightAction F G hPD hG T i hi I e hc).comp
    ⟨fun a => (a, φ), continuous_id.prodMk continuous_const⟩

@[simp]
theorem fullAEL2CuspidalOrbitMap_apply (φ : S) (a : AdelicGroupPoints F G) :
    fullAEL2CuspidalOrbitMap F G hPD hG T i hi I e hc φ a = ρc a φ := rfl

end Langlands.Automorphic.GroupSchemeFunctions
