import Langlands.Automorphic.GroupSchemeQuotientL2
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # Joint continuity of the actual canonical quotient L2 right action -/

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
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "Q" => PositiveRationalQuotient F G T i
local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "hR" => haarQuotientMeasureRightInvariant F G T i hi I e hc
local notation "ρ" => quotientL2RightAction F G T i μQ hR

/-- The original positive quotient L2 action, continuous jointly in the adelic
element and the actual null class for the unchanged canonical measure. -/
def haarQuotientL2JointRightAction :
    C(AdelicGroupPoints F G × Lp ℂ 2 μQ, Lp ℂ 2 μQ) where
  toFun aφ := ρ aφ.1 aφ.2
  continuous_toFun := by
    let := positiveRationalQuotient_t2Space F G T i hi I e hc
    let := positiveRationalQuotient_borelSpace F G T i hi I e hc
    let := positiveRationalQuotientHaarMeasure_regular F G T i hi I e hc
    let r : C(AdelicGroupPoints F G × Q, Q) :=
      ⟨fun aq => LeftCosetSpace.rightTranslate (positiveRationalSubgroup F G T i) aq.1 aq.2,
        continuous_smul.comp
          ((MulOpposite.continuous_op.comp continuous_fst).prodMk continuous_snd)⟩
    exact continuous_snd.compMeasurePreservingLp
      (r.curry.continuous.comp continuous_fst) (fun aφ => hR aφ.1) (by simp)

@[simp]
theorem haarQuotientL2JointRightAction_apply (a : AdelicGroupPoints F G) (φ : Lp ℂ 2 μQ) :
    haarQuotientL2JointRightAction F G T i hi I e hc (a, φ) = ρ a φ := rfl

/-- The continuous orbit map of each actual L2 vector under the same right action. -/
def haarQuotientL2OrbitMap (φ : Lp ℂ 2 μQ) : C(AdelicGroupPoints F G, Lp ℂ 2 μQ) :=
  (haarQuotientL2JointRightAction F G T i hi I e hc).comp
    ⟨fun a => (a, φ), continuous_id.prodMk continuous_const⟩

@[simp]
theorem haarQuotientL2OrbitMap_apply (φ : Lp ℂ 2 μQ) (a : AdelicGroupPoints F G) :
    haarQuotientL2OrbitMap F G T i hi I e hc φ a = ρ a φ := rfl

end Langlands.Automorphic.GroupSchemeFunctions
