import Langlands.Representation.Aubert.General.RationalLatticeStrictExponentStatement
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation

/-! # Applying the literal valuation chamber condition to uniformizer rays -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Nonnegative simple-root pairings, with at least one positive pairing,
give exactly the valuation chamber in the general rational criterion. -/
theorem isNoncentralNegativeTorusPoint_uniformizerSection
    (x : cocharacterLattice T)
    (hnonneg : ∀ β, 0 ≤ simpleRootPairing i ν β x)
    (hpos : ∃ β, 0 < simpleRootPairing i ν β x) :
    IsNoncentralNegativeTorusPoint i ν
      (Plancherel.RenardCartan.uniformizerSection T (.ofAdd x)) := by
  have hπ : ValuativeRel.valuation k (LocalField.uniformizer k) < 1 := by
    rw [← (ValuativeRel.valuation k).vlt_one_iff, ← FML.ord_lt_ord_iff k 1]
    simp
  have hπ0 : 0 < ValuativeRel.valuation k (LocalField.uniformizer k) :=
    (ValuativeRel.valuation k).pos_iff.mpr (LocalField.uniformizer_ne_zero k)
  have heval (β : SimpleRoot i ν) :
      ValuativeRel.valuation k
        (simpleRootPointValue i ν β
          (Plancherel.RenardCartan.uniformizerSection T (.ofAdd x)) : k) =
      ValuativeRel.valuation k (LocalField.uniformizer k) ^ simpleRootPairing i ν β x := by
    rw [simpleRootPointValue, Plancherel.RenardCartan.uniformizerSection_apply,
      CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
      Units.val_zpow_eq_zpow_val, map_zpow₀, SplitTorusValuation.uniformizerUnit_val]
    rfl
  refine ⟨fun β => ?_, ?_⟩
  · rw [heval β]
    exact zpow_le_one₀ hπ0 hπ.le (hnonneg β)
  · obtain ⟨β, hβ⟩ := hpos
    refine ⟨β, ?_⟩
    rw [heval β]
    exact zpow_lt_one₀ hπ0 hπ hβ

/-- The strict normalized exponent hypothesis applies at the actual central
Levi point defined by a noncentral nonnegative uniformizer direction. -/
theorem rationalLatticeStrictExponent :
    RationalLatticeStrictExponentStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ ν hν hStandard hU A hstrict J x hzero hnonneg hpos
  have := hG.smooth
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  have hexists := (hStandard k G hG T i hi ν hν
    (rootSet i ν J) (rootSet_subset i ν J)).1
  let m : levi i ν J := ⟨uniformizerPowers i (.ofAdd x), uniformizerPowers_mem_levi i ν J x⟩
  have hm : m ∈ Subgroup.center (levi i ν J) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact commute_uniformizerPowers i ν hfinite J hexists x hzero y y.2
  let z : Subgroup.center (levi i ν J) := ⟨m, hm⟩
  refine ⟨z, rfl, fun χ hχ => ?_⟩
  exact hstrict J χ hχ
    (Plancherel.RenardCartan.uniformizerSection T (.ofAdd x)) z rfl
    (isNoncentralNegativeTorusPoint_uniformizerSection i ν x hnonneg hpos)

end Langlands.Aubert.General.RationalPointFamily
