import Langlands.Geometry.Building.TorusFiltration.Construction
import Langlands.Geometry.Building.TorusFiltration.StructuralStatements

/-! # The congruence shift and monotonicity of minimal congruent terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "Model" => IntegralModel O K T.toGrp
local notation "M₀" => connectedNeronModel F T hT

omit [IsAffine T.X.left] in
private theorem map_identity_le_of_le {M N : Model} (h : M.integralPoints ≤ N.integralPoints) :
    M.integralPoints.map (rationalPoints.map (𝟙 T.toGrp)) ≤ N.integralPoints := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using h hx

omit [IsAffine T.X.left] in
private theorem congruenceSubgroup_eq_of_integralPoints_eq {M N : Model}
    (hM : M.IsSmooth) (hN : N.IsSmooth) (h : M.integralPoints = N.integralPoints) :
    M.congruenceSubgroup = N.congruenceSubgroup := by
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F hM rfl
    (map_identity_le_of_le F T h.le)
  obtain ⟨ψ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F hN rfl
    (map_identity_le_of_le F T h.ge)
  rw [← M.congruenceSubgroupAt_one, ← N.congruenceSubgroupAt_one]
  apply le_antisymm
  · intro x hx
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      φ.map_mem_congruenceSubgroupAt 1 hx
  · intro x hx
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      ψ.map_mem_congruenceSubgroupAt 1 hx

private local instance : IsDiscreteValuationRing O := (fixedFieldIntegers_strictHenselian F).1

omit [IsAffine T.X.left] in
private theorem positiveCongruenceModel_isSmooth (M : Model) (hM : M.IsSmooth)
    {π : O} (hπ : Irreducible π) (n : ℕ+) : (M.positiveCongruenceModel hπ n).IsSmooth := by
  have h := IntegralModel.dilatationStructure.2 O K T.toGrp M π hπ hM n
  rw [M.congruenceModel_coe_pnat] at h
  exact h.1

/-- The minimal congruent terms decrease with the depth. -/
theorem minimalCongruentPoints_antitone : Antitone (minimalCongruentPoints F T hT) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M₁ := (M₀).positiveCongruenceModel hπ 1
  refine minimalCongruentPoints_antitone_of_firstCongruence F T hT M₁
    (positiveCongruenceModel_isSmooth F T M₀ (connectedNeronModel_isSmooth F T hT) hπ 1)
    (((M₀).integralPoints_positiveCongruenceModel hπ 1).trans (M₀).congruenceSubgroupAt_one) ?_
  intro n
  simpa only [add_comm] using (M₀).congruenceSubgroupAt_positiveCongruenceModel hπ 1 n

private theorem congruenceSubgroup_eq_nextDepth (r : ℝ≥0) (M : Model) (hM : M.IsSmooth)
    (hp : M.integralPoints = minimalCongruentPoints F T hT r) :
    M.congruenceSubgroup = minimalCongruentPoints F T hT (r + 1) := by
  obtain ⟨q, n, rfl⟩ := exists_depthParts r
  let B := minimalCongruentModel F T hT q
  have hB := B.property.2.2.trans (minimalCongruentPoints_of_lt_one F T hT q)
  have shift (n : ℕ+) (A : Model) (hA : A.IsSmooth)
      (ha : A.integralPoints = minimalCongruentShallowSubgroup F T hT q) :
      minimalCongruentPoints F T hT ((q : ℝ≥0) + (n : ℕ)) = A.congruenceSubgroupAt n :=
    minimalCongruentPoints_add_pnat F T hT q n A hA ha
  cases n with
  | zero =>
    simp only [Nat.cast_zero, add_zero] at hp ⊢
    rw [congruenceSubgroup_eq_of_integralPoints_eq F T hM B.property.1
      (hp.trans B.property.2.2.symm)]
    simpa only [PNat.val_ofNat, Nat.cast_one, IntegralModel.congruenceSubgroupAt_one] using
      (shift 1 B.val B.property.1 hB).symm
  | succ n =>
    let k := Nat.succPNat n
    change M.congruenceSubgroup = minimalCongruentPoints F T hT ((q : ℝ≥0) + ((k : ℕ) : ℝ≥0) + 1)
    change M.integralPoints = minimalCongruentPoints F T hT ((q : ℝ≥0) + (k : ℕ)) at hp
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    let P := B.val.positiveCongruenceModel hπ k
    have heq : M.integralPoints = P.integralPoints := hp.trans
      ((shift k B.val B.property.1 hB).trans (B.val.integralPoints_positiveCongruenceModel hπ k).symm)
    rw [congruenceSubgroup_eq_of_integralPoints_eq F T hM
      (positiveCongruenceModel_isSmooth F T B.val B.property.1 hπ k) heq,
      ← P.congruenceSubgroupAt_one]
    change (B.val.positiveCongruenceModel hπ k).congruenceSubgroupAt 1 = _
    rw [B.val.congruenceSubgroupAt_positiveCongruenceModel hπ k 1]
    simpa only [PNat.add_coe, PNat.val_ofNat, Nat.cast_add, Nat.cast_one, add_assoc] using
      (shift (k + 1) B.val B.property.1 hB).symm

/-- The first congruence subgroup at depth `r` is the term at depth `r + 1`. -/
theorem minimalCongruentCongruence : MinimalCongruentCongruenceStatement.{u} := by
  intro F _ _ _ _ T _ hT r M hM hp
  exact congruenceSubgroup_eq_nextDepth F T hT r M hM hp

end Langlands.Geometry.Building
