import Langlands.Geometry.Building.TorusFiltration.FunctorialityProof
import Langlands.Geometry.Building.TorusFiltration.InducedPowerTransfer
import Langlands.Geometry.Building.TorusFiltration.InducedStandardShift
import Langlands.Geometry.Building.TorusFiltration.PositivePowerSaturation
import Langlands.Geometry.Building.TorusFiltration.TameDegree
import Langlands.Geometry.Building.TorusFiltration.ZeroPlusProof
import Langlands.GroupScheme.Torus.InducedEmbedding
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction
import Mathlib.FieldTheory.Normal.Closure

/-! # Comparison with the standard torus filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open scoped CategoryTheory.MonObj NNReal ValuativeRel

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

section Filtration

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "K" => inertiaFixedField F
local notation "Ω" => SeparableClosure F
local notation "κ" => IsLocalRing.ResidueField (fixedFieldIntegers F)

set_option maxHeartbeats 1500000 in
private theorem inducedEmbedding
    (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]
    (hT : IsTorus T.toGrp) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of K)))
      (hS : IsInducedTorus S) (hA : IsAffine S.X.left) (i : T ⟶ S),
      ∀ r : ℝ≥0, 0 < r → localGeometricCharacterCongruence F T r =
        (@localTorusFiltration F _ _ _ _ S hA hS.isTorus r).comap
          (rationalPoints.map (CommGroupScheme.groupHom i)) := by
  obtain ⟨S, i, hS, hi⟩ := hT.exists_mono_inducedTorus T
  let : IsAffine S.X.left := SplittingAssembly.isAffine_of_isTorus S.toGrp hS.isTorus
  refine ⟨S, hS, inferInstance, i, ?_⟩
  intro r hr
  let base := inertiaFixedField F
  let sep := SeparableClosure F
  let ω := Langlands.LocalField.algebraicExtensionAddValuation F sep
  let j := CommGroupScheme.groupHom i
  let jSep := (GroupScheme.baseChange (baseMap base sep)).map j
  let : Mono j.hom.hom := hi
  let : Mono jSep.hom.hom.left := by
    change Mono (((Over.pullback (baseMap base sep)).map j.hom.hom).left)
    infer_instance
  let LT := localTorusSplittingData F T hT
  let LS := localTorusSplittingData F S hS.isTorus
  have ht := LT.splits.baseChange_fieldTower base LT.L sep T.toGrp
  have hs := LS.splits.baseChange_fieldTower base LS.L sep S.toGrp
  rw [localTorusFiltration_eq_geometric_of_induced F S hS hr]
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mp
      (map_extendedCharacterCongruence_le base sep ω T.toGrp j r)
  · intro x hx
    change rationalPoints.map j x ∈ extendedCharacterCongruence base sep ω S.toGrp r at hx
    change x ∈ extendedCharacterCongruence base sep ω T.toGrp r
    rw [mem_extendedCharacterCongruence, rationalExtend_map, mem_characterCongruence] at hx
    rw [mem_extendedCharacterCongruence, mem_characterCongruence]
    intro χ
    obtain ⟨ψ, rfl⟩ := ht.characterRestrict_surjective_of_mono hs jSep χ
    rw [rationalCharacterEval_characterRestrict]
    exact hx ψ

set_option maxHeartbeats 1100000 in
private theorem points_eq_standard_of_induced
    (S : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine S.X.left] (hS : IsInducedTorus S)
    (r : ℝ≥0) : minimalCongruentPoints F S hS.isTorus r = localTorusFiltration F S hS.isTorus r := by
  let hT := hS.isTorus
  let M₀ := connectedNeronModel F S hT
  obtain ⟨q, m, hparts⟩ := exists_depthParts r
  suffices heq : ∀ n : ℕ, minimalCongruentPoints F S hT ((q : ℝ≥0) + n) =
      localTorusFiltration F S hT ((q : ℝ≥0) + n) by
    simpa only [hparts] using heq m
  intro n
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, minimalCongruentPoints_of_lt_one]
    by_cases hq : (q : ℝ≥0) = 0
    · rw [minimalCongruentShallowSubgroup, ite_eq_left hq, hq]
      exact connectedNeronModel_integralPoints F S hT
    · have hq' : 0 < (q : ℝ≥0) := pos_of_ne_zero hq
      rw [minimalCongruentShallowSubgroup, ite_eq_right hq]
      apply le_antisymm
      · refine sup_le ?_ (inducedImages_le_standard_at_positiveDepth F S hT hq')
        have h := inducedStandardCongruence F S hS 0 M₀ (connectedNeronModel_isSmooth F S hT)
          (connectedNeronModel_integralPoints F S hT)
        rw [zero_add] at h
        exact h.le.trans (localTorusFiltration_antitone F S hT q.property.le)
      · rw [localTorusFiltration_eq_geometric_of_induced F S hS hq']
        apply le_sup_of_le_right
        have hi : (localGeometricCharacterCongruence F S q).map
            (rationalPoints.map (CommGroupScheme.groupHom (𝟙 S))) ≤
              inducedTorusStandardImages F S q :=
          le_iSup_of_le S (le_iSup_of_le hS (le_iSup_of_le (𝟙 S) le_rfl))
        intro x hx
        exact hi ⟨x, hx, by
          have hId : CommGroupScheme.groupHom (𝟙 S) = 𝟙 S.toGrp := rfl
          rw [hId, rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]⟩
  | succ n ih =>
    let d := (q : ℝ≥0) + (n : ℝ≥0)
    let M := minimalCongruentModel F S hT d
    have hmc := minimalCongruentCongruence F S hT d M.val M.property.1 M.property.2.2
    have hstd := inducedStandardCongruence F S hS d M.val M.property.1 (M.property.2.2.trans ih)
    simpa only [Nat.cast_succ, ← add_assoc, d] using hmc.symm.trans hstd

set_option maxHeartbeats 1700000 in
set_option synthInstance.maxHeartbeats 180000 in
private theorem standard_le_minimal_of_weaklyInduced
    (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]
    (hT : IsTorus T.toGrp) (hWeak : IsWeaklyInducedTorus F T)
    {r : ℝ≥0} (hr : 0 < r) :
    localTorusFiltration F T hT r ≤ minimalCongruentPoints F T hT r := by
  obtain ⟨L, hL, hTame, hInd⟩ := hWeak
  let : FiniteDimensional K L := hL
  let : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  let L' := IntermediateField.normalClosure K L Ω
  let S₀ := localTorusSplittingData F T hT
  let E : IntermediateField K Ω := L' ⊔ S₀.L
  let : FiniteDimensional K E := inferInstanceAs (FiniteDimensional K ↥(L' ⊔ S₀.L))
  let : IsGalois K E := ⟨⟩
  have hLE : L ≤ E := (IntermediateField.le_normalClosure L).trans le_sup_left
  have hS₀E : S₀.L ≤ E := le_sup_right
  let algL : Algebra L E := (IntermediateField.inclusion hLE).toAlgebra
  let : Algebra L E := algL
  let : SMul L E := algL.toSMul
  let algS₀ : Algebra S₀.L E := (IntermediateField.inclusion hS₀E).toAlgebra
  let : Algebra S₀.L E := algS₀
  let : SMul S₀.L E := algS₀.toSMul
  let : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq (R := K) (S := L) (A := E)
    fun _ => rfl
  let : IsScalarTower K S₀.L E := IsScalarTower.of_algebraMap_eq (R := K) (S := S₀.L) (A := E)
    fun _ => rfl
  have hSplit := S₀.splits.baseChange_fieldTower K S₀.L E T.toGrp
  obtain ⟨S, i, j, hS, hij⟩ :=
    InducedPowerTransfer.exists_degree_power_factorization K L E T hInd hSplit
  let : IsAffine S.X.left := SplittingAssembly.isAffine_of_isTorus S.toGrp hS.isTorus
  let : Algebra 𝓀[F] κ := (residueToFixedField F).toAlgebra
  have hm : (Module.finrank K L).Coprime (ringChar κ) := by
    rw [← Algebra.ringChar_eq 𝓀[F] κ, Nat.coprime_comm,
      (CharP.prime_ringChar 𝓀[F]).coprime_iff_not_dvd]
    exact not_dvd_finrank_of_tame F L hTame
  intro x hx
  have h₀ : x ∈ minimalCongruentPlus F T hT 0 := by
    rw [(minimalCongruentZeroPlus F T hT).1, Set.mem_inter_iff,
      connectedNeronModel_integralPoints]
    exact ⟨localTorusFiltration_antitone F T hT zero_le hx, Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hx⟩⟩
  apply minimalCongruentPoints_mem_of_coprime_pow F T hT h₀ r hm
  have hi : rationalPoints.map (CommGroupScheme.groupHom i) x ∈ localTorusFiltration F S hS.isTorus r :=
    map_localTorusFiltration_le F T hT hS.isTorus i r ⟨x, hx, rfl⟩
  rw [← points_eq_standard_of_induced F S hS] at hi
  have hj := minimalCongruentFunctoriality F S T hS.isTorus hT j r
    ⟨rationalPoints.map (CommGroupScheme.groupHom i) x, hi, rfl⟩
  change (x ≫ (CommGroupScheme.groupHom i).hom.hom) ≫
    (CommGroupScheme.groupHom j).hom.hom ∈ minimalCongruentPoints F T hT r at hj
  rw [← comp_groupHom_comp, hij, comp_groupHom_zsmul, zpow_natCast] at hj
  simpa only [show CommGroupScheme.groupHom (𝟙 T) = 𝟙 T.toGrp from rfl,
    Grp.id_hom_hom, Category.comp_id] using hj

end Filtration

set_option maxHeartbeats 1500000 in
theorem minimalCongruentWeaklyInduced : MinimalCongruentWeaklyInducedStatement.{u} := by
  intro F _ _ _ _ T _ hT hWeak r
  by_cases hr : r = 0
  · rw [hr, minimalCongruentPoints_zero, connectedNeronModel_integralPoints]
  have hpos : 0 < r := pos_of_ne_zero hr
  apply le_antisymm
  · let L := localTorusSplittingData F T hT
    obtain ⟨S, hS, hA, i, hi⟩ := inducedEmbedding F T hT
    let : IsAffine S.X.left := hA
    have hmap := minimalCongruentFunctoriality F T S hT hS.isTorus i r
    rw [points_eq_standard_of_induced F S hS] at hmap
    have hgeo := Subgroup.map_le_iff_le_comap.mp hmap
    rw [← hi r hpos] at hgeo
    rw [localTorusFiltration_eq_of_splitting F L.L T hT L.splits,
      localTorusFiltrationAtSplitting, ite_eq_right hr]
    refine le_inf ?_ hgeo
    have hle := minimalCongruentPoints_antitone F T hT (show 0 ≤ r from zero_le)
    rwa [minimalCongruentPoints_zero, connectedNeronModel_integralPoints,
      localTorusFiltration_zero F L.L T hT L.splits] at hle
  · exact standard_le_minimal_of_weaklyInduced F T hT hWeak hpos

end Langlands.Geometry.Building
