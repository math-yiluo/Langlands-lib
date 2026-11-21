import Langlands.Geometry.Building.KPLieCocharacterRootSupportStatement
import Langlands.GroupScheme.Lie.TorusCentralizer
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Proof of the apartment cocharacter root-support statement

Proves `LieRootSupportOfApartmentCocharacterStatement` by splitting the Lie algebra into the
weight spaces of the apartment torus that pair positively, respectively nonpositively, with
the cocharacter.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

open ParahoricBuildingData.LieFiltrationData

private theorem cocharacterPositiveLie_eq_iSup {F : Type u} [Field F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (ν : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    cocharacterPositiveLie ν =
      ⨆ n : ℕ, weightSpace ν (Gm.powerHom _ (n + 1)) := by
  rw [cocharacterPositiveLie, RelativeRoot.positiveWeightSpan]
  apply le_antisymm
  · refine iSup_le fun n => le_iSup_of_le (n.1 - 1) ?_
    have hn : n.1 - 1 + 1 = n.1 := Nat.sub_add_cancel n.2
    have he : ((n.1 - 1 : ℕ) : ℤ) + 1 = (n.1 : ℤ) := by exact_mod_cast hn
    simp [he]
  · refine iSup_le fun n => le_iSup_of_le ⟨n + 1, Nat.succ_pos _⟩ ?_
    have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by simp
    rw [Gm.powerHom_apply, hn]
    exact le_rfl

set_option maxHeartbeats 1200000 in
/-- Proof of `LieRootSupportOfApartmentCocharacterStatement`. -/
theorem lieRootSupportOfApartmentCocharacter :
    LieRootSupportOfApartmentCocharacterStatement.{u} := by
  classical
  intro F _ _ _ _ G _ P L x ν r X hX hν v a ha
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  let t := shiftedIndex r
  let pos : Set (characterLattice P.S) := {χ | 0 < latticePairing P.S χ ν}
  let neg : Set (characterLattice P.S) := {χ | latticePairing P.S χ ν ≤ 0}
  let Pos : Submodule F (Additive (lieKernel G F)) := ⨆ χ ∈ pos, weightSpace P.i χ
  let Neg : Submodule F (Additive (lieKernel G F)) := ⨆ χ ∈ neg, weightSpace P.i χ
  let E := GenericLie.equiv 𝒪[F] G
  let PosO := (Pos.comap E.toLinearMap).restrictScalars 𝒪[F]
  let NegO := (Neg.comap E.toLinearMap).restrictScalars 𝒪[F]
  have hpn : Disjoint Pos Neg :=
    (isInternal_weightSpace_of_isSplitTorus F G P.S hT P.i).submodule_iSupIndep.disjoint_biSup_biSup
      (Set.disjoint_left.2 fun χ hp hn =>
        (not_lt_of_ge (show latticePairing P.S χ ν ≤ 0 from hn))
          (show 0 < latticePairing P.S χ ν from hp))
  have hpnO : Disjoint PosO NegO := Submodule.disjoint_def.2 fun Y hYpos hYneg =>
    E.injective (by rw [map_zero]; exact Submodule.disjoint_def.1 hpn (E Y) hYpos hYneg)
  have hXpos : E X ∈ Pos := by
    rw [cocharacterPositiveLie_eq_iSup, iSup_nat_succ_weightSpace_cocharacter hT] at hν
    exact hν
  have hscaledPos : a • X ∈ PosO := by
    change E (a • X) ∈ Pos
    rw [GenericLie.smul_def, map_smul]
    exact Pos.smul_mem _ hXpos
  have hscale := (L.mem_lieFiltrationReal.1 hX) a ha
  let Q := ⨆ (ψ : P.affineRoots) (_ : (t : ℝ) ≤ ψ.1 x) (_ : 0 < ψ.1.linear v), L.affineRootLie ψ
  have hslope (ψ : P.affineRoots) (α : relativeRoots P.i) (hα : ψ.1.linear = rootForm P.i α) :
      ψ.1.linear v = (latticePairing P.S α ν : ℝ) := by
    rw [hα]
    change rootForm P.i α (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν)) = _
    simp
  have hpos (ψ : P.affineRoots) (hp : 0 < ψ.1.linear v) : L.affineRootLie ψ ≤ PosO := by
    obtain ⟨α, hα, -⟩ := ψ.2
    have hαpos : 0 < latticePairing P.S α ν := by
      rw [hslope ψ α hα] at hp
      exact_mod_cast hp
    refine (L.affineRootLie_le ψ α hα).trans ?_
    intro Z hZ
    change E Z ∈ Pos
    refine (show RelativeRoot.positiveWeightSpan P.i α ≤ Pos from ?_) hZ
    refine iSup_le fun n => le_iSup₂_of_le (n.1 • α.val) ?_ le_rfl
    change 0 < latticePairing P.S (n.1 • α.val) ν
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (by exact_mod_cast n.2) hαpos
  have hneg (ψ : P.affineRoots) (hn : ψ.1.linear v ≤ 0) : L.affineRootLie ψ ≤ NegO := by
    obtain ⟨α, hα, -⟩ := ψ.2
    have hαneg : latticePairing P.S α ν ≤ 0 := by
      rw [hslope ψ α hα] at hn
      exact_mod_cast hn
    refine (L.affineRootLie_le ψ α hα).trans ?_
    intro Z hZ
    change E Z ∈ Neg
    refine (show RelativeRoot.positiveWeightSpan P.i α ≤ Neg from ?_) hZ
    refine iSup_le fun n => le_iSup₂_of_le (n.1 • α.val) ?_ le_rfl
    change latticePairing P.S (n.1 • α.val) ν ≤ 0
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hαneg
  have hz : L.centralizerLieImage t ≤ NegO := by
    rintro _ ⟨Z, _, rfl⟩
    change E (GenericLie.map 𝒪[F] P.centralizer.j Z) ∈ Neg
    rw [GenericLie.map_apply, LinearEquiv.apply_symm_apply]
    apply (show weightSpace P.i 0 ≤ Neg from le_iSup₂_of_le 0 (by simp [neg]) le_rfl)
    apply Lie.mem_weightSpace_zero_of_mem_torusCentralizer
    rw [← P.centralizer.isRepresentedBy.2]
    exact SubgroupFunctor.mem_range.2 ⟨(GenericLie.equiv 𝒪[F] P.centralizer.Z Z).toMul.val, rfl⟩
  have hQpos : Q ≤ PosO := iSup₂_le fun ψ _ => iSup_le (hpos ψ)
  have hsub : L.lieFiltration x t ≤ Q ⊔ NegO := by
    rw [lieFiltration]
    apply sup_le (hz.trans le_sup_right)
    refine iSup₂_le fun ψ hψ => ?_
    by_cases hp : 0 < ψ.1.linear v
    · exact le_sup_of_le_left (le_iSup₂_of_le ψ hψ (le_iSup_of_le hp le_rfl))
    · exact (hneg ψ (le_of_not_gt hp)).trans le_sup_right
  obtain ⟨Y, hY, Z, hZ, hYZ⟩ := Submodule.mem_sup.1 (hsub hscale)
  have hZpos : Z ∈ PosO := by
    have hsum : Y + Z ∈ PosO := hYZ ▸ hscaledPos
    simpa only [add_sub_cancel_left] using PosO.sub_mem hsum (hQpos hY)
  have hZ0 := Submodule.disjoint_def.1 hpnO Z hZpos hZ
  rw [hZ0, add_zero] at hYZ
  exact hYZ ▸ hY

end Langlands.Geometry.Building
