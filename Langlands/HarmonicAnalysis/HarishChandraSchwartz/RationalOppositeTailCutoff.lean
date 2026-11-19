import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOpenCellHeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalChamberHeight

/-! # The actual opposite-radical height cutoff in VIII.3.1 -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The opposite radical meets `GammaBar * P` exactly in `GammaBar`. -/
theorem mem_mapped_opposite_open_of_mem_mul
    (chi : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (GammaBar : Subgroup (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints)
    (x : rationalPoints G)
    (hx : x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints)
    (hmem : x ∈
      (GammaBar.map (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints.subtype :
        Set (rationalPoints G)) * ((Dynamic.parabolic chi).rationalPoints : Set (rationalPoints G))) :
    x ∈ GammaBar.map (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints.subtype := by
  obtain ⟨v, hv, p, hp, hvp⟩ := hmem
  change v * p = x at hvp
  have hvV : v ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints := by
    obtain ⟨v0, _, rfl⟩ := hv
    exact v0.2
  have hpV : p ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints := by
    have he : p = v⁻¹ * x := by rw [← hvp]; group
    rw [he]
    exact mul_mem (inv_mem hvV) hx
  have hp1 := Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic chi hpV hp
  rw [hp1, mul_one] at hvp
  exact hvp ▸ hv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Every standard opposite radical is contained in the opposite minimal
parabolic, which is the domain of the actual inverse-conjugation estimate. -/
theorem oppositeUnipotent_le_oppositeMinimalParabolic
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta) :
    (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints ≤
      standardParabolicPoints i (-nu) ∅ := by
  have := hi.isSplitSubtorus.mono
  have hneg : ∀ beta ∈ relativeRoots i, -beta ∈ relativeRoots i := fun beta hbeta =>
    (relativeRootSystem F G hG T i hi).neg_mem_relativeRoots i hi.isSplitSubtorus.1 hbeta
  have hnuNeg := IsGenericCocharacter.neg i nu hnu
  have hzetaNeg := IsStandardCocharacter.neg i nu hneg hzeta
  let Jneg := Neg.neg '' (simpleRelativeRoots i nu \ {alpha})
  have hstd := (standardCocharacter F G hG T i hi (-nu) hnuNeg Jneg hzetaNeg.1).2 (-zeta) hzetaNeg
  have hU : (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))) =
      standardUnipotent i (-nu) Jneg := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter i zeta]
    exact hstd.2.2.symm
  have hord := ((standardParabolicOrder F G hG T i hi (-nu) hnuNeg).1 ∅ Jneg
    (Set.empty_subset _) hzetaNeg.1).2 (Set.empty_subset _)
  rw [hU]
  exact (hord.2.trans (standardUnipotent_le_standardParabolic i (-nu) ∅)) _

/-- On a maximal-root sector, the complement of the conjugated compact open
in the actual opposite radical has height at least a fixed positive multiple
of the chamber height. This is the cutoff on printed p.325 of VIII.3.1. -/
theorem exists_rationalOppositeTail_height_cutoff
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup)
    (GammaBar : OpenSubgroup
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)
    (hGammaBar : IsCompact (GammaBar : Set
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)) :
    ∃ b > 0, ∀ a ∈ rationalMinimalRootSector i nu alpha,
      ∀ u ∈ (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints,
      u ∉ (GammaBar.toSubgroup.map
        (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints.subtype).map
          (MulAut.conj a : rationalPoints G →* rationalPoints G) →
      b * (1 + rationalHeight (F := F) rho a) ≤ 1 + rationalHeight (F := F) rho u := by
  have := hi.isSplitSubtorus.mono
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let chi := CommGroupScheme.groupHom zeta ≫ i
  let Ubar := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints
  let GammaSet : Subgroup (rationalPoints G) := GammaBar.toSubgroup.map Ubar.subtype
  obtain ⟨C6, hC6, hmem⟩ := exists_mem_opposite_open_mul_of_small_rationalHeight hG i hi nu hnu
    alpha halpha zeta hzeta rho hrho K hK hPK GammaBar hGammaBar
  obtain ⟨C8, hC8, hconj⟩ := exists_one_add_rationalHeight_inv_conj_le_on_opposite hG hi hnu rho
  obtain ⟨H, hH, hheight⟩ := exists_one_add_rationalHeight_le_on_rootSectors hG hi hnu rho
  let L := 1 + (C8 + 1) / C6
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨(H * L)⁻¹, inv_pos.mpr (mul_pos hH hL), fun a ha u hu hnot => ?_⟩
  have haCh : a ∈ rationalMinimalChamber i nu := (rationalMinimalRootSector_subset alpha ha).1
  obtain ⟨a0, ha0, hadom⟩ := (mem_rationalMinimalChamber_iff_order i nu a).mp haCh
  have hstd := (standardCocharacter F G hG T i hi nu hnu
    (simpleRelativeRoots i nu \ {alpha}) Set.sdiff_subset).2 zeta hzeta
  have haM : a ∈ (Dynamic.centralizer chi).rationalPoints := by
    rw [← hstd.2.1, ← ha0]
    exact (range_le_standardLevi i nu (simpleRelativeRoots i nu \ {alpha})) _ ⟨a0, rfl⟩
  have hxV : a⁻¹ * u * a ∈ Ubar := by
    have haMopp : a⁻¹ ∈ (Dynamic.centralizer (Dynamic.oppositeCocharacter chi)).rationalPoints := by
      rw [Dynamic.centralizer_oppositeCocharacter]
      exact inv_mem haM
    have hn := Dynamic.centralizer_le_normalizer_unipotent (Dynamic.oppositeCocharacter chi) _ haMopp
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hn u).mp hu
  have hxnot : a⁻¹ * u * a ∉ GammaSet := by
    intro hx
    exact hnot (MinimalParabolicDistanceLength.mem_map_conj.mpr hx)
  have hlarge : C6 * (rationalTorusCharacterOrder i alpha a : ℝ) <
      1 + rationalHeight (F := F) rho (a⁻¹ * u * a) + rationalHeight (F := F) rho u := by
    by_contra hle
    rw [not_lt] at hle
    have hcell := hmem a haCh (a⁻¹ * u * a) (by
      simpa only [show a * (a⁻¹ * u * a) * a⁻¹ = u by group] using hle)
    rw [show standardParabolicPoints i nu (simpleRelativeRoots i nu \ {alpha}) =
      (Dynamic.parabolic chi).rationalPoints from congrArg SubgroupFunctor.rationalPoints hstd.1] at hcell
    exact hxnot (mem_mapped_opposite_open_of_mem_mul chi GammaBar.toSubgroup _ hxV hcell)
  have huP : u ∈ standardParabolicPoints i (-nu) ∅ :=
    oppositeUnipotent_le_oppositeMinimalParabolic hG i hi nu hnu alpha zeta hzeta hu
  have hc := hconj a haCh u huP
  have hs := rationalHeight_nonneg rho u
  have horder : (rationalTorusCharacterOrder i alpha a : ℝ) ≤
      (C8 + 1) / C6 * (1 + rationalHeight (F := F) rho u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hC6]
    nlinarith
  obtain ⟨a1, ha1, hha⟩ := hheight alpha a ha
  have hha' : 1 + rationalHeight (F := F) rho a ≤
      H * (1 + (rationalTorusCharacterOrder i alpha a : ℝ)) := by
    simpa only [← ha1, rationalTorusCharacterOrder_map] using hha
  have hfinal : 1 + rationalHeight (F := F) rho a ≤
      H * L * (1 + rationalHeight (F := F) rho u) := by
    refine hha'.trans ?_
    dsimp only [L]
    have h1 : 1 + (rationalTorusCharacterOrder i alpha a : ℝ) ≤
        (1 + (C8 + 1) / C6) * (1 + rationalHeight (F := F) rho u) := by
      nlinarith
    exact (mul_le_mul_of_nonneg_left h1 hH.le).trans_eq (by ring)
  rw [inv_mul_le_iff₀ (mul_pos hH hL)]
  exact hfinal


/-- The closed geometric tail cutoff used in the VIII.3.1 integral estimate. -/
def RationalOppositeTailHeightCutoffStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (_hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i) (nu : cocharacterLattice T) (_hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (_halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (_hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    (N : ℕ) [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (_hrho : IsClosedSubgroup rho) (K : OpenSubgroup (rationalPoints G))
    (_hK : IsCompact (K : Set (rationalPoints G)))
    (_hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup)
    (GammaBar : OpenSubgroup
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)
    (_hGammaBar : IsCompact (GammaBar : Set
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)),
    ∃ b > 0, ∀ a ∈ rationalMinimalRootSector i nu alpha,
      ∀ u ∈ (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints,
      u ∉ (GammaBar.toSubgroup.map
        (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints.subtype).map
          (MulAut.conj a : rationalPoints G →* rationalPoints G) →
      b * (1 + rationalHeight (F := F) rho a) ≤ 1 + rationalHeight (F := F) rho u

/-- The exact closed cutoff statement at arbitrary field universe. -/
theorem rationalOppositeTailHeightCutoff : RationalOppositeTailHeightCutoffStatement.{u} := by
  intro F _ _ _ _ G _ _ hG T i hi nu hnu alpha halpha zeta hzeta N _ rho hrho K hK hPK
    GammaBar hGammaBar
  exact exists_rationalOppositeTail_height_cutoff hG i hi nu hnu alpha halpha zeta hzeta
    rho hrho K hK hPK GammaBar hGammaBar

end Langlands.HarishChandraSchwartz
