import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeTailCutoff
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConjugationSplit

/-! # Actual geometry for the intrinsic conjugation integral split -/

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

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The geometric cell of II.3.5 is exactly the actual truncated cell in
the intrinsic integral split, at the same ambient compact-open scale. -/
theorem rationalParabolicSmallCell_eq_rationalDynamicConjugationCell
    (chi : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (H : OpenSubgroup (rationalPoints G))
    (a : (Dynamic.centralizer chi).rationalPoints) :
    rationalParabolicSmallCell chi
      (H.comap (Dynamic.unipotent chi).rationalPoints.subtype continuous_subtype_val).toSubgroup
      (H.comap (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints.subtype
        continuous_subtype_val).toSubgroup a = rationalDynamicConjugationCell chi H a := by
  let M := (Dynamic.centralizer chi).rationalPoints
  let U := (Dynamic.unipotent chi).rationalPoints
  let V := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints
  have hMU : M ≤ Subgroup.normalizer (U : Set (rationalPoints G)) :=
    Dynamic.centralizer_le_normalizer_unipotent chi _
  ext g
  constructor
  · rintro ⟨u, hu, m, hm, v, hv, hg⟩
    obtain ⟨u0, hu0, rfl⟩ := hu
    obtain ⟨v0, hv0, rfl⟩ := hv
    change g = ((a : rationalPoints G)⁻¹ * (u0 : rationalPoints G) * a) * m *
      (v0 : rationalPoints G) at hg
    let m0 : M := ⟨m, hm⟩
    let ur : U := conjUnipotent hMU m0⁻¹ (conjUnipotent hMU a⁻¹ u0)
    let vr : V := v0⁻¹
    refine ⟨((m0, ur), vr), ⟨?_, ?_⟩, ?_⟩
    · change (a : rationalPoints G) *
        ((m0 : rationalPoints G) * (ur : rationalPoints G) * (m0 : rationalPoints G)⁻¹) *
          (a : rationalPoints G)⁻¹ ∈ H
      have he : (a : rationalPoints G) *
          ((m0 : rationalPoints G) * (ur : rationalPoints G) * (m0 : rationalPoints G)⁻¹) *
            (a : rationalPoints G)⁻¹ = u0 := by
        dsimp only [ur, conjUnipotent, Subgroup.coe_inv]
        group
      rw [he]
      exact hu0
    · exact H.inv_mem hv0
    · change (m0 : rationalPoints G) * ur * (vr : rationalPoints G)⁻¹ = g
      rw [hg]
      dsimp only [m0, ur, vr, conjUnipotent, Subgroup.coe_inv]
      group
  · rintro ⟨⟨⟨m, u⟩, v⟩, ⟨huH, hvH⟩, hg⟩
    let up : U := conjUnipotent hMU a (conjUnipotent hMU m u)
    refine ⟨up, ⟨up, huH, rfl⟩, m, m.2, (v : rationalPoints G)⁻¹,
      ⟨v⁻¹, H.inv_mem hvH, rfl⟩, ?_⟩
    rw [← hg]
    dsimp only [openCellCoord, up, conjUnipotent]
    group

/-- The complement height comparison on a maximal-root sector, with the
exact cell used by the actual intrinsic conjugation integral split. -/
theorem exists_rationalDynamicCell_complement_height_bound
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup)
    (H : OpenSubgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G))) :
    ∃ B > 0, ∀ a : (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints,
      (a : rationalPoints G) ∈ rationalMinimalRootSector i nu alpha → ∀ g : rationalPoints G,
      g ∉ rationalDynamicConjugationCell (CommGroupScheme.groupHom zeta ≫ i) H a →
      1 + rationalHeight (F := F) rho a ≤ B * (1 + rationalHeight (F := F) rho g +
        rationalHeight (F := F) rho ((a : rationalPoints G) * g * (a : rationalPoints G)⁻¹)) := by
  have := hi.isSplitSubtorus.mono
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let chi := CommGroupScheme.groupHom zeta ≫ i
  let U := (Dynamic.unipotent chi).rationalPoints
  let V := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints
  let Gamma : OpenSubgroup U := H.comap U.subtype continuous_subtype_val
  let GammaBar : OpenSubgroup V := H.comap V.subtype continuous_subtype_val
  have hU : IsClosed (U : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F (Dynamic.unipotent chi)
      (Dynamic.Affine.unipotentHom chi) (Dynamic.Affine.isRepresentedBy_unipotentHom chi)
      (Dynamic.Affine.isClosedSubgroup_unipotentHom chi)
  have hV : IsClosed (V : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F (Dynamic.unipotent (Dynamic.oppositeCocharacter chi))
      (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter chi))
      (Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter chi))
      (Dynamic.Affine.isClosedSubgroup_unipotentHom (Dynamic.oppositeCocharacter chi))
  have hGamma : IsCompact (Gamma : Set U) := hU.isClosedEmbedding_subtypeVal.isCompact_preimage hH
  have hGammaBar : IsCompact (GammaBar : Set V) := hV.isClosedEmbedding_subtypeVal.isCompact_preimage hH
  obtain ⟨C, hC, hcell⟩ := exists_openCellBound_rationalParabolicSmallCell hG i hi nu hnu alpha halpha
    zeta hzeta rho hrho K hK hPK Gamma hGamma GammaBar hGammaBar
  obtain ⟨D, hD, hheight⟩ := exists_one_add_rationalHeight_le_on_rootSectors hG hi hnu rho
  have hsector : rationalMinimalRootSector i nu alpha ⊆ rationalMinimalChamber i nu :=
    fun a ha => (rationalMinimalRootSector_subset alpha ha).1
  have hheight' : ∀ a ∈ rationalMinimalRootSector i nu alpha,
      1 + rationalHeight (F := F) rho a ≤ D * (1 + (rationalTorusCharacterOrder i alpha a : ℝ)) := by
    intro a ha
    obtain ⟨a0, ha0, hb⟩ := hheight alpha a ha
    simpa only [← ha0, rationalTorusCharacterOrder_map] using hb
  obtain ⟨B, hb⟩ := conjugationSigmaBound_of_openCellBound hC (rationalHeight_nonneg rho)
    hsector hcell hD.le hheight'
  refine ⟨max B 0 + 1, by positivity, fun a ha g hg => ?_⟩
  have hout : g ∉ rationalParabolicSmallCell chi Gamma.toSubgroup GammaBar.toSubgroup a := by
    rwa [rationalParabolicSmallCell_eq_rationalDynamicConjugationCell chi H a]
  have hb' := hb a ha g hout
  refine hb'.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · linarith [le_max_left B 0]
  · linarith [rationalHeight_nonneg rho g,
      rationalHeight_nonneg rho ((a : rationalPoints G) * g * (a : rationalPoints G)⁻¹)]


/-- The tail-height cutoff at the same ambient compact-open scale used by
the actual conjugation integral split. The hypothesis is literal
nonmembership in that compact after inverse conjugation. -/
theorem exists_rationalDynamicCell_opposite_tail_height_cutoff
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup)
    (H : OpenSubgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G))) :
    ∃ b > 0, ∀ a : (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints,
      (a : rationalPoints G) ∈ rationalMinimalRootSector i nu alpha →
      ∀ u : (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints,
      (a : rationalPoints G)⁻¹ * u * a ∉ H →
      b * (1 + rationalHeight (F := F) rho a) ≤ 1 + rationalHeight (F := F) rho u := by
  let chi := CommGroupScheme.groupHom zeta ≫ i
  let V := (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints
  let GammaBar : OpenSubgroup V := H.comap V.subtype continuous_subtype_val
  have hV : IsClosed (V : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F (Dynamic.unipotent (Dynamic.oppositeCocharacter chi))
      (Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter chi))
      (Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter chi))
      (Dynamic.Affine.isClosedSubgroup_unipotentHom (Dynamic.oppositeCocharacter chi))
  have hGammaBar : IsCompact (GammaBar : Set V) := hV.isClosedEmbedding_subtypeVal.isCompact_preimage hH
  obtain ⟨b, hb, hcut⟩ := exists_rationalOppositeTail_height_cutoff hG i hi nu hnu alpha halpha
    zeta hzeta rho hrho K hK hPK GammaBar hGammaBar
  refine ⟨b, hb, fun a ha u hu => hcut a ha u u.2 ?_⟩
  intro hmem
  obtain ⟨v, hv, heq⟩ := MinimalParabolicDistanceLength.mem_map_conj.mp hmem
  apply hu
  rw [← heq]
  exact hv

/-- The two geometric estimates on the exact cell and actual opposite
tail, at any ambient compact-open scale. -/
def RationalConjugationGeometricBoundsStatement : Prop :=
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
    (H : OpenSubgroup (rationalPoints G)) (_hH : IsCompact (H : Set (rationalPoints G))),
    (∃ B > 0, ∀ a : (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints,
      (a : rationalPoints G) ∈ rationalMinimalRootSector i nu alpha → ∀ g : rationalPoints G,
      g ∉ rationalDynamicConjugationCell (CommGroupScheme.groupHom zeta ≫ i) H a →
      1 + rationalHeight (F := F) rho a ≤ B * (1 + rationalHeight (F := F) rho g +
        rationalHeight (F := F) rho ((a : rationalPoints G) * g * (a : rationalPoints G)⁻¹))) ∧
    ∃ b > 0, ∀ a : (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints,
      (a : rationalPoints G) ∈ rationalMinimalRootSector i nu alpha →
      ∀ u : (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints,
      (a : rationalPoints G)⁻¹ * u * a ∉ H →
      b * (1 + rationalHeight (F := F) rho a) ≤ 1 + rationalHeight (F := F) rho u

/-- The exact closed geometric prerequisite to the actual VIII.3.1 split. -/
theorem rationalConjugationGeometricBounds : RationalConjugationGeometricBoundsStatement.{u} := by
  intro F _ _ _ _ G _ _ hG T i hi nu hnu alpha halpha zeta hzeta N _ rho hrho K hK hPK H hH
  exact ⟨exists_rationalDynamicCell_complement_height_bound hG i hi nu hnu alpha halpha zeta hzeta
    rho hrho K hK hPK H hH,
    exists_rationalDynamicCell_opposite_tail_height_cutoff hG i hi nu hnu alpha halpha zeta hzeta
      rho hrho K hK hPK H hH⟩

end Langlands.HarishChandraSchwartz
