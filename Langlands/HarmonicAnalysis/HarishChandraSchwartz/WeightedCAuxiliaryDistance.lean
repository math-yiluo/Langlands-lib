import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionAuxiliaryParabolics
import Langlands.Representation.Plancherel.DynamicCommonLeviGallery
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Root signs and distance for the auxiliary parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicCommonLeviComposition

namespace Langlands.HarishChandraSchwartz.WeakExpansion

variable {F : Type u} [Field F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

/-- A distance condition with opposite endpoint parabolics holds for every middle cocharacter. -/
theorem isDistanceAdditive_to_opposite (β middle : cocharacterLattice T) :
    IsDistanceAdditive (CommGroupScheme.groupHom β ≫ i)
      (CommGroupScheme.groupHom middle ≫ i) (CommGroupScheme.groupHom (-β) ≫ i) := by
  constructor
  · rw [groupHom_neg_comp_eq_oppositeCocharacter]
    change radical (CommGroupScheme.groupHom β ≫ i) ⊓
      oppositeRadical (CommGroupScheme.groupHom β ≫ i) ≤ _
    exact (radical_inf_oppositeRadical _).le.trans bot_le
  · change radical (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom β ≫ i)) ⊓
      radical (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom (-β) ≫ i)) ≤ _
    rw [← groupHom_neg_comp_eq_oppositeCocharacter, ← groupHom_neg_comp_eq_oppositeCocharacter,
      neg_neg, groupHom_neg_comp_eq_oppositeCocharacter, inf_comm]
    change radical (CommGroupScheme.groupHom β ≫ i) ⊓
      oppositeRadical (CommGroupScheme.groupHom β ≫ i) ≤ _
    exact (radical_inf_oppositeRadical _).le.trans bot_le

variable [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

include hG hi in
/-- A root pairing on a dominant auxiliary cocharacter has the sign of the outer
pairing when that is nonzero and agrees with the inner pairing when that is zero. -/
theorem auxiliaryCocharacter_pairing_pos_iff (α β : cocharacterLattice T)
    {c : characterLattice T} (hc : c ∈ relativeRoots i) :
    0 < latticePairing T c (auxiliaryCocharacter i α β) ↔
      0 < latticePairing T c α ∨ latticePairing T c α = 0 ∧ 0 < latticePairing T c β := by
  let : Smooth G.X.hom := hG.smooth
  have hp := (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth
    hi.isSplitSubtorus.1 i α (auxiliaryCocharacter i α β)).mp (auxiliaryCocharacter_spec i α β).2.2
  rcases lt_trichotomy (latticePairing T c α) 0 with h | h | h
  · have hm := hp (-c) (relativeRootNegation F G hG T i hi c hc) (by simpa using h)
    have hmneg : latticePairing T c (auxiliaryCocharacter i α β) < 0 := by simpa using hm
    simp [h.not_gt, h.ne, hmneg.not_gt]
  · have he : latticePairing T c (auxiliaryCocharacter i α β) = latticePairing T c β := by
      simp [auxiliaryCocharacter, h]
    simp [h, he]
  · simp [h, hp c hc h]

include hG hi in
/-- The corresponding negative sign criterion for an auxiliary cocharacter. -/
theorem auxiliaryCocharacter_pairing_neg_iff (α β : cocharacterLattice T)
    {c : characterLattice T} (hc : c ∈ relativeRoots i) :
    latticePairing T c (auxiliaryCocharacter i α β) < 0 ↔
      latticePairing T c α < 0 ∨ latticePairing T c α = 0 ∧ latticePairing T c β < 0 := by
  simpa using auxiliaryCocharacter_pairing_pos_iff i hG hi α β
    (relativeRootNegation F G hG T i hi c hc)

include hG hi in
/-- The signed auxiliary parabolics have the conjugated starting parabolic
between them in the distance condition for composition of standard integrals. -/
theorem isDistanceAdditive_auxiliary (α β : cocharacterLattice T) :
    IsDistanceAdditive
      (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i)
      (CommGroupScheme.groupHom β ≫ i)
      (CommGroupScheme.groupHom (auxiliaryCocharacter i (-α) β) ≫ i) := by
  constructor
  · apply RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots
      hG.smooth hG.connectedSpace hi.isSplitSubtorus.1 i
    rintro c ⟨hc, hn⟩ hp
    have h₀ := (auxiliaryCocharacter_pairing_pos_iff i hG hi α β hc).mp hp
    have h₁ := (auxiliaryCocharacter_pairing_pos_iff i hG hi (-α) β hc).mp hn
    simp only [map_neg, neg_pos, neg_eq_zero] at h₁
    omega
  · change radical (Dynamic.oppositeCocharacter _) ⊓ radical (Dynamic.oppositeCocharacter _) ≤
      radical (Dynamic.oppositeCocharacter _)
    simp only [← groupHom_neg_comp_eq_oppositeCocharacter]
    apply RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots
      hG.smooth hG.connectedSpace hi.isSplitSubtorus.1 i
    rintro c ⟨hc, hn⟩ hp
    simp only [map_neg, neg_pos] at hp hn ⊢
    have h₀ := (auxiliaryCocharacter_pairing_neg_iff i hG hi α β hc).mp hp
    have h₁ := (auxiliaryCocharacter_pairing_neg_iff i hG hi (-α) β hc).mp hn
    simp only [map_neg, neg_lt_zero, neg_eq_zero] at h₁
    omega

include hG hi in
/-- Negating both entries of a dominant auxiliary cocharacter gives the
opposite parabolic and exchanges the two radicals. -/
theorem auxiliaryCocharacter_neg_sameDynamicChamber (α β : cocharacterLattice T) :
    SameDynamicChamber (CommGroupScheme.groupHom (-auxiliaryCocharacter i α β) ≫ i)
      (CommGroupScheme.groupHom (auxiliaryCocharacter i (-α) (-β)) ≫ i) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let x := -auxiliaryCocharacter i α β
  let y := auxiliaryCocharacter i (-α) (-β)
  have hZ : Dynamic.centralizer (CommGroupScheme.groupHom x ≫ i) =
      Dynamic.centralizer (CommGroupScheme.groupHom y ≫ i) := by
    dsimp only [x, y]
    rw [Dynamic.centralizer_groupHom_neg, (auxiliaryCocharacter_spec i α β).1,
      (auxiliaryCocharacter_spec i (-α) (-β)).1,
      Dynamic.centralizer_groupHom_neg, Dynamic.centralizer_groupHom_neg]
  have hpos (c : characterLattice T) (hc : c ∈ relativeRoots i) :
      0 < latticePairing T c x ↔ 0 < latticePairing T c y := by
    rw [show x = -auxiliaryCocharacter i α β from rfl, map_neg, neg_pos,
      auxiliaryCocharacter_pairing_neg_iff i hG hi α β hc,
      show y = auxiliaryCocharacter i (-α) (-β) from rfl,
      auxiliaryCocharacter_pairing_pos_iff i hG hi (-α) (-β) hc]
    simp only [map_neg, neg_pos, neg_eq_zero]
  have hU : Dynamic.unipotent (CommGroupScheme.groupHom x ≫ i) =
      Dynamic.unipotent (CommGroupScheme.groupHom y ≫ i) := by
    apply le_antisymm
    · exact (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth
        hi.isSplitSubtorus.1 i x y).mpr fun c hc => (hpos c hc).mp
    · exact (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth
        hi.isSplitSubtorus.1 i y x).mpr fun c hc => (hpos c hc).mpr
  refine ⟨?_, hU, ?_⟩
  · apply le_antisymm
    · exact Dynamic.parabolic_le_of_unipotent_le_of_centralizer_le _ _
        (hU.le.trans (Dynamic.unipotent_le_parabolic _))
        (hZ.le.trans (Dynamic.centralizer_le_parabolic _))
    · exact Dynamic.parabolic_le_of_unipotent_le_of_centralizer_le _ _
        (hU.ge.trans (Dynamic.unipotent_le_parabolic _))
        (hZ.ge.trans (Dynamic.centralizer_le_parabolic _))
  · change Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom x ≫ i)) =
      Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom y ≫ i))
    rw [← groupHom_neg_comp_eq_oppositeCocharacter, ← groupHom_neg_comp_eq_oppositeCocharacter]
    have hneg (c : characterLattice T) (hc : c ∈ relativeRoots i) :
        0 < latticePairing T c (-x) ↔ 0 < latticePairing T c (-y) := by
      simpa only [map_neg, LinearMap.neg_apply] using
        hpos (-c) (relativeRootNegation F G hG T i hi c hc)
    apply le_antisymm
    · exact (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth
        hi.isSplitSubtorus.1 i (-x) (-y)).mpr fun c hc => (hneg c hc).mp
    · exact (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth
        hi.isSplitSubtorus.1 i (-y) (-x)).mpr fun c hc => (hneg c hc).mpr

/-- An auxiliary cocharacter realizes the extension of the supplied inner
parabolic through any closed representative of the outer Levi. -/
theorem auxiliary_realization_of_innerCocharacter
    {L : GroupScheme (Spec (CommRingCat.of F))} (j : L ⟶ G) (hjc : IsClosedSubgroup j)
    (α β : cocharacterLattice T) (χL : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i)).IsRepresentedBy j)
    (hL : χL ≫ j = CommGroupScheme.groupHom β ≫ i) :
    let o := CommGroupScheme.groupHom α ≫ i
    let ψ := CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i
    Dynamic.parabolic ψ = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic χL) ∧
      Dynamic.centralizer ψ = (Dynamic.centralizer χL).map j ∧
      Dynamic.unipotent ψ = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent χL) := by
  dsimp only
  let ψ := CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i
  let o := CommGroupScheme.groupHom α ≫ i
  obtain ⟨hM, hP, hU⟩ := auxiliaryCocharacter_spec i α β
  have hOrbit (Y : Over (Spec (CommRingCat.of F))) (l : Y ⟶ L.X) :
      Dynamic.orbit ψ (l ≫ j.hom.hom) = Dynamic.orbit (χL ≫ j) (l ≫ j.hom.hom) := by
    rw [hL]
    exact auxiliaryCocharacter_orbit i α β (hj.2 ▸ SubgroupFunctor.mem_range.mpr ⟨l, rfl⟩)
  exact Dynamic.realization_of_inclusions o j hj χL ψ hOrbit hjc hP hU
    (hM.le.trans (fun _ _ h => h.1))

include hG hi in
/-- The opposite of the positive auxiliary parabolic extends the opposite
inner parabolic through the negative outer parabolic. -/
theorem auxiliary_opposite_realization_of_innerCocharacter
    {L : GroupScheme (Spec (CommRingCat.of F))} (j : L ⟶ G) (hjc : IsClosedSubgroup j)
    (α β : cocharacterLattice T) (χL : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom (-α) ≫ i)).IsRepresentedBy j)
    (hL : χL ≫ j = CommGroupScheme.groupHom β ≫ i) :
    let o := CommGroupScheme.groupHom (-α) ≫ i
    let ψ := Dynamic.oppositeCocharacter (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i)
    let χopp := Dynamic.oppositeCocharacter χL
    Dynamic.parabolic ψ = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic χopp) ∧
      Dynamic.centralizer ψ = (Dynamic.centralizer χopp).map j ∧
      Dynamic.unipotent ψ = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent χopp) := by
  dsimp only
  have hs := auxiliaryCocharacter_neg_sameDynamicChamber i hG hi α β
  rw [groupHom_neg_comp_eq_oppositeCocharacter] at hs
  have hLopp : Dynamic.oppositeCocharacter χL ≫ j = CommGroupScheme.groupHom (-β) ≫ i := by
    simp only [groupHom_neg_comp_eq_oppositeCocharacter, Dynamic.oppositeCocharacter,
      Category.assoc, hL]
  obtain ⟨hP, hM, hU⟩ := auxiliary_realization_of_innerCocharacter i j hjc (-α) (-β)
    (Dynamic.oppositeCocharacter χL) hj hLopp
  have hC : Dynamic.centralizer (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom (auxiliaryCocharacter i α β) ≫ i)) =
        Dynamic.centralizer (CommGroupScheme.groupHom (auxiliaryCocharacter i (-α) (-β)) ≫ i) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter, Dynamic.centralizer_groupHom_neg,
      (auxiliaryCocharacter_spec i α β).1, (auxiliaryCocharacter_spec i (-α) (-β)).1]
    simp only [Dynamic.centralizer_groupHom_neg]
  exact ⟨hs.1.trans hP, hC.trans hM, hs.2.1.trans hU⟩

end Langlands.HarishChandraSchwartz.WeakExpansion
