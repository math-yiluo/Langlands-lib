import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOpenCellOneSide
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeChamberContraction
import Langlands.GroupScheme.Rational.MinimalParabolicDistanceLengthProof
import Langlands.Representation.Aubert.General.RationalOppositeChamber
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry

/-! # The two-sided actual maximal-parabolic open-cell estimate -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Matrix Topology
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.HarishChandraSchwartz

section Iwasawa

/-- An Iwasawa factorization with a fixed subgroup holds for every conjugate
of the parabolic. Factoring the conjugating point gives a conjugation by an
element of the same compact subgroup. -/
theorem IsIwasawaPair.map_conj {X : Type*} [Group X] {P K : Subgroup X}
    (h : IsIwasawaPair P K) (w : X) :
    IsIwasawaPair (P.map (MulAut.conj w : X →* X)) K := by
  obtain ⟨p0, hp0, k0, hk0, hw⟩ := h w⁻¹
  have hw' : w = k0⁻¹ * p0⁻¹ := by
    simpa only [_root_.mul_inv_rev, inv_inv] using congrArg Inv.inv hw
  intro g
  obtain ⟨p, hp, k, hk, hg⟩ := h (k0 * g)
  refine ⟨k0⁻¹ * p * k0, ?_, k0⁻¹ * k, K.mul_mem (K.inv_mem hk0) hk, ?_⟩
  · refine ⟨p0 * p * p0⁻¹, P.mul_mem (P.mul_mem hp0 hp) (P.inv_mem hp0), ?_⟩
    change w * (p0 * p * p0⁻¹) * w⁻¹ = _
    rw [hw']
    group
  · calc
      g = k0⁻¹ * (k0 * g) := by group
      _ = k0⁻¹ * (p * k) := by rw [hg]
      _ = (k0⁻¹ * p * k0) * (k0⁻¹ * k) := by group

end Iwasawa

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Reversing the actual minimal parabolic preserves Iwasawa with the same
compact subgroup, by the proved rational chamber conjugacy. -/
theorem isIwasawaPair_minimal_neg (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (K : Subgroup (rationalPoints G))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K) :
    IsIwasawaPair (standardParabolicPoints i (-nu) ∅) K := by
  have := hi.isSplitSubtorus.mono
  have hneg := IsGenericCocharacter.neg i nu hnu
  obtain ⟨n, hn, _⟩ := MinimalParabolicDistanceLength.exists_map_conj_eq i hG hi hnu hneg
  have hp := congrArg SubgroupFunctor.rationalPoints
    (standardParabolicEndpoints F G hG T i hi nu hnu).1
  have hpneg := congrArg SubgroupFunctor.rationalPoints
    (standardParabolicEndpoints F G hG T i hi (-nu) hneg).1
  change standardParabolicPoints i nu ∅ =
    MinimalParabolicDistanceLength.parabolicPoints i nu at hp
  rw [show standardParabolicPoints i (-nu) ∅ =
    MinimalParabolicDistanceLength.parabolicPoints i (-nu) from hpneg,
    ← hn, ← hp]
  exact hPK.map_conj n


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The reversed maximal face is the literal negative image of the original
face, including for nonreduced relative root systems. -/
theorem simpleRoot_maximalFace_neg (i : T.toGrp ⟶ G) (nu : cocharacterLattice T)
    (hneg : ∀ alpha ∈ relativeRoots i, -alpha ∈ relativeRoots i) (alpha : characterLattice T) :
    Neg.neg '' (simpleRelativeRoots i nu \ {alpha}) =
      simpleRelativeRoots i (-nu) \ {-alpha} := by
  ext beta
  constructor
  · rintro ⟨b, ⟨hb, hba⟩, rfl⟩
    exact ⟨(neg_mem_simpleRelativeRoots_iff i nu hneg b).mpr hb, by simpa using hba⟩
  · rintro ⟨hb, hba⟩
    refine ⟨-beta, ⟨?_, ?_⟩, neg_neg beta⟩
    · simpa only [neg_neg] using
        (neg_mem_simpleRelativeRoots_iff i nu hneg (-beta)).mp (by simpa only [neg_neg] using hb)
    · simpa only [Set.mem_singleton_iff, neg_eq_iff_eq_neg] using hba

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- On an actual torus point, simultaneous root negation and point inversion
preserve its character order. -/
theorem rationalTorusCharacterOrder_neg_inv_map (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (alpha : characterLattice T) (a : rationalPoints T.toGrp) :
    rationalTorusCharacterOrder i (-alpha) (rationalPoints.map i a)⁻¹ =
      rationalTorusCharacterOrder i alpha (rationalPoints.map i a) := by
  rw [← map_inv, rationalTorusCharacterOrder_map, rationalTorusCharacterOrder_map]
  simp only [RenardLeviCones.characterOrder, AddEquiv.map_neg, AddMonoidHom.map_neg, map_inv, toAdd_inv,
    AddMonoidHom.neg_apply, neg_neg]

/-- The one-sided estimate for the opposite parabolic, with the same original
compact and original matrix height and the inverse conjugation orientation. -/
theorem exists_mem_open_mul_opposite_of_small_rationalHeight
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup)
    (Gamma : OpenSubgroup (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints)
    (hGamma : IsCompact (Gamma : Set
      (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints)) :
    ∃ C > 0, ∀ a ∈ rationalMinimalChamber i nu, ∀ g : rationalPoints G,
      1 + rationalHeight (F := F) rho g + rationalHeight (F := F) rho (a⁻¹ * g * a) ≤
        C * (rationalTorusCharacterOrder i alpha a : ℝ) →
      g ∈ (Gamma.toSubgroup.map
        (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints.subtype :
          Set (rationalPoints G)) *
        ((Dynamic.parabolic (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints :
          Set (rationalPoints G)) := by
  have := hi.isSplitSubtorus.mono
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hneg : ∀ beta ∈ relativeRoots i, -beta ∈ relativeRoots i := fun beta hbeta =>
    (relativeRootSystem F G hG T i hi).neg_mem_relativeRoots i hi.isSplitSubtorus.1 hbeta
  have hnuNeg := IsGenericCocharacter.neg i nu hnu
  have halphaNeg := (neg_mem_simpleRelativeRoots_iff i nu hneg alpha).mpr halpha
  have hzetaNeg := IsStandardCocharacter.neg i nu hneg hzeta
  rw [simpleRoot_maximalFace_neg i nu hneg alpha] at hzetaNeg
  have hchiNeg : CommGroupScheme.groupHom (-zeta) ≫ i =
      Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i) :=
    groupHom_neg_comp_eq_oppositeCocharacter i zeta
  have hstdNeg := (standardCocharacter F G hG T i hi (-nu) hnuNeg
    (simpleRelativeRoots i (-nu) \ {-alpha}) Set.sdiff_subset).2 (-zeta) hzetaNeg
  have hmemAll := fun (GammaNeg : OpenSubgroup
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom (-zeta) ≫ i))).rationalPoints)
    (hGammaNeg : IsCompact (GammaNeg : Set
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom (-zeta) ≫ i))).rationalPoints)) =>
      exists_mem_opposite_open_mul_of_small_rationalHeight hG i hi (-nu) hnuNeg
        (-alpha) halphaNeg (-zeta) hzetaNeg rho hrho K hK
        (isIwasawaPair_minimal_neg hG i hi nu hnu K.toSubgroup hPK) GammaNeg hGammaNeg
  have hUneg :
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom (-zeta) ≫ i))).rationalPoints =
      (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints := by
    rw [hchiNeg, Dynamic.oppositeCocharacter_oppositeCocharacter]
  rw [hUneg] at hmemAll
  obtain ⟨C, hC, hmem⟩ := hmemAll Gamma hGamma
  refine ⟨C, hC, fun a ha g hg => ?_⟩
  have horder : rationalTorusCharacterOrder i (-alpha) a⁻¹ = rationalTorusCharacterOrder i alpha a := by
    obtain ⟨a0, rfl, _⟩ := (mem_rationalMinimalChamber_iff_order i nu a).mp ha
    exact rationalTorusCharacterOrder_neg_inv_map i alpha a0
  have hout := hmem a⁻¹ (inv_mem_rationalMinimalChamber_neg hG hi ha) g (by
    simpa only [inv_inv, horder] using hg)
  have hpNeg : standardParabolicPoints i (-nu) (simpleRelativeRoots i (-nu) \ {-alpha}) =
      (Dynamic.parabolic (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints := by
    rw [standardParabolicPoints, hstdNeg.1, hchiNeg]
  simpa only [hpNeg] using hout


/-- The actual truncated parabolic cell `a^-1 Gamma a M GammaBar`, in the
unipotent-first coordinate order of II.3.5 and VIII.3.1. -/
def rationalParabolicSmallCell
    (chi : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (Gamma : Subgroup (Dynamic.unipotent chi).rationalPoints)
    (GammaBar : Subgroup (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints)
    (a : rationalPoints G) : Set (rationalPoints G) :=
  {g | ∃ u ∈ Gamma.map (Dynamic.unipotent chi).rationalPoints.subtype,
    ∃ m ∈ (Dynamic.centralizer chi).rationalPoints,
    ∃ v ∈ GammaBar.map (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints.subtype,
      g = (a⁻¹ * u * a) * m * v}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The actual opposite membership intersection is the truncated cell.
This is a pointwise group argument using the full dynamic intersection
`P(chi) ∩ P(-chi) = M(chi)`. -/
theorem mem_rationalParabolicSmallCell_of_opposite_memberships
    (chi : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (Gamma : Subgroup (Dynamic.unipotent chi).rationalPoints)
    (GammaBar : Subgroup (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints)
    (a g : rationalPoints G) (ha : a ∈ (Dynamic.centralizer chi).rationalPoints)
    (hplus : a * g * a⁻¹ ∈
      (Gamma.map (Dynamic.unipotent chi).rationalPoints.subtype : Set (rationalPoints G)) *
        ((Dynamic.parabolic (Dynamic.oppositeCocharacter chi)).rationalPoints : Set (rationalPoints G)))
    (hminus : g⁻¹ ∈
      (GammaBar.map (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints.subtype :
        Set (rationalPoints G)) * ((Dynamic.parabolic chi).rationalPoints : Set (rationalPoints G))) :
    g ∈ rationalParabolicSmallCell chi Gamma GammaBar a := by
  obtain ⟨u, hu, pb, hpb, hupb⟩ := hplus
  obtain ⟨v, hv, p, hp, hvp⟩ := hminus
  change u * pb = a * g * a⁻¹ at hupb
  change v * p = g⁻¹ at hvp
  let w := a⁻¹ * u * a
  let m := w⁻¹ * g * v
  have huU : u ∈ (Dynamic.unipotent chi).rationalPoints := by
    obtain ⟨u0, _, rfl⟩ := hu
    exact u0.2
  have hvV : v ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter chi)).rationalPoints := by
    obtain ⟨v0, _, rfl⟩ := hv
    exact v0.2
  have hwU : w ∈ (Dynamic.unipotent chi).rationalPoints := by
    have hn := Dynamic.centralizer_le_normalizer_unipotent chi _
      ((Dynamic.centralizer chi).rationalPoints.inv_mem ha)
    have hw := (Subgroup.mem_normalizer_iff.mp hn u).mp huU
    simpa only [inv_inv] using hw
  have hgplus : g = a⁻¹ * (u * pb) * a := by rw [hupb]; group
  have hgminus : g = p⁻¹ * v⁻¹ := by
    simpa only [_root_.mul_inv_rev, inv_inv] using (congrArg Inv.inv hvp).symm
  have hmP : m ∈ (Dynamic.parabolic chi).rationalPoints := by
    have he : m = w⁻¹ * p⁻¹ := by dsimp only [m]; rw [hgminus]; group
    rw [he]
    exact mul_mem (inv_mem (Dynamic.unipotent_le_parabolic chi _ hwU)) (inv_mem hp)
  have haPbar : a ∈ (Dynamic.parabolic (Dynamic.oppositeCocharacter chi)).rationalPoints := by
    apply Dynamic.centralizer_le_parabolic (Dynamic.oppositeCocharacter chi)
    rwa [Dynamic.centralizer_oppositeCocharacter]
  have hmPbar : m ∈ (Dynamic.parabolic (Dynamic.oppositeCocharacter chi)).rationalPoints := by
    have he : m = a⁻¹ * pb * a * v := by
      dsimp only [m, w]
      rw [hgplus]
      group
    rw [he]
    exact mul_mem (mul_mem (mul_mem (inv_mem haPbar) hpb) haPbar)
      (Dynamic.unipotent_le_parabolic (Dynamic.oppositeCocharacter chi) _ hvV)
  have hmM : m ∈ (Dynamic.centralizer chi).rationalPoints := by
    rw [← Dynamic.parabolic_inf_opposite_eq_centralizer chi]
    exact ⟨hmP, hmPbar⟩
  refine ⟨u, hu, m, hmM, v⁻¹, inv_mem hv, ?_⟩
  dsimp only [m, w]
  group

/-- Waldspurger II.3.5 on the full actual chamber, with the original
arbitrary closed matrix height and the original compact Iwasawa subgroup. -/
theorem exists_openCellBound_rationalParabolicSmallCell
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice T) (hnu : IsGenericCocharacter i nu)
    (alpha : characterLattice T) (halpha : alpha ∈ simpleRelativeRoots i nu)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i nu (simpleRelativeRoots i nu \ {alpha}) zeta)
    {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) K.toSubgroup)
    (Gamma : OpenSubgroup (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints)
    (hGamma : IsCompact (Gamma : Set
      (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints))
    (GammaBar : OpenSubgroup
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)
    (hGammaBar : IsCompact (GammaBar : Set
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)) :
    ∃ C > 0, OpenCellBound (rationalHeight (F := F) rho)
      (fun a => (rationalTorusCharacterOrder i alpha a : ℝ)) (rationalMinimalChamber i nu)
      (rationalParabolicSmallCell (CommGroupScheme.groupHom zeta ≫ i) Gamma.toSubgroup GammaBar.toSubgroup) C := by
  have := hi.isSplitSubtorus.mono
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨C6, hC6, hmem⟩ := exists_mem_opposite_open_mul_of_small_rationalHeight hG i hi nu hnu
    alpha halpha zeta hzeta rho hrho K hK hPK GammaBar hGammaBar
  obtain ⟨C8, hC8, hmemOpp⟩ := exists_mem_open_mul_opposite_of_small_rationalHeight hG i hi nu hnu
    alpha halpha zeta hzeta rho hrho K hK hPK Gamma hGamma
  have hstd := (standardCocharacter F G hG T i hi nu hnu
    (simpleRelativeRoots i nu \ {alpha}) Set.sdiff_subset).2 zeta hzeta
  have hp : standardParabolicPoints i nu (simpleRelativeRoots i nu \ {alpha}) =
      (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints :=
    congrArg SubgroupFunctor.rationalPoints hstd.1
  refine ⟨min C6 C8, lt_min hC6 hC8, fun a ha g hg => ?_⟩
  obtain ⟨a0, ha0, hadom⟩ := (mem_rationalMinimalChamber_iff_order i nu a).mp ha
  have ht : 0 ≤ (rationalTorusCharacterOrder i alpha a : ℝ) := by
    rw [← ha0, rationalTorusCharacterOrder_map]
    exact_mod_cast hadom alpha halpha
  have haM : a ∈ (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints := by
    rw [← hstd.2.1, ← ha0]
    exact (range_le_standardLevi i nu (simpleRelativeRoots i nu \ {alpha})) _ ⟨a0, rfl⟩
  apply mem_rationalParabolicSmallCell_of_opposite_memberships
    (CommGroupScheme.groupHom zeta ≫ i) Gamma.toSubgroup GammaBar.toSubgroup a g haM
  · apply hmemOpp a ha (a * g * a⁻¹)
    have hconj : a⁻¹ * (a * g * a⁻¹) * a = g := by group
    rw [hconj]
    have hle := hg.trans (mul_le_mul_of_nonneg_right (min_le_right C6 C8) ht)
    linarith
  · rw [← hp]
    apply hmem a ha g⁻¹
    have hconj : a * g⁻¹ * a⁻¹ = (a * g * a⁻¹)⁻¹ := by group
    rw [hconj, rationalHeight_inv, rationalHeight_inv]
    exact hg.trans (mul_le_mul_of_nonneg_right (min_le_left C6 C8) ht)


/-- The full actual-point form of Waldspurger II.3.5. -/
def RationalParabolicOpenCellHeightStatement : Prop :=
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
    (Gamma : OpenSubgroup (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints)
    (_hGamma : IsCompact (Gamma : Set
      (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).rationalPoints))
    (GammaBar : OpenSubgroup
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)
    (_hGammaBar : IsCompact (GammaBar : Set
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).rationalPoints)),
    ∃ C > 0, OpenCellBound (rationalHeight (F := F) rho)
      (fun a => (rationalTorusCharacterOrder i alpha a : ℝ)) (rationalMinimalChamber i nu)
      (rationalParabolicSmallCell (CommGroupScheme.groupHom zeta ≫ i) Gamma.toSubgroup GammaBar.toSubgroup) C

/-- The exact closed II.3.5 proposition at arbitrary field universe. -/
theorem rationalParabolicOpenCellHeight : RationalParabolicOpenCellHeightStatement.{u} := by
  intro F _ _ _ _ G _ _ hG T i hi nu hnu alpha halpha zeta hzeta N _ rho hrho K hK hPK
    Gamma hGamma GammaBar hGammaBar
  exact exists_openCellBound_rationalParabolicSmallCell hG i hi nu hnu alpha halpha zeta hzeta
    rho hrho K hK hPK Gamma hGamma GammaBar hGammaBar

end Langlands.HarishChandraSchwartz
