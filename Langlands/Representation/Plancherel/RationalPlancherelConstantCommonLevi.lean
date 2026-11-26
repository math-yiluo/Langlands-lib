import Langlands.Representation.Plancherel.RationalSourceGammaCommonLevi
import Langlands.Representation.Plancherel.DynamicOppositeStandardIntertwining
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # The rank-one factors of `c(G|M)` on the parabolics of one semistandard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz
open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

local instance plancherelCommonLeviAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance plancherelCommonLeviPointTopology {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] : TopologicalSpace (RationalPoint F H.X) :=
  rationalPointTopology F H.X
local instance plancherelCommonLeviPointMeasurable {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] : MeasurableSpace (RationalPoint F H.X) :=
  borel (RationalPoint F H.X)
local instance plancherelCommonLeviPointBorel {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] : BorelSpace (RationalPoint F H.X) := ⟨rfl⟩
local instance plancherelCommonLeviFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance plancherelCommonLeviPointTopologicalGroup
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] :
    IsTopologicalGroup (RationalPoint F H.X) := rationalPoint_isTopologicalGroup F H
local instance plancherelCommonLeviPointT2 {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] : T2Space (RationalPoint F H.X) := rationalPoint_t2Space F H
local instance plancherelCommonLeviPointLocallyCompact
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] : LocallyCompactSpace (RationalPoint F H.X) :=
  rationalPoint_locallyCompactSpace F H
local instance plancherelCommonLeviFieldSecondCountable : SecondCountableTopology F :=
  localField_secondCountableTopology F
local instance plancherelCommonLeviPointSecondCountable
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] : SecondCountableTopology (RationalPoint F H.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F H
local instance plancherelCommonLeviSubgroupSecondCountable
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] (L : Subgroup (RationalPoint F H.X)) :
    SecondCountableTopology L :=
  TopologicalSpace.Subtype.secondCountableTopology (L : Set (RationalPoint F H.X))

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem oppositeCocharacter_groupHom_comp (ν : cocharacterLattice S) :
    oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i) =
      CommGroupScheme.groupHom (-ν) ≫ i :=
  (groupHom_neg_comp_eq_oppositeCocharacter i ν).symm

variable (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- Adding a cocharacter of `N` does not change the rank-one constant at `N`: points of the
submodule centralizer centralize it, so the parabolic and opposite radical intersections
with that centralizer are unchanged. -/
theorem rankOneGamma_add_of_mem (ζ ν : cocharacterLattice S)
    (N : Submodule ℤ (cocharacterLattice S)) (hν : ν ∈ N) :
    rankOneGamma i (ζ + ν) K hK N = rankOneGamma i ζ K hK N := by
  have hN := isClosed_cocharacterSubmoduleCentralizer i N
  unfold rankOneGamma leviGamma
  refine compactNormalizedSourceGamma_eq_of_transport (ContinuousMulEquiv.refl _) K K hK hK
    (isClosed_parabolic_inf _ _ hN) (isClosed_oppositeRadical_inf _ _ hN)
    (isClosed_parabolic_inf _ _ hN) (isClosed_oppositeRadical_inf _ _ hN)
    (fun x => ?_) (fun x => ?_) (fun _ => Iff.rfl)
  · change x ∈ (Dynamic.parabolic (CommGroupScheme.groupHom (ζ + ν) ≫ i)).carrier X₀ ⊓
        (cocharacterSubmoduleCentralizer i N).carrier X₀ ↔
      x ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).carrier X₀ ⊓
        (cocharacterSubmoduleCentralizer i N).carrier X₀
    simp only [Subgroup.mem_inf]
    refine ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨?_, h.2⟩⟩
    · exact (Dynamic.mem_parabolic_add_iff_of_mem_centralizer i ζ ν x
        ((mem_cocharacterSubmoduleCentralizer i N).1 h.2 ν hν)).mp h.1
    · exact (Dynamic.mem_parabolic_add_iff_of_mem_centralizer i ζ ν x
        ((mem_cocharacterSubmoduleCentralizer i N).1 h.2 ν hν)).mpr h.1
  · change x ∈ unipotentPoints (oppositeCocharacter (CommGroupScheme.groupHom (ζ + ν) ≫ i)) ⊓
        (cocharacterSubmoduleCentralizer i N).carrier X₀ ↔
      x ∈ unipotentPoints (oppositeCocharacter (CommGroupScheme.groupHom ζ ≫ i)) ⊓
        (cocharacterSubmoduleCentralizer i N).carrier X₀
    rw [oppositeCocharacter_groupHom_comp, oppositeCocharacter_groupHom_comp, neg_add]
    simp only [Subgroup.mem_inf]
    refine ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨?_, h.2⟩⟩
    · exact (Dynamic.mem_unipotent_add_iff_of_mem_centralizer i (-ζ) (-ν) x
        ((mem_cocharacterSubmoduleCentralizer i N).1 h.2 (-ν) (N.neg_mem hν))).mp h.1
    · exact (Dynamic.mem_unipotent_add_iff_of_mem_centralizer i (-ζ) (-ν) x
        ((mem_cocharacterSubmoduleCentralizer i N).1 h.2 (-ν) (N.neg_mem hν))).mpr h.1


/-- **Opposite symmetry of a rank-one constant.** Replacing `ζ` by `-ζ` does not change the
rank-one constant at `N`, if the common compact is limit-stable for the dynamic parabolic of
every cocharacter of the maximal split torus. The submodule centralizer is the centralizer
scheme of one generic cocharacter of `N`; there the constant is the source gamma of the
actual factored cocharacter, and the published opposite symmetry of source gamma applies. -/
theorem rankOneGamma_neg (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hKs : ∀ (ξ : cocharacterLattice S)
      (p : (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).carrier X₀),
      (p : RationalPoint F G.X) ∈ K →
        (Dynamic.limitHom (CommGroupScheme.groupHom ξ ≫ i) X₀ p : RationalPoint F G.X) ∈ K)
    (ζ : cocharacterLattice S) (N : Submodule ℤ (cocharacterLattice S)) :
    rankOneGamma i (-ζ) K hK N = rankOneGamma i ζ K hK N := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  obtain ⟨ν, -, hνN⟩ := exists_dynamicCentralizer_eq_cocharacterSubmoduleCentralizer hT i N
  let ψ := CommGroupScheme.groupHom ν ≫ i
  have hjψ := Dynamic.Affine.isRepresentedBy_centralizerHom ψ
  have hjc := Dynamic.Affine.isClosedSubgroup_centralizerHom ψ
  have hj : (cocharacterSubmoduleCentralizer i N).IsRepresentedBy
      (Dynamic.Affine.centralizerHom ψ) := by
    rw [← hνN]
    exact hjψ
  have : IsClosedImmersion (Dynamic.Affine.centralizerHom ψ).hom.hom.left := hjc
  have : IsAffine (Dynamic.Affine.centralizerScheme ψ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.centralizerHom ψ).hom.hom.left
  have : Smooth (Dynamic.Affine.centralizerScheme ψ).X.hom :=
    Dynamic.smooth_affineCentralizer_overRing ψ inferInstance
  have : LocallyOfFiniteType (Dynamic.Affine.centralizerScheme ψ).X.hom := inferInstance
  have hGH : IsConnectedReductive (Dynamic.Affine.centralizerScheme ψ) :=
    DynamicOppositeStandardIntertwining.parameterScheme_isConnectedReductive ψ hG
  set j := Dynamic.Affine.centralizerHom ψ
  set χH := Dynamic.intersectionCocharacter i (CommGroupScheme.groupHom ν)
    (CommGroupScheme.groupHom ζ) hjψ
  have hχH : χH ≫ j = CommGroupScheme.groupHom ζ ≫ i :=
    Dynamic.intersectionCocharacter_comp i _ _ hjψ
  have hχH' : oppositeCocharacter χH ≫ j = CommGroupScheme.groupHom (-ζ) ≫ i := by
    rw [← oppositeCocharacter_groupHom_comp, ← hχH, oppositeCocharacter, oppositeCocharacter,
      Category.assoc]
  have hsplitH : ∀ (t : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ Dynamic.Affine.centralizerScheme ψ)
      (ξ : cocharacterLattice S), t ≫ j = CommGroupScheme.groupHom ξ ≫ i →
      ∀ p : (Dynamic.parabolic t).carrier X₀,
        (p : RationalPoint F (Dynamic.Affine.centralizerScheme ψ).X) ∈
            closedSubgroupCompact hj hjc K →
          (Dynamic.limitHom t X₀ p : RationalPoint F (Dynamic.Affine.centralizerScheme ψ).X) ∈
            closedSubgroupCompact hj hjc K := by
    intro t ξ hη
    apply (compact_split_iff_limit_stable t (closedSubgroupCompact hj hjc K)).mp
    intro m u
    have hG' := (compact_split_iff_limit_stable (CommGroupScheme.groupHom ξ ≫ i) K).mpr (hKs ξ)
    have hm : (m : RationalPoint F (Dynamic.Affine.centralizerScheme ψ).X) ≫ j.hom.hom ∈
        (Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i)).carrier X₀ := by
      rw [← hη]
      exact Dynamic.centralizer_le_comap t j X₀ m.2
    have hu : (u : RationalPoint F (Dynamic.Affine.centralizerScheme ψ).X) ≫ j.hom.hom ∈
        unipotentPoints (CommGroupScheme.groupHom ξ ≫ i) := by
      rw [← hη]
      exact Dynamic.unipotent_le_comap t j X₀ u.2
    have h3 := hG' ⟨_, hm⟩ ⟨_, hu⟩
    rw [OpenSubgroup.mem_comap, OpenSubgroup.mem_comap, OpenSubgroup.mem_comap, map_mul,
      closedSubgroupPointHom_apply, closedSubgroupPointHom_apply]
    exact h3
  unfold rankOneGamma
  rw [leviGamma_eq_gamma_of_isClosedSubgroup hj hjc _ χH hχH K hK,
    leviGamma_eq_gamma_of_isClosedSubgroup hj hjc _ (oppositeCocharacter χH) hχH' K hK]
  exact gamma_oppositeCocharacter χH (closedSubgroupCompact hj hjc K)
    (isCompact_closedSubgroupCompact hj hjc K hK) hGH (hsplitH χH ζ hχH)
    (hsplitH _ (-ζ) hχH')


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The index sets of the rank-one products agree for two cocharacters whose pairings vanish
at the same relative roots: a root positive for one cocharacter is, up to sign, positive for
the other, and a root and its negative give the same annihilator. -/
theorem rankOneCocharacterSet_subset (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ζ ζ' : cocharacterLattice S}
    (hz : ∀ α ∈ relativeRoots i, latticePairing S α ζ = 0 ↔ latticePairing S α ζ' = 0) :
    rankOneCocharacterSet i ζ ⊆ rankOneCocharacterSet i ζ' := by
  have hlevi : leviRelativeRoots i ζ = leviRelativeRoots i ζ' := by
    ext α
    exact ⟨fun h => ⟨h.1, (hz α h.1).mp h.2⟩, fun h => ⟨h.1, (hz α h.1).mpr h.2⟩⟩
  rintro _ ⟨β, ⟨hβ, hβpos⟩, rfl⟩
  rcases lt_trichotomy (latticePairing S β ζ') 0 with h | h | h
  · refine ⟨-β, ⟨relativeRootNegation F G hG S i hi β hβ, by rw [map_neg, LinearMap.neg_apply]; omega⟩, ?_⟩
    unfold rankOneCocharacters
    rw [← hlevi]
    ext ν
    simp only [mem_cocharacterAnnihilator, Set.mem_insert_iff, forall_eq_or_imp, map_neg,
      LinearMap.neg_apply, neg_eq_zero]
  · exact absurd ((hz β hβ).mpr h) hβpos.ne'
  · refine ⟨β, ⟨hβ, h⟩, ?_⟩
    unfold rankOneCocharacters
    rw [hlevi]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem rankOneCocharacterSet_eq_of_pairing_zero_iff (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {ζ ζ' : cocharacterLattice S}
    (hz : ∀ α ∈ relativeRoots i, latticePairing S α ζ = 0 ↔ latticePairing S α ζ' = 0) :
    rankOneCocharacterSet i ζ = rankOneCocharacterSet i ζ' :=
  (rankOneCocharacterSet_subset hG hi hz).antisymm
    (rankOneCocharacterSet_subset hG hi fun α hα => (hz α hα).symm)

/-- **The rank-one constants agree.** For two cocharacters whose pairings vanish at the same
relative roots, and a root `β` positive for the first, the rank-one constants of the two
cocharacters at `X_*(A_β)` agree. With `a = ⟨β, ζ⟩` and `b = ⟨β, ζ'⟩`, the cocharacter
`a ζ' - b ζ` lies in `X_*(A_β)`; positive multiples, this shift and, when `b < 0`, the
opposite symmetry identify the constants. -/
theorem rankOneGamma_eq_of_pairing_zero_iff (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i)
    (hKs : ∀ (ξ : cocharacterLattice S)
      (p : (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).carrier X₀),
      (p : RationalPoint F G.X) ∈ K →
        (Dynamic.limitHom (CommGroupScheme.groupHom ξ ≫ i) X₀ p : RationalPoint F G.X) ∈ K)
    {ζ ζ' : cocharacterLattice S}
    (hz : ∀ α ∈ relativeRoots i, latticePairing S α ζ = 0 ↔ latticePairing S α ζ' = 0)
    {β : characterLattice S} (hβ : β ∈ positiveRelativeRoots i ζ) :
    rankOneGamma i ζ' K hK (rankOneCocharacters i ζ β) =
      rankOneGamma i ζ K hK (rankOneCocharacters i ζ β) := by
  obtain ⟨hβR, ha⟩ := hβ
  set a := latticePairing S β ζ
  set b := latticePairing S β ζ'
  have hb : b ≠ 0 := fun h => ha.ne' ((hz β hβR).mpr h)
  have hν : a • ζ' + (-b) • ζ ∈ rankOneCocharacters i ζ β := by
    unfold rankOneCocharacters
    rw [mem_cocharacterAnnihilator]
    intro χ hχ
    rcases hχ with rfl | ⟨hχR, hχ0⟩
    · simp only [map_add, map_zsmul, smul_eq_mul, a, b]
      ring
    · simp only [map_add, map_zsmul, smul_eq_mul, hχ0, (hz χ hχR).mp hχ0, mul_zero, add_zero]
  have hsplit : a • ζ' = b • ζ + (a • ζ' + (-b) • ζ) := by
    rw [neg_smul]
    abel
  rw [← rankOneGamma_zsmul i ζ' K hK ha, hsplit, rankOneGamma_add_of_mem K hK _ _ _ hν]
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have e : b • ζ = (-b) • (-ζ) := by rw [neg_smul, smul_neg, neg_neg]
    rw [e, rankOneGamma_zsmul i (-ζ) K hK (by omega), rankOneGamma_neg K hK hG hi hKs]
  · exact rankOneGamma_zsmul i ζ K hK hpos _

/-- **The rank-one products agree** for two cocharacters whose pairings vanish at the same
relative roots, if the common compact is limit-stable for every cocharacter of the torus. -/
theorem rankOneGammaProduct_eq_of_pairing_zero_iff (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i)
    (hKs : ∀ (ξ : cocharacterLattice S)
      (p : (Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i)).carrier X₀),
      (p : RationalPoint F G.X) ∈ K →
        (Dynamic.limitHom (CommGroupScheme.groupHom ξ ≫ i) X₀ p : RationalPoint F G.X) ∈ K)
    {ζ ζ' : cocharacterLattice S}
    (hz : ∀ α ∈ relativeRoots i, latticePairing S α ζ = 0 ↔ latticePairing S α ζ' = 0) :
    rankOneGammaProduct i ζ K hK = rankOneGammaProduct i ζ' K hK := by
  unfold rankOneGammaProduct
  rw [← rankOneCocharacterSet_eq_of_pairing_zero_iff hG hi hz]
  refine finprod_mem_congr rfl fun N hN => ?_
  obtain ⟨β, hβ, rfl⟩ := hN
  exact (rankOneGamma_eq_of_pairing_zero_iff K hK hG hi hKs hz hβ).symm

end Langlands.Plancherel.RationalDynamicSource
