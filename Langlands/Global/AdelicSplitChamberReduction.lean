import Langlands.Global.AdelicChamberFromRankOneHeight
import Langlands.Global.AdelicSplitRankOneOrbitHeightBound
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Chamber reduction from root-Levi height bounds, and its split case -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal Pointwise

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

local instance (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom_source

/-- The root-Levi arithmetic input of the chamber reduction, for one fixed setup.
For every simple relative root `α` and every set `K` of simple relative roots not
containing `α`, an exact coordinate line of the standard parabolic `P_K`, restricted to the
singleton standard Levi `L_α`, has a uniform norm-one rational-orbit height bound
on `L_α`. -/
def HasRootLeviHeightBounds : Prop :=
  ∀ α ∈ simpleRelativeRoots i ν, ∀ K : Set (characterLattice T),
    K ⊆ simpleRelativeRoots i ν → α ∉ K →
      ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (b : Fin n),
        ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν K) b →
          HasUniformNormOneRationalOrbitHeightBound F (Standard.leviScheme i ν {α})
            (ρ.restrict (Standard.leviHom i ν {α})) (Pi.single b 1)

/-- The universal rank-one height bound supplies the root-Levi input. -/
theorem hasRootLeviHeightBounds_of_rankOne
    [LocallyOfFiniteType G.X.hom]
    (harith : RankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    HasRootLeviHeightBounds F G T i ν :=
  fun α hα K hK hαK _ ρ b hstab =>
    hasUniformNormOneRationalOrbitHeightBound_rootLevi F G T i ν harith hG hi hν
      α hα K hK hαK ρ b hstab

/-- For a split group, the split rank-one height bound already supplies the root-Levi
input: the ambient torus factor of each singleton standard Levi is again a maximal
torus, so every such Levi is split. -/
theorem hasRootLeviHeightBounds_of_splitRankOne
    [LocallyOfFiniteType G.X.hom]
    (hsplit : SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hT : IsMaximalTorus i)
    (hν : IsGenericCocharacter i ν) :
    HasRootLeviHeightBounds F G T i ν := by
  intro α hα K hK hαK n ρ b hstab
  let L := Standard.leviScheme i ν {α}
  let zL := Standard.leviHom i ν {α}
  let iL := standardLeviTorusFactor i ν {α} (Standard.isRepresentedBy_leviHom i ν {α})
  have hJ : ({α} : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    Set.singleton_subset_iff.mpr hα
  have hL := (standardLeviSplitComponentStatement F G hG T i hi ν hν {α} hJ).1
  let : LocallyOfFiniteType L.X.hom := by
    have : IsClosedImmersion zL.hom.hom.left := Standard.isClosedSubgroup_leviHom i ν {α}
    rw [← Over.w zL.hom.hom]
    infer_instance
  have hiL : IsMaximalSplitTorus iL :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν {α}
      (Standard.isRepresentedBy_leviHom i ν {α}) (Standard.isClosedSubgroup_leviHom i ν {α})
  have hTL : IsMaximalTorus iL := by
    apply IsMaximalTorus.of_comp (Standard.isClosedSubgroup_leviHom i ν {α})
    rw [standardLeviTorusFactor_comp]
    exact hT
  obtain ⟨hsimple, hνL, _⟩ := standardLeviStandardFamilies dynamicLie standardCocharacter
    F G hG T i hi ν hν {α} hJ L hL zL
      (Standard.isRepresentedBy_leviHom i ν {α}) (Standard.isClosedSubgroup_leviHom i ν {α})
  have hinter : ({α} : Set (characterLattice T)) ∩ K = ∅ := by
    ext β
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    intro heq
    simpa only [heq] using hαK
  have hstabL := standardLevi_inter_coordinateLine_stabilizer i ν hG hi hν
    {α} K hJ hK ρ b hstab
  rw [hinter] at hstabL
  exact hsplit F L hL T iL hiL hTL ν hνL α hsimple n (ρ.restrict zL) b hstabL

/-- `exists_bounded_rootLevi_normalization_of_prefix_minima`, with the universal
rank-one premise replaced by the root-Levi input of the fixed setup. -/
theorem exists_bounded_rootLevi_normalization_of_prefix_minima_of_rootLevi
    (hroot : HasRootLeviHeightBounds F G T i ν)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (r : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (b : (a : ℕ) → Fin (d a))
    (l : ℕ) (hl : l < r)
    (hstab : (ρ l).HasExactCoordinateLineStabilizer (standardParabolic i ν (K l)) (b l))
    (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν)
    (hαK : α ∉ K l) (hprev : ∀ a, a < l → α ∈ K a) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      ∀ (h : AdelicGroupPoints F (Standard.leviScheme i ν {α}))
        (x : AdelicGroupPoints F (Standard.unipotentScheme i ν {α}))
        (p : AdelicGroupPoints F G),
        p = map F _ G (Standard.leviHom i ν {α}) h *
          map F _ G (Standard.unipotentHom i ν {α}) x →
        p ∈ adelicChainHeightMinimalSet F G r d ρ
          (fun a => Pi.single (b a) 1)
          (closedPrefixRationalSubgroup F G
            (fun a => Standard.parabolicScheme i ν (K a))
            (fun a => Standard.parabolicHom i ν (K a))) c →
        HasBoundedStandardLeviNormalization F G T i ν {α} (ρ l) (b l) c C h := by
  have hJ : ({α} : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    Set.singleton_subset_iff.mpr hα
  have hline :
      ((ρ l).restrict (Standard.parabolicHom i ν (K l))).PreservesCoordinateLine (b l) := by
    intro Q y
    have hy : y ≫ (Standard.parabolicHom i ν (K l)).hom.hom ∈
        (standardParabolic i ν (K l)).carrier Q := by
      rw [← (Standard.isRepresentedBy_parabolicHom i ν (K l)).2]
      exact ⟨y, rfl⟩
    simpa only [MatrixRepresentation.pointMatrix_restrict] using
      (hstab Q (y ≫ (Standard.parabolicHom i ν (K l)).hom.hom)).mp hy
  obtain ⟨C, hC, hbound⟩ :=
    (hroot α hα (K l) (hK l) hαK (d l) (ρ l) (b l) hstab).bounds_approximate_minima F _
  refine ⟨C, hC, ?_⟩
  intro c hc h x p hp hmin
  have hraw := isRationalOrbitHeightApproximateMinimum_standardLevi_of_prefix
    F G T i ν hG hi hν K hK r d ρ b l hl hline {α} hJ
      (fun a ha => Set.singleton_subset_iff.mpr (hprev a ha)) c h x p hp hmin
  obtain ⟨hL, A, z, f, hz, hf⟩ :=
    standardLeviSplitComponentStatement F G hG T i hi ν hν {α} hJ
  obtain ⟨a, m, hfact, hm⟩ := exists_normOne_chainHeightMinimalSet_of_splitComponent
    F (Standard.leviScheme i ν {α}) hL A z hz 1 (fun _ => d l)
    (fun _ => (ρ l).restrict (Standard.leviHom i ν {α})) (fun _ => b l)
    (fun _ _ => preservesCoordinateLine_standardLevi_of_torus_factor F G T i ν
      {α} (K l) A.toGrp z f hf (ρ l) (b l) hline)
    (fun _ => ⊤) c h (by
      intro _ _ q
      exact hraw q)
  have hm' : IsRationalOrbitHeightApproximateMinimum F (Standard.leviScheme i ν {α})
      ((ρ l).restrict (Standard.leviHom i ν {α})) (Pi.single (b l) 1) c m :=
    fun q => hm 0 (by omega) ⟨q, Subgroup.mem_top q⟩
  exact ⟨A, z, f, hz, hf, a, m, hfact, hm', hbound c hc m hm'⟩

/-- `hasUniformRootBound_of_minimal_coordinates_and_prefix_minima`, with the universal
rank-one premise replaced by the root-Levi input of the fixed setup. -/
theorem hasUniformRootBound_of_minimal_coordinates_and_prefix_minima_of_rootLevi
    (hroot : HasRootLeviHeightBounds F G T i ν)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (r : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (b : (a : ℕ) → Fin (d a))
    (l : ℕ) (hl : l < r)
    (hstab : (ρ l).HasExactCoordinateLineStabilizer (standardParabolic i ν (K l)) (b l))
    (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν)
    (hαK : α ∉ K l) (hprev : ∀ a, a < l → α ∈ K a)
    (c : ℝ) (hc : 0 < c) (S : Set (AdelicGroupPoints F T.toGrp))
    (hS : ∀ s ∈ S,
      ∃ (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
        (x : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)),
        map F _ G (Standard.leviHom i ν ∅) m * map F _ G i s *
            map F _ G (Standard.unipotentHom i ν ∅) x ∈
          adelicChainHeightMinimalSet F G r d ρ (fun a => Pi.single (b a) 1)
            (closedPrefixRationalSubgroup F G
              (fun a => Standard.parabolicScheme i ν (K a))
              (fun a => Standard.parabolicHom i ν (K a))) c) :
    PositiveRealTorus.HasUniformCharacterBound F T α S := by
  let L := Standard.leviScheme i ν {α}
  let zL := Standard.leviHom i ν {α}
  let iL := standardLeviTorusFactor i ν {α} (Standard.isRepresentedBy_leviHom i ν {α})
  have hJ : ({α} : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    Set.singleton_subset_iff.mpr hα
  let jL := Standard.minimalLeviToLevi i ν hG hi hν {α} hJ
  have hL := (standardLeviSplitComponentStatement F G hG T i hi ν hν {α} hJ).1
  have hiL : IsMaximalSplitTorus iL :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν {α}
      (Standard.isRepresentedBy_leviHom i ν {α}) (Standard.isClosedSubgroup_leviHom i ν {α})
  obtain ⟨hsimple, hνL, _⟩ := standardLeviStandardFamilies dynamicLie standardCocharacter
    F G hG T i hi ν hν {α} hJ L hL zL
      (Standard.isRepresentedBy_leviHom i ν {α}) (Standard.isClosedSubgroup_leviHom i ν {α})
  have hinter : ({α} : Set (characterLattice T)) ∩ K l = ∅ := by
    ext β
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro heq
    simpa only [heq] using hαK
  have hstabL := standardLevi_inter_coordinateLine_stabilizer i ν hG hi hν
    {α} (K l) hJ (hK l) (ρ l) (b l) hstab
  rw [hinter] at hstabL
  let : Mono iL.hom.hom.left := hiL.isSplitSubtorus.mono
  let : Fintype (relativeWeylGroup iL) :=
    relativeWeylGroupFintype iL (relativeRootSystem F L hL T iL hiL)
  obtain ⟨hTline, hrel⟩ :=
    MatrixRepresentation.positiveRootRelation_of_exact_emptyStandardParabolic_stabilizer
      iL hL hiL ν hνL α hsimple ((ρ l).restrict zL) (b l) hstabL
  have hαL : α ∈ relativeRoots iL :=
    (show α ∈ simpleRelativeRoots iL ν by rw [hsimple]; rfl).1.1
  have hU : IsUnipotent (Standard.unipotentScheme iL ν ∅) :=
    isUnipotent_standardUnipotentScheme F L T iL ν hL hiL hνL ∅ (Set.empty_subset _)
  have hUline : (((ρ l).restrict zL).restrict
      (Standard.unipotentHom iL ν ∅)).PreservesCoordinateLine (b l) := by
    intro Q y
    have hy : y ≫ (Standard.unipotentHom iL ν ∅).hom.hom ∈
        (standardUnipotent iL ν ∅).carrier Q := by
      rw [← (Standard.isRepresentedBy_unipotentHom iL ν ∅).2]
      exact ⟨y, rfl⟩
    simpa only [MatrixRepresentation.pointMatrix_restrict] using
      (hstabL Q (y ≫ (Standard.unipotentHom iL ν ∅).hom.hom)).mp
        (standardUnipotent_le_standardParabolic iL ν ∅ Q hy)
  have hLline : (((ρ l).restrict zL).restrict jL).PreservesCoordinateLine (b l) := by
    intro Q y
    have hy : y ≫ (Standard.leviHom i ν ∅).hom.hom ∈
        (standardLevi i ν ∅).carrier Q := by
      rw [← (Standard.isRepresentedBy_leviHom i ν ∅).2]
      exact ⟨y, rfl⟩
    have hinc : standardLevi i ν ∅ ≤ standardLevi i ν (K l) :=
      (((standardParabolicOrder F G hG T i hi ν hν).1 ∅ (K l)
        (Set.empty_subset _) (hK l)).2 (Set.empty_subset _)).1
    have hline := (hstab Q (y ≫ (Standard.leviHom i ν ∅).hom.hom)).mp
      (standardLevi_le_standardParabolic i ν (K l) Q (hinc Q hy))
    have hjcomp : jL.hom.hom ≫ zL.hom.hom = (Standard.leviHom i ν ∅).hom.hom :=
      congrArg (fun f : Standard.leviScheme i ν ∅ ⟶ G => f.hom.hom)
        (Standard.minimalLeviToLevi_comp i ν hG hi hν {α} hJ)
    simpa only [MatrixRepresentation.pointMatrix_restrict, Category.assoc, hjcomp] using hline
  obtain ⟨C, hC, hbound⟩ :=
    exists_bounded_rootLevi_normalization_of_prefix_minima_of_rootLevi F G T i ν hroot
      hG hi hν K hK r d ρ b l hl hstab α hα hαK hprev
  apply hasUniformRootBound_of_normOne_torus_adjustments F T L iL
    ((ρ l).restrict zL) (b l) hTline α hrel S (c * C) (mul_pos hc hC)
  intro s hs
  obtain ⟨m, x, hmin⟩ := hS s hs
  obtain ⟨y, z, hfact⟩ :=
    exists_standardLevi_minimal_coordinates F G T i ν hG hi hν {α} hJ m s x
  have hnorm := hbound c hc.le _ z _ hfact hmin
  exact hasBoundedRootLeviTorusAdjustment_of_normalization F G T i ν
    hG hi hν α hα (ρ l) (b l) c C m s y hU hαL hUline hLline hTline hnorm

end Langlands.Global.RepresentationGrowth

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- `hasWeakChamberReduction_of_rankOne_height`, with the universal rank-one premise
replaced by the root-Levi input of the fixed setup. The proof is the published one. -/
theorem hasWeakChamberReduction_of_rootLeviHeightBounds
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hroot : HasRootLeviHeightBounds F G T i ν)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K) :
    HasWeakChamberReduction F G T i ν T₀ j K := by
  classical
  let Δ := simpleRelativeRoots i ν
  have hfinite : Δ.Finite := hS.1.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype Δ := hfinite.fintype
  let r := Fintype.card Δ
  let e : Fin r ≃ Δ := (Fintype.equivFin Δ).symm
  let α : ℕ → characterLattice T := fun l =>
    if h : l < r then (e ⟨l, h⟩).val else 0
  have hα (l : ℕ) (hl : l < r) : α l ∈ Δ := by
    simpa only [α, dite_eq_left hl] using (e ⟨l, hl⟩).property
  have hinj (a l : ℕ) (ha : a < r) (hl : l < r) (heq : α a = α l) : a = l := by
    simp only [α, dite_eq_left ha, dite_eq_left hl] at heq
    exact congrArg Fin.val (e.injective (Subtype.ext heq))
  have hcover (β : characterLattice T) (hβ : β ∈ Δ) :
      ∃ l, l < r ∧ α l = β := by
    let l := e.symm ⟨β, hβ⟩
    refine ⟨l.val, l.isLt, ?_⟩
    simp only [α, dite_eq_left l.isLt, Fin.eta]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨β, hβ⟩)
  let J : ℕ → Set (characterLattice T) := fun l => Δ \ {α l}
  have hJ (l : ℕ) : J l ⊆ simpleRelativeRoots i ν := fun _ h => h.1
  obtain ⟨d, b, ρ, hstab, _, hmin⟩ :=
    exists_adapted_standardParabolicPrefix_minima F G T i ν J
  let d' : ℕ → ℕ := fun l => d l + 1
  let Q := closedPrefixRationalSubgroup F G
    (fun l => Standard.parabolicScheme i ν (J l))
    (fun l => Standard.parabolicHom i ν (J l))
  have hv (l : ℕ) (_ : l < r) :
      (Pi.single (b l) 1 : Fin (d' l) → F) ≠ 0 := by
    intro hz
    have he := congrFun hz (b l)
    simp at he
  obtain ⟨D, hD, htransport⟩ := exists_pos_chainHeightMinimalSet_compact_transport
    F G r d' ρ (fun l _ => Nat.zero_lt_succ (d l)) hK.1.1
  let S : Set (AdelicGroupPoints F T.toGrp) := {s |
    ∃ (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (x : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)),
      map F _ G (Standard.leviHom i ν ∅) m * map F _ G i s *
          map F _ G (Standard.unipotentHom i ν ∅) x ∈
        adelicChainHeightMinimalSet F G r d' ρ (fun l => Pi.single (b l) 1) Q D}
  have hbound : PositiveRealTorus.HasUniformSimpleRootBound F G T i ν S := by
    apply PositiveRealTorus.hasUniformSimpleRootBound_of_character_bounds
      F G T i ν hfinite S
    intro β hβ
    obtain ⟨l, hl, rfl⟩ := hcover β hβ
    apply hasUniformRootBound_of_minimal_coordinates_and_prefix_minima_of_rootLevi
      F G T i ν hroot hG hS.1 hS.2.1 J hJ r d' ρ b l hl (hstab l)
        (α l) (hα l hl) (by simp [J]) (fun a ha => ?_) D hD S
    · exact fun _ hs => hs
    · refine ⟨hα l hl, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      have heq' := hinj l a hl (ha.trans hl) heq
      omega
  obtain ⟨t, ht⟩ := hbound.exists_lower_inv F G T i ν
  let s : PositiveRealTorus.intrinsicSubgroup F T₀ → AdelicGroupPoints F T.toGrp :=
    fun a => map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a
  have hs (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
      map F T.toGrp G i (s a) = positiveMap F G T i T₀ j a := by
    change (a.val ≫ (CommGroupScheme.groupHom j).hom.hom) ≫ i.hom.hom =
      a.val ≫ (CommGroupScheme.groupHom j ≫ i).hom.hom
    rw [Grp.comp_hom_hom, Category.assoc]
  refine ⟨t, fun g => ?_⟩
  obtain ⟨q, hq⟩ := hmin r g⁻¹
  let y : normOneSubgroup F G := g⁻¹ * rationalNormOne F G q
  let z : normOneSubgroup F G := rationalNormOne F G q⁻¹ * g
  have hzy : z⁻¹ = y := by
    simp only [z, y, mul_inv_rev, map_inv, inv_inv]
  obtain ⟨x, m, a, k, hk, heq⟩ := HasMinimalParabolicNormFactors.exists_iwasawa_factors
    F G T i ν T₀ j (hS.hasMinimalParabolicNormFactors F G T i ν T₀ j hG) K hK z
  let p₀ := map F _ G (Standard.unipotentHom i ν ∅) x *
    map F _ G (Standard.leviHom i ν ∅) m * positiveMap F G T i T₀ j a
  have hp₀ : p₀ = (z : AdelicGroupPoints F G) * k⁻¹ := by
    rw [← heq]
    simp only [p₀, mul_inv_cancel_right]
  have hpone : p₀⁻¹ ∈ normOneSubgroup F G := by
    rw [hp₀]
    exact (normOneSubgroup F G).inv_mem ((normOneSubgroup F G).mul_mem z.property
      ((normOneSubgroup F G).inv_mem
        (compactSubgroup_le_normOneSubgroup F G K hK.1.1 hk)))
  let p : normOneSubgroup F G := ⟨p₀⁻¹, hpone⟩
  let k' : normOneSubgroup F G := ⟨k⁻¹,
    compactSubgroup_le_normOneSubgroup F G K hK.1.1 (K.inv_mem hk)⟩
  have hk'p : k' * p = y := by
    apply Subtype.ext
    change k⁻¹ * p₀⁻¹ = (y : AdelicGroupPoints F G)
    rw [← mul_inv_rev]
    change (p₀ * k)⁻¹ = (y : AdelicGroupPoints F G)
    rw [heq]
    exact congrArg Subtype.val hzy
  have hpmin : p ∈ chainHeightMinimalSet F G r d' ρ
      (fun l => Pi.single (b l) 1) Q D := by
    have h := (htransport (fun l => Pi.single (b l) 1) hv Q k' (K.inv_mem hk)
      p 1 zero_le_one).2 (hk'p.symm ▸ hq)
    simpa only [mul_one] using h
  have hporder :
      map F _ G (Standard.leviHom i ν ∅) (m⁻¹ : normOneSubgroup F _) *
        map F _ G i (s a)⁻¹ * map F _ G (Standard.unipotentHom i ν ∅) x⁻¹ =
          (p : AdelicGroupPoints F G) := by
    have hc := (hS.commute_torus_minimalLevi F G T i ν T₀ j (s a) m).inv_inv
    simp only [hs] at hc
    change _ = p₀⁻¹
    simp only [p₀, mul_inv_rev, Subgroup.coe_inv, map_inv, hs]
    rw [← mul_assoc, hc.eq]
  have hsa : (s a)⁻¹ ∈ S := by
    refine ⟨m⁻¹, x⁻¹, ?_⟩
    rw [hporder]
    exact hpmin
  have ha : a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t := by
    intro β hβ
    have h := ht β hβ (s a)⁻¹ hsa
    rw [inv_inv] at h
    exact (PositiveRealTorus.normCharacter_pullback F T₀ T j β a).symm ▸ h
  refine ⟨q⁻¹, x, m, a, ha, k, hk, ?_⟩
  simpa only [z, Subgroup.coe_mul, rationalNormOne_val] using heq

/-- For a split group, the split rank-one height bound gives the weak chamber reduction
for every actual Siegel setup and every prescribed Iwasawa compact subgroup. -/
theorem hasWeakChamberReduction_of_splitRankOne_height
    [LocallyOfFiniteType G.X.hom]
    (hsplit : SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j) (hT : IsMaximalTorus i)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K) :
    HasWeakChamberReduction F G T i ν T₀ j K :=
  hasWeakChamberReduction_of_rootLeviHeightBounds F G T i ν T₀ j hG hS
    (hasRootLeviHeightBounds_of_splitRankOne F G T i ν hsplit hG hS.1 hT hS.2.1) K hK

end Langlands.Global.AdelicSiegelFactors
