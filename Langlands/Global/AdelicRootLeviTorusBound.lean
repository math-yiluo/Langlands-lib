import Langlands.Global.AdelicCentralTorusHeightTransfer
import Langlands.Global.AdelicRootLeviHeightNormalization
import Langlands.Global.AdelicStandardLeviMinimalCoordinates

/-! # Original torus bounds from intrinsic root-Levi normalization -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]

section OrderedProduct

variable (G : GroupScheme (Spec (CommRingCat.of F)))
  (T A : CommGroupScheme (Spec (CommRingCat.of F))) (f : A ⟶ T)
  (i : T.toGrp ⟶ G)
  (U L : GroupScheme (Spec (CommRingCat.of F))) (zU : U ⟶ G) (zL : L ⟶ G)

/-- Right unipotence and intrinsic norm-one line preservation remove the
two nontorus factors in the actual Levi--torus--unipotent order. -/
theorem orbitHeight_normOne_mul_torus_mul_unipotent
    (hU : IsUnipotent U)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hUline : (ρ.restrict zU).PreservesCoordinateLine j)
    (hLline : (ρ.restrict zL).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j)
    (m : normOneSubgroup F L) (s : AdelicGroupPoints F T.toGrp)
    (x : AdelicGroupPoints F U) :
    orbitHeight F G ρ (Pi.single j 1)
        (map F L G zL m * map F T.toGrp G i s * map F U G zU x) =
      orbitHeight F G ρ (Pi.single j 1) (map F T.toGrp G i s) := by
  have hfix := isOrbitVectorFixedBy_range_of_isUnipotent F G U zU ρ j hUline hU
  rw [orbitHeight_mul_eq_of_fixed F G ρ (Pi.single j 1)
    (map F U G zU).toMonoidHom.range hfix
      (map F L G zL m * map F T.toGrp G i s) (map F U G zU x) ⟨x, rfl⟩,
    orbitHeight_mul_map_eq_lineCharacterNorm F G T.toGrp i ρ j hTline]
  have hm :
      orbitHeight F G ρ (Pi.single j 1) (map F L G zL m) =
        orbitHeight F G ρ (Pi.single j 1) 1 := by
    simpa only [one_mul] using
      orbitHeight_mul_map_normOne F G L zL ρ j hLline 1 m
  rw [hm]
  simpa only [one_mul] using
    (orbitHeight_mul_map_eq_lineCharacterNorm F G T.toGrp i ρ j hTline 1 s).symm

/-- Central cancellation adjusts only the torus in a Levi--torus--unipotent
product; no commutation of the unipotent and Levi factors is required. -/
theorem centralAdjustedTorusPoint_factorization_right_unipotent
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i))
    (a : AdelicGroupPoints F A.toGrp) (m : AdelicGroupPoints F L)
    (s : AdelicGroupPoints F T.toGrp) (x : AdelicGroupPoints F U)
    (p : AdelicGroupPoints F G)
    (hp : map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a * p =
      map F L G zL m * map F T.toGrp G i s * map F U G zU x) :
    p = map F L G zL m *
      map F T.toGrp G i (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s) *
        map F U G zU x := by
  let bT := map F A.toGrp T.toGrp (CommGroupScheme.groupHom f) a
  let bG := map F T.toGrp G i bT
  have hcomp : map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a = bG := by
    change a ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom =
      (a ≫ (CommGroupScheme.groupHom f).hom.hom) ≫ i.hom.hom
    simp only [Grp.comp_hom_hom, Category.assoc]
  have hcomm : Commute bG (map F L G zL m) := by
    rw [← hcomp]
    exact commute_of_mem_center (hc _ a) _
  apply mul_left_cancel (a := bG)
  rw [← hcomp, hp, hcomp]
  symm
  calc
    bG * (map F L G zL m *
        map F T.toGrp G i
          (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s) *
            map F U G zU x) =
        map F L G zL m *
          (bG * map F T.toGrp G i
            (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s)) *
              map F U G zU x := by
      rw [← mul_assoc, ← mul_assoc, hcomm.eq]
      simp only [mul_assoc]
    _ = map F L G zL m * map F T.toGrp G i s * map F U G zU x := by
      simp only [PositiveRealTorus.centralAdjustedTorusPoint, map_mul, map_inv, bG, bT]
      group

/-- Intrinsic norm-one membership and selected-vector height both pass from
the normalized product to its adjusted torus image in this actual order. -/
theorem centralAdjustedTorusPoint_mem_normOne_and_height_right_unipotent
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i)) (hU : IsUnipotent U)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hUline : (ρ.restrict zU).PreservesCoordinateLine j)
    (hLline : (ρ.restrict zL).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j)
    (a : AdelicGroupPoints F A.toGrp) (m : normOneSubgroup F L)
    (s : AdelicGroupPoints F T.toGrp) (x : AdelicGroupPoints F U)
    (p : normOneSubgroup F G)
    (hp : map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a * p =
      map F L G zL m * map F T.toGrp G i s * map F U G zU x) :
    map F T.toGrp G i (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s) ∈
        normOneSubgroup F G ∧
      orbitHeight F G ρ (Pi.single j 1)
        (map F T.toGrp G i (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s)) =
          orbitHeight F G ρ (Pi.single j 1) p := by
  have hfact := centralAdjustedTorusPoint_factorization_right_unipotent
    F G T A f i U L zU zL hc a m s x p hp
  constructor
  · have hx : map F U G zU x ∈ normOneSubgroup F G :=
      range_le_normOne_of_charactersTrivialAlong F U G zU
        (charactersTrivialAlong_of_isUnipotent F U G zU hU) ⟨x, rfl⟩
    have hm : map F L G zL m ∈ normOneSubgroup F G :=
      map_normOneSubgroup_le F L G zL ⟨m, m.property, rfl⟩
    have he :
        map F T.toGrp G i (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s) =
          (map F L G zL m)⁻¹ * p * (map F U G zU x)⁻¹ := by
      rw [hfact]
      group
    rw [he]
    exact (normOneSubgroup F G).mul_mem
      ((normOneSubgroup F G).mul_mem ((normOneSubgroup F G).inv_mem hm) p.property)
      ((normOneSubgroup F G).inv_mem hx)
  · rw [hfact]
    exact (orbitHeight_normOne_mul_torus_mul_unipotent F G T i U L zU zL
      hU ρ j hUline hLline hTline m
      (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s) x).symm

end OrderedProduct

variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

local instance (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom_source

/-- A bounded torus adjustment inside the actual singleton standard Levi,
preserving the original simple-root norm. Membership is intrinsic to this Levi. -/
def HasBoundedRootLeviTorusAdjustment (α : characterLattice T) {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n)) (b : Fin n) (B : ℝ)
    (s : AdelicGroupPoints F T.toGrp) : Prop :=
  let L := Standard.leviScheme i ν {α}
  let iL := standardLeviTorusFactor i ν {α} (Standard.isRepresentedBy_leviHom i ν {α})
  ∃ s' : AdelicGroupPoints F T.toGrp,
    map F T.toGrp L iL s' ∈ normOneSubgroup F L ∧
      PositiveRealTorus.normCharacter F T α s' = PositiveRealTorus.normCharacter F T α s ∧
      orbitHeight F L (ρ.restrict (Standard.leviHom i ν {α}))
        (Pi.single b 1) (map F T.toGrp L iL s') ≤ B

/-- A bounded normalization of a supplied minimal-coordinate product gives a
root-preserving torus adjustment. All line and intrinsic structural data used
to remove its other factors are explicit. -/
theorem hasBoundedRootLeviTorusAdjustment_of_normalization
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (b : Fin n)
    (c C : ℝ)
    (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
    (s : AdelicGroupPoints F T.toGrp)
    (x : AdelicGroupPoints F
      (Standard.unipotentScheme
        (standardLeviTorusFactor i ν {α} (Standard.isRepresentedBy_leviHom i ν {α})) ν ∅))
    (hU : IsUnipotent
      (Standard.unipotentScheme
        (standardLeviTorusFactor i ν {α} (Standard.isRepresentedBy_leviHom i ν {α})) ν ∅))
    (hαL : α ∈ relativeRoots
      (standardLeviTorusFactor i ν {α} (Standard.isRepresentedBy_leviHom i ν {α})))
    (hUline : ((ρ.restrict (Standard.leviHom i ν {α})).restrict
      (Standard.unipotentHom
        (standardLeviTorusFactor i ν {α} (Standard.isRepresentedBy_leviHom i ν {α})) ν ∅)
      ).PreservesCoordinateLine b)
    (hLline : ((ρ.restrict (Standard.leviHom i ν {α})).restrict
      (Standard.minimalLeviToLevi i ν hG hi hν {α}
        (Set.singleton_subset_iff.mpr hα))).PreservesCoordinateLine b)
    (hTline : ((ρ.restrict (Standard.leviHom i ν {α})).restrict
      (standardLeviTorusFactor i ν {α} (Standard.isRepresentedBy_leviHom i ν {α}))
      ).PreservesCoordinateLine b)
    (hnorm : HasBoundedStandardLeviNormalization F G T i ν {α} ρ b c C
      ((mapNormOne F _ _ (Standard.minimalLeviToLevi i ν hG hi hν {α}
        (Set.singleton_subset_iff.mpr hα)) m : AdelicGroupPoints F _) *
          map F _ _ (standardLeviTorusFactor i ν {α}
            (Standard.isRepresentedBy_leviHom i ν {α})) s *
          map F _ _ (Standard.unipotentHom
            (standardLeviTorusFactor i ν {α}
              (Standard.isRepresentedBy_leviHom i ν {α})) ν ∅) x)) :
    HasBoundedRootLeviTorusAdjustment F G T i ν α ρ b (c * C) s := by
  let L := Standard.leviScheme i ν {α}
  let zL := Standard.leviHom i ν {α}
  let iL := standardLeviTorusFactor i ν {α} (Standard.isRepresentedBy_leviHom i ν {α})
  let jL := Standard.minimalLeviToLevi i ν hG hi hν {α}
    (Set.singleton_subset_iff.mpr hα)
  let mL := mapNormOne F _ L jL m
  obtain ⟨A, z, f, hz, hf, a, p, hp, _, hb⟩ := hnorm
  let f' : A ⟶ T := Additive.ofMul f
  have hfL : CommGroupScheme.groupHom f' ≫ iL = z := by
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    have : IsClosedImmersion zL.hom.hom.left :=
      Standard.isClosedSubgroup_leviHom i ν {α}
    apply (cancel_mono zL.hom.hom.left).mp
    have he : (CommGroupScheme.groupHom f' ≫ iL) ≫ zL = z ≫ zL := by
      rw [Category.assoc, standardLeviTorusFactor_comp]
      exact hf
    exact congrArg (fun q : A.toGrp ⟶ G => q.hom.hom.left) he
  have hc : IsCentral (CommGroupScheme.groupHom f' ≫ iL) := by
    rw [hfL]
    exact hz.1.2
  let : LocallyOfFiniteType L.X.hom := by
    have : Smooth L.X.hom :=
      (standardLeviSplitComponentStatement F G hG T i hi ν hν {α}
        (Set.singleton_subset_iff.mpr hα)).1.smooth
    infer_instance
  have hp' : map F A.toGrp L (CommGroupScheme.groupHom f' ≫ iL) a.val * p =
      map F _ L jL m * map F _ L iL s *
        map F _ L (Standard.unipotentHom iL ν ∅) x := by
    rw [hfL]
    exact hp
  obtain ⟨hn, hh⟩ :=
    centralAdjustedTorusPoint_mem_normOne_and_height_right_unipotent
      F L T A f' iL _ _ (Standard.unipotentHom iL ν ∅) jL
        hc hU (ρ.restrict zL) b hUline hLline hTline a.val m s x p hp'
  refine ⟨PositiveRealTorus.centralAdjustedTorusPoint F T A f' a.val s, hn, ?_, ?_⟩
  · exact PositiveRealTorus.normCharacter_centralAdjustedTorusPoint F T A f'
      L iL hz.1.1.1 hc α hαL a.val s
  · exact hh.trans_le hb

/-- Original minimal coordinates satisfying the chosen prefix minimum have a
uniform upper bound on the newly omitted root. The rank-one arithmetic
assertion remains an explicit premise; all root-Levi comparisons are proved. -/
theorem hasUniformRootBound_of_minimal_coordinates_and_prefix_minima
    [LocallyOfFiniteType G.X.hom]
    (harith : RankOneParabolicRationalOrbitHeightBoundStatement.{u})
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
    exists_bounded_rootLevi_normalization_of_prefix_minima F G T i ν harith hG hi hν
      K hK r d ρ b l hl hstab α hα hαK hprev
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
