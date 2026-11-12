import Langlands.Global.AdelicStandardParabolicMinimumDecomposition
import Langlands.Global.AdelicRankOneOrbitHeightBound

/-! # Normalized root-Levi height bounds from preceding-intersection minima -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

local instance (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom_source

/-- A constructed positive central normalization of a raw standard-Levi point,
retaining the full rational minimum inequality and an explicit height bound. -/
def HasBoundedStandardLeviNormalization
    (J : Set (characterLattice T)) {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n)) (b : Fin n) (c C : ℝ)
    (h : AdelicGroupPoints F (Standard.leviScheme i ν J)) : Prop :=
  ∃ (A : CommGroupScheme (Spec (CommRingCat.of F)))
    (z : A.toGrp ⟶ Standard.leviScheme i ν J) (f : A.toGrp ⟶ T.toGrp),
    IsSplitComponent z ∧ f ≫ i = z ≫ Standard.leviHom i ν J ∧
      ∃ (a : PositiveRealTorus.intrinsicSubgroup F A)
        (m : normOneSubgroup F (Standard.leviScheme i ν J)),
        PositiveRealTorus.positivePointMap F (Standard.leviScheme i ν J) A z a * m = h ∧
          IsRationalOrbitHeightApproximateMinimum F (Standard.leviScheme i ν J)
            (ρ.restrict (Standard.leviHom i ν J)) (Pi.single b 1) c m ∧
          orbitHeight F (Standard.leviScheme i ν J)
            (ρ.restrict (Standard.leviHom i ν J)) (Pi.single b 1) m ≤ c * C

omit [NumberField F] in
/-- If a standard Levi is contained in each preceding individual parabolic,
all of its rational points lie in the preceding rational intersection. -/
theorem standardLevi_rational_mem_closedPrefix
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)
    (l : ℕ) (hprev : ∀ a, a < l → J ⊆ K a)
    (q : RationalGroupPoints F (Standard.leviScheme i ν J)) :
    (Standard.leviScheme i ν J).affinePointsTarget
        (Standard.leviHom i ν J) (CommAlgCat.of F F) q ∈
      closedPrefixRationalSubgroup F G
        (fun a => Standard.parabolicScheme i ν (K a))
        (fun a => Standard.parabolicHom i ν (K a)) l := by
  apply (mem_closedPrefixRationalSubgroup F G _ _ l _).2
  intro a ha
  have hL : standardLevi i ν J ≤ standardLevi i ν (K a) :=
    (((standardParabolicOrder F G hG T i hi ν hν).1 J (K a) hJ (hK a)).2
      (hprev a ha)).1
  have hq : q ≫ (Standard.leviHom i ν J).hom.hom ∈
      (standardLevi i ν J).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))) := by
    rw [← (Standard.isRepresentedBy_leviHom i ν J).2]
    exact ⟨q, rfl⟩
  have hp := standardLevi_le_standardParabolic i ν (K a) _ (hL _ hq)
  change _ ∈ (SubgroupFunctor.range (Standard.parabolicHom i ν (K a))).carrier _
  rw [(Standard.isRepresentedBy_parabolicHom i ν (K a)).2]
  exact hp

/-- A chosen prefix inequality restricts to the full rational group of any
standard Levi contained in the preceding parabolics. The raw Levi need not
be intrinsically norm one. The canonical unipotent factor is removed only
after checking its normalization by every tested rational Levi point. -/
theorem isRationalOrbitHeightApproximateMinimum_standardLevi_of_prefix
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (r : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (b : (a : ℕ) → Fin (d a))
    (l : ℕ) (hl : l < r)
    (hline : ((ρ l).restrict (Standard.parabolicHom i ν (K l))).PreservesCoordinateLine
      (b l))
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hprev : ∀ a, a < l → J ⊆ K a)
    (c : ℝ) (h : AdelicGroupPoints F (Standard.leviScheme i ν J))
    (x : AdelicGroupPoints F (Standard.unipotentScheme i ν J))
    (p : AdelicGroupPoints F G)
    (hp : p = map F _ G (Standard.leviHom i ν J) h *
      map F _ G (Standard.unipotentHom i ν J) x)
    (hmin : p ∈ adelicChainHeightMinimalSet F G r d ρ
      (fun a => Pi.single (b a) 1)
      (closedPrefixRationalSubgroup F G
        (fun a => Standard.parabolicScheme i ν (K a))
        (fun a => Standard.parabolicHom i ν (K a))) c) :
    IsRationalOrbitHeightApproximateMinimum F (Standard.leviScheme i ν J)
      ((ρ l).restrict (Standard.leviHom i ν J)) (Pi.single (b l) 1) c h := by
  let N := (map F (Standard.unipotentScheme i ν J) G
    (Standard.unipotentHom i ν J)).toMonoidHom.range
  have hfix : IsOrbitVectorFixedBy F G (ρ l) (Pi.single (b l) 1) N :=
    isOrbitVectorFixedBy_range_of_isUnipotent F G _ _ (ρ l) (b l)
      (preservesCoordinateLine_standardUnipotent_of_standardParabolic F G T i ν
        hG hi hν J (K l) hJ (hK l) (ρ l) (b l) hline)
      (isUnipotent_standardUnipotentScheme F G T i ν hG hi hν J hJ)
  intro q
  let qG : closedPrefixRationalSubgroup F G
      (fun a => Standard.parabolicScheme i ν (K a))
      (fun a => Standard.parabolicHom i ν (K a)) l :=
    ⟨(Standard.leviScheme i ν J).affinePointsTarget
      (Standard.leviHom i ν J) (CommAlgCat.of F F) q,
        standardLevi_rational_mem_closedPrefix F G T i ν hG hi hν K hK J hJ l hprev q⟩
  have hm := hmin l hl qG
  have hnorm : rational F G qG ∈
      Subgroup.normalizer (N : Set (AdelicGroupPoints F G)) := by
    apply standardLevi_adelic_range_le_normalizer F G T i ν J
    refine ⟨rational F _ q, ?_⟩
    exact (DFunLike.congr_fun (rational_naturality F _
      (Standard.leviHom i ν J)) q).symm
  have hx : map F _ G (Standard.unipotentHom i ν J) x ∈ N := ⟨x, rfl⟩
  change orbitHeight F G (ρ l) (Pi.single (b l) 1) p ≤
    c * orbitHeight F G (ρ l) (Pi.single (b l) 1) (p * rational F G qG) at hm
  rw [hp, orbitHeight_mul_eq_of_fixed F G _ _ N hfix _ _ hx,
    orbitHeight_mul_mul_eq_of_normalizer F G _ _ N hfix _ _ _ hx hnorm] at hm
  have hnat : map F _ G (Standard.leviHom i ν J) (rational F _ q) =
      rational F G qG :=
    (DFunLike.congr_fun (rational_naturality F _
      (Standard.leviHom i ν J)) q).symm
  simpa only [orbitHeight_restrict, map_mul, hnat] using hm

/-- The universal rank-one arithmetic assertion bounds the representation
obtained by restricting an exact ambient parabolic line to the singleton
standard Levi, when that root is absent from the ambient parabolic index. -/
theorem hasUniformNormOneRationalOrbitHeightBound_rootLevi
    [LocallyOfFiniteType G.X.hom]
    (harith : RankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν)
    (K : Set (characterLattice T)) (hK : K ⊆ simpleRelativeRoots i ν) (hαK : α ∉ K)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (b : Fin n)
    (hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν K) b) :
    HasUniformNormOneRationalOrbitHeightBound F (Standard.leviScheme i ν {α})
      (ρ.restrict (Standard.leviHom i ν {α})) (Pi.single b 1) := by
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
  exact harith F L hL T iL hiL ν hνL α hsimple n (ρ.restrict zL) b hstabL

/-- Each finite-prefix minimum yields a uniformly height-bounded intrinsic
normalization in the root Levi belonging to its newly omitted simple root.
The arithmetic constant precedes every comparison constant and point. -/
theorem exists_bounded_rootLevi_normalization_of_prefix_minima
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
    (hasUniformNormOneRationalOrbitHeightBound_rootLevi F G T i ν harith hG hi hν
      α hα (K l) (hK l) hαK (ρ l) (b l) hstab).bounds_approximate_minima F _
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

end Langlands.Global.RepresentationGrowth
