import Langlands.Global.AdelicStandardLeviParabolicMinima
import Langlands.Global.AdelicHeightMinimumCentralNormalization

/-! # Constructing norm-one minima in the first canonical standard Levi -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

local instance standardLeviNormalizedMinimaAffine (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom_source

/-- A positive factor in an actual split component of the canonical first Levi,
and a norm-one factor satisfying the successor minima for its intrinsic standard
parabolics. The original Levi point has no prescribed character norms. -/
def HasNormalizedStandardLeviTailMinima
    (K : ℕ → Set (characterLattice T)) (s : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (j : (a : ℕ) → Fin (d a)) (c : ℝ)
    (h : AdelicGroupPoints F (Standard.leviScheme i ν (K 0))) : Prop :=
  ∃ (A : CommGroupScheme (Spec (CommRingCat.of F)))
    (z : A.toGrp ⟶ Standard.leviScheme i ν (K 0)) (b : A.toGrp ⟶ T.toGrp),
    IsSplitComponent z ∧ b ≫ i = z ≫ Standard.leviHom i ν (K 0) ∧
      ∃ (a : PositiveRealTorus.intrinsicSubgroup F A)
        (m : normOneSubgroup F (Standard.leviScheme i ν (K 0))),
        PositiveRealTorus.positivePointMap F (Standard.leviScheme i ν (K 0)) A z a * m = h ∧
          m ∈ chainHeightMinimalSet F (Standard.leviScheme i ν (K 0)) s
            (fun a => d (a + 1))
            (fun a => (ρ (a + 1)).restrict (Standard.leviHom i ν (K 0)))
            (fun a => Pi.single (j (a + 1)) 1)
            (standardLeviParabolicTailPrefixRationalSubgroup F G T i ν K) c

set_option maxHeartbeats 600000 in
/-- The canonical tail inequalities first restrict to the raw adelic Levi point;
norm-one membership is unnecessary at this stage. -/
theorem mem_adelicChainHeightMinimalSet_standardLevi_tail
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (s : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (j : (a : ℕ) → Fin (d a))
    (hline : ∀ a, ((ρ a).restrict (Standard.parabolicHom i ν (K a))).PreservesCoordinateLine
      (j a))
    (c : ℝ) (h : AdelicGroupPoints F (Standard.leviScheme i ν (K 0)))
    (x : AdelicGroupPoints F (Standard.unipotentScheme i ν (K 0)))
    (p : AdelicGroupPoints F G)
    (hp : p =
      map F (Standard.leviScheme i ν (K 0)) G (Standard.leviHom i ν (K 0)) h *
        map F (Standard.unipotentScheme i ν (K 0)) G
          (Standard.unipotentHom i ν (K 0)) x)
    (hmin : p ∈ adelicChainHeightMinimalSet F G (s + 1) d ρ
      (fun a => Pi.single (j a) 1)
      (closedPrefixRationalSubgroup F G
        (fun a => Standard.parabolicScheme i ν (K a))
        (fun a => Standard.parabolicHom i ν (K a))) c) :
    h ∈ adelicChainHeightMinimalSet F (Standard.leviScheme i ν (K 0)) s
      (fun a => d (a + 1))
      (fun a => (ρ (a + 1)).restrict (Standard.leviHom i ν (K 0)))
      (fun a => Pi.single (j (a + 1)) 1)
      (standardLeviTailPrefixRationalSubgroup F G T i ν K) c := by
  refine mem_adelicChainHeightMinimalSet_restrict_of_fixed_factor F G
    (Standard.leviScheme i ν (K 0)) (Standard.leviHom i ν (K 0))
    (s + 1) s d ρ (fun a => Pi.single (j a) 1)
    (closedPrefixRationalSubgroup F G
      (fun a => Standard.parabolicScheme i ν (K a))
      (fun a => Standard.parabolicHom i ν (K a)))
    (standardLeviTailPrefixRationalSubgroup F G T i ν K)
    (fun a => a + 1) (fun _ ha => Nat.succ_lt_succ ha)
    (map F (Standard.unipotentScheme i ν (K 0)) G
      (Standard.unipotentHom i ν (K 0))).toMonoidHom.range
    ?_ ?_ ?_ c h _ ⟨x, rfl⟩ p hp hmin
  · intro a _
    exact isOrbitVectorFixedBy_range_of_isUnipotent F G
      (Standard.unipotentScheme i ν (K 0)) (Standard.unipotentHom i ν (K 0))
      (ρ (a + 1)) (j (a + 1))
      (preservesCoordinateLine_standardUnipotent_of_standardParabolic F G T i ν hG hi hν
        (K 0) (K (a + 1)) (hK 0) (hK (a + 1))
        (ρ (a + 1)) (j (a + 1)) (hline (a + 1)))
      (isUnipotent_standardUnipotentScheme F G T i ν hG hi hν (K 0) (hK 0))
  · intro a _ q
    exact (standardLeviTailPrefixRationalSubgroup_eq_comap F G T i ν K a).le q.property
  · intro a _ q
    apply standardLevi_adelic_range_le_normalizer F G T i ν (K 0)
    refine ⟨rational F (Standard.leviScheme i ν (K 0)) q, ?_⟩
    exact (DFunLike.congr_fun (rational_naturality F (Standard.leviScheme i ν (K 0))
      (Standard.leviHom i ν (K 0)))
        (q : RationalGroupPoints F (Standard.leviScheme i ν (K 0)))).symm

omit [NumberField F] in
/-- Any morphism into the canonical Levi whose ambient composite factors through
the fixed torus inherits preservation of every ambient standard-parabolic line. -/
theorem preservesCoordinateLine_standardLevi_of_torus_factor
    (J K : Set (characterLattice T))
    (A : GroupScheme (Spec (CommRingCat.of F)))
    (z : A ⟶ Standard.leviScheme i ν J) (b : A ⟶ T.toGrp)
    (hb : b ≫ i = z ≫ Standard.leviHom i ν J)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hline : (ρ.restrict (Standard.parabolicHom i ν K)).PreservesCoordinateLine j) :
    ((ρ.restrict (Standard.leviHom i ν J)).restrict z).PreservesCoordinateLine j := by
  intro Q y
  have hy : y ≫ z.hom.hom ≫ (Standard.leviHom i ν J).hom.hom ∈
      (standardParabolic i ν K).carrier Q := by
    have htorus : (y ≫ b.hom.hom) ≫ i.hom.hom ∈ (SubgroupFunctor.range i).carrier Q :=
      ⟨y ≫ b.hom.hom, rfl⟩
    have hP := standardLevi_le_standardParabolic i ν K Q
      (range_le_standardLevi i ν K Q htorus)
    have hb' : b.hom.hom ≫ i.hom.hom =
        z.hom.hom ≫ (Standard.leviHom i ν J).hom.hom :=
      congrArg (fun f : A ⟶ G => f.hom.hom) hb
    simpa only [Category.assoc, hb'] using hP
  rw [← (Standard.isRepresentedBy_parabolicHom i ν K).2] at hy
  obtain ⟨w, hw⟩ := hy
  change w ≫ (Standard.parabolicHom i ν K).hom.hom =
    y ≫ z.hom.hom ≫ (Standard.leviHom i ν J).hom.hom at hw
  simpa only [MatrixRepresentation.pointMatrix_restrict, hw, Category.assoc] using hline Q w

/-- Construct a norm-one Levi minimum representative from the raw Levi factor.
The split component, its torus factor, and the actual positive factor are all
produced; only the original Levi-unipotent factorization is supplied. -/
theorem hasNormalizedStandardLeviTailMinima_of_factor
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (s : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (j : (a : ℕ) → Fin (d a))
    (hline : ∀ a, ((ρ a).restrict (Standard.parabolicHom i ν (K a))).PreservesCoordinateLine
      (j a))
    (c : ℝ) (h : AdelicGroupPoints F (Standard.leviScheme i ν (K 0)))
    (x : AdelicGroupPoints F (Standard.unipotentScheme i ν (K 0)))
    (p : normOneSubgroup F G)
    (hp : (p : AdelicGroupPoints F G) =
      map F (Standard.leviScheme i ν (K 0)) G (Standard.leviHom i ν (K 0)) h *
        map F (Standard.unipotentScheme i ν (K 0)) G
          (Standard.unipotentHom i ν (K 0)) x)
    (hmin : p ∈ chainHeightMinimalSet F G (s + 1) d ρ
      (fun a => Pi.single (j a) 1)
      (closedPrefixRationalSubgroup F G
        (fun a => Standard.parabolicScheme i ν (K a))
        (fun a => Standard.parabolicHom i ν (K a))) c) :
    HasNormalizedStandardLeviTailMinima F G T i ν K s d ρ j c h := by
  have hraw := mem_adelicChainHeightMinimalSet_standardLevi_tail F G T i ν
    hG hi hν K hK s d ρ j hline c h x p hp hmin
  obtain ⟨hL, A, z, b, hz, hb⟩ :=
    standardLeviSplitComponentStatement F G hG T i hi ν hν (K 0) (hK 0)
  obtain ⟨a, m, hfact, hm⟩ := exists_normOne_chainHeightMinimalSet_of_splitComponent
    F (Standard.leviScheme i ν (K 0)) hL A z hz s
    (fun a => d (a + 1))
    (fun a => (ρ (a + 1)).restrict (Standard.leviHom i ν (K 0)))
    (fun a => j (a + 1)) (fun a _ =>
      preservesCoordinateLine_standardLevi_of_torus_factor F G T i ν
        (K 0) (K (a + 1)) A.toGrp z b hb (ρ (a + 1)) (j (a + 1)) (hline (a + 1)))
    (standardLeviTailPrefixRationalSubgroup F G T i ν K) c h hraw
  refine ⟨A, z, b, hz, hb, a, m, hfact, ?_⟩
  have he :
      standardLeviParabolicTailPrefixRationalSubgroup F G T i ν K =
        standardLeviTailPrefixRationalSubgroup F G T i ν K :=
    funext (standardLeviParabolicTailPrefixRationalSubgroup_eq_tail
      F G T i ν hG hi hν K hK)
  rwa [he]

end Langlands.Global.RepresentationGrowth
