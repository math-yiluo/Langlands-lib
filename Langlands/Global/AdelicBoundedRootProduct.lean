import Langlands.Global.AdelicNormOneRootBox
import Langlands.Global.AdelicSplitMinimalParabolicCompactCover
import Langlands.Global.AdelicStandardSiegelFactors

/-! # Compact rational representatives for bounded-root parabolic products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise NNReal

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G H T : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] (j : H ⟶ G) (f : T ⟶ H)

omit [IsAffine G.X.left] in
/-- Compact ambient representatives of any subset restrict to compact
representatives in the actual norm-one subgroup. -/
theorem exists_isCompact_normOne_rational_mul_mem_of_ambient
    (S : Set (AdelicGroupPoints F G))
    (hS : ∃ K : Set (AdelicGroupPoints F G), IsCompact K ∧
      ∀ g ∈ S, ∃ q : RationalGroupPoints F G, rational F G q * g ∈ K) :
    ∃ K : Set (normOneSubgroup F G), IsCompact K ∧
      ∀ g : normOneSubgroup F G, (g : AdelicGroupPoints F G) ∈ S →
        ∃ q : RationalGroupPoints F G, rationalNormOne F G q * g ∈ K := by
  obtain ⟨K, hK, hcover⟩ := hS
  refine ⟨((↑) : normOneSubgroup F G → AdelicGroupPoints F G) ⁻¹' K,
    (isClosed_normOneSubgroup F G).isClosedEmbedding_subtypeVal.isCompact_preimage hK, ?_⟩
  intro g hg
  obtain ⟨q, hq⟩ := hcover g hg
  exact ⟨q, hq⟩

/-- Compact principal representatives for a subset of a group mapping into H,
together with a compact norm-one rational cover of H, give compact principal
representatives for the ordered product H¹ S C in the ambient adelic group. -/
theorem exists_isCompact_rational_mul_mem_normOne_mul_set_mul
    (hH : HasCompactNormOneRationalCover H)
    (S : Set (AdelicGroupPoints F T))
    (hS : ∃ K : Set (AdelicGroupPoints F T), IsCompact K ∧
      ∀ s ∈ S, ∃ q : RationalGroupPoints F T, rational F T q * s ∈ K)
    (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C) :
    ∃ K : Set (AdelicGroupPoints F G), IsCompact K ∧
      ∀ g ∈ (map F H G j '' (normOneSubgroup F H : Set (AdelicGroupPoints F H))) *
          (map F T G (f ≫ j) '' S) * C,
        ∃ q : RationalGroupPoints F G, rational F G q * g ∈ K := by
  obtain ⟨KH, hKH, hcoverH⟩ := hH
  obtain ⟨KT, hKT, hcoverT⟩ := hS
  let J := map F H G j
  let D := map F T G (f ≫ j)
  refine ⟨((fun p : normOneSubgroup F H => J p) '' KH) * (D '' KT) * C,
    ((hKH.image (J.continuous.comp continuous_subtype_val)).mul
      (hKT.image D.continuous)).mul hC, ?_⟩
  rintro g ⟨_, ⟨_, ⟨p, hp, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩, c, hc, rfl⟩
  obtain ⟨t, ht⟩ := hcoverT s hs
  let tH : RationalGroupPoints F H := T.affinePointsTarget f (CommAlgCat.of F F) t
  let p' : normOneSubgroup F H := ⟨p, hp⟩ * (rationalNormOne F H tH)⁻¹
  obtain ⟨r, hr⟩ := hcoverH p'
  let rG : RationalGroupPoints F G := H.affinePointsTarget j (CommAlgCat.of F F) r
  have hrG : J (rational F H r) = rational F G rG :=
    (DFunLike.congr_fun (rational_naturality F H j) r).symm
  have htH : J (rational F H tH) = D (rational F T t) := by
    have htH := DFunLike.congr_fun (rational_naturality F T f) t
    simp only [MonoidHom.comp_apply] at htH
    change J (rational F H tH) = _
    rw [htH]
    simp only [J, D, map_apply, GroupScheme.affinePointsTarget_apply,
      Grp.comp_hom_hom, Category.assoc]
  refine ⟨rG, ?_⟩
  refine ⟨_, ⟨_, ⟨rationalNormOne F H r * p', hr, rfl⟩,
    _, ⟨rational F T t * s, ht, rfl⟩, rfl⟩, c, hc, ?_⟩
  change J (rational F H r * (p * (rational F H tH)⁻¹)) *
    D (rational F T t * s) * c =
      rational F G rG * (J p * D s * c)
  rw [map_mul, map_mul, map_inv, htH, hrG, map_mul]
  group

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The ordered product of actual norm-one minimal-parabolic points,
an ambient norm-one simple-root box in the torus, and a specified ambient set. -/
def boundedRootParabolicProduct (b : ℝ≥0) (C : Set (AdelicGroupPoints F G)) :
    Set (AdelicGroupPoints F G) :=
  (map F (Standard.parabolicScheme i ν ∅) G
    (Standard.parabolicHom i ν ∅) ''
      (normOneSubgroup F (Standard.parabolicScheme i ν ∅) :
        Set (AdelicGroupPoints F (Standard.parabolicScheme i ν ∅)))) *
  (map F T.toGrp G i '' ambientNormOneRootBox F G T i ν b) * C

/-- For a split connected reductive group, a two-sided simple-root box with
ambient norm one gives compact principal representatives for P¹ S C,
where P is the actual canonical minimal standard parabolic. -/
theorem exists_isCompact_rational_mul_mem_emptyParabolic_rootBox_mul_compact
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hmax : IsMaximalTorus i)
    (b : ℝ≥0) (hb : 1 ≤ b)
    (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C) :
    ∃ K : Set (AdelicGroupPoints F G), IsCompact K ∧
      ∀ g ∈ boundedRootParabolicProduct F G T i ν b C,
        ∃ q : RationalGroupPoints F G, rational F G q * g ∈ K := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have h :=
    exists_isCompact_rational_mul_mem_normOne_mul_set_mul F G
      (Standard.parabolicScheme i ν ∅) T.toGrp
      (Standard.parabolicHom i ν ∅) (torusToStandardParabolic F G T i ν)
      (hasCompactNormOneRationalCover_emptyParabolic_of_maximalTorus
        i ν hG hi hν hmax)
      (ambientNormOneRootBox F G T i ν b)
      (exists_isCompact_rational_mul_mem_ambientNormOneRootBox
        F G T i ν hG hi hν b hb) C hC
  simpa only [boundedRootParabolicProduct, torusToStandardParabolic_comp] using h

/-- The norm-one part of a bounded-root minimal-parabolic product has compact
principal representatives in the original norm-one adelic group itself. -/
theorem exists_isCompact_normOne_rational_mul_mem_emptyParabolic_rootBox_mul_compact
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hmax : IsMaximalTorus i)
    (b : ℝ≥0) (hb : 1 ≤ b)
    (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C) :
    ∃ K : Set (normOneSubgroup F G), IsCompact K ∧
      ∀ g : normOneSubgroup F G,
        (g : AdelicGroupPoints F G) ∈ boundedRootParabolicProduct F G T i ν b C →
          ∃ q : RationalGroupPoints F G, rationalNormOne F G q * g ∈ K := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact exists_isCompact_normOne_rational_mul_mem_of_ambient F G _
    (exists_isCompact_rational_mul_mem_emptyParabolic_rootBox_mul_compact
      F G T i ν hG hi hν hmax b hb C hC)

end Langlands.Global.AdelicSiegelFactors
