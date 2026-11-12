import Langlands.Global.AdelicStandardLeviNormalizedMinima
import Langlands.Global.AdelicHeightMinimumCompactTransport
import Langlands.Global.AdelicIwasawaStatement

/-! # Actual Iwasawa and Levi decompositions of simultaneous height minima -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Pointwise

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

/-- The actual Levi-unipotent factorization and the normalized intrinsic tail
minimum data, now asserted directly for an ambient parabolic point. -/
def HasNormalizedStandardParabolicTailMinima
    (K : ℕ → Set (characterLattice T)) (s : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (j : (a : ℕ) → Fin (d a)) (c : ℝ) (p : AdelicGroupPoints F G) : Prop :=
  ∃ (h : AdelicGroupPoints F (Standard.leviScheme i ν (K 0)))
    (x : AdelicGroupPoints F (Standard.unipotentScheme i ν (K 0))),
    p = map F (Standard.leviScheme i ν (K 0)) G (Standard.leviHom i ν (K 0)) h *
      map F (Standard.unipotentScheme i ν (K 0)) G
        (Standard.unipotentHom i ν (K 0)) x ∧
      HasNormalizedStandardLeviTailMinima F G T i ν K s d ρ j c h

/-- Every actual adelic point of a valid standard parabolic is a canonical Levi
image times a canonical unipotent image, in the order used by height restriction. -/
theorem exists_standardLevi_mul_standardUnipotent_of_mem_range
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)
    (p : AdelicGroupPoints F G)
    (hp : p ∈ (map F (Standard.parabolicScheme i ν J) G
      (Standard.parabolicHom i ν J)).toMonoidHom.range) :
    ∃ (h : AdelicGroupPoints F (Standard.leviScheme i ν J))
      (x : AdelicGroupPoints F (Standard.unipotentScheme i ν J)),
      p = map F (Standard.leviScheme i ν J) G (Standard.leviHom i ν J) h *
        map F (Standard.unipotentScheme i ν J) G
          (Standard.unipotentHom i ν J) x := by
  let Q := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))
  have hP :
      (map F (Standard.parabolicScheme i ν J) G
        (Standard.parabolicHom i ν J)).toMonoidHom.range =
          (standardParabolic i ν J).carrier Q :=
    congrArg (fun S : SubgroupFunctor G => S.carrier Q)
      (Standard.isRepresentedBy_parabolicHom i ν J).2
  rw [hP] at hp
  obtain ⟨⟨ζ, hζ⟩, heq⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  obtain ⟨v, hv, l, hl, hvl⟩ :=
    StandardLeviIntersection.exists_standardUnipotent_mul_standardLevi i ν
      ⟨hζ, (heq ζ hζ).2.1.ge, (heq ζ hζ).2.2.ge⟩ hp
  have hx : l⁻¹ * v * l ∈ (standardUnipotent i ν J).carrier Q := by
    simpa only [inv_inv] using
      StandardLeviIntersection.conj_mem_standardUnipotent i ν
        (inv_mem (standardLevi_le_standardParabolic i ν J Q hl)) hv
  rw [← (Standard.isRepresentedBy_leviHom i ν J).2] at hl
  rw [← (Standard.isRepresentedBy_unipotentHom i ν J).2] at hx
  obtain ⟨h, hh⟩ := hl
  obtain ⟨x, hx⟩ := hx
  refine ⟨h, x, ?_⟩
  change map F (Standard.leviScheme i ν J) G (Standard.leviHom i ν J) h = l at hh
  change map F (Standard.unipotentScheme i ν J) G
    (Standard.unipotentHom i ν J) x = l⁻¹ * v * l at hx
  rw [hh, hx, ← hvl]
  group

/-- For an actual norm-one standard-parabolic minimum point, both the raw
Levi-unipotent factorization and its normalized tail minimum data are constructed. -/
theorem hasNormalizedStandardParabolicTailMinima_of_mem_range
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (s : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (j : (a : ℕ) → Fin (d a))
    (hline : ∀ a, ((ρ a).restrict (Standard.parabolicHom i ν (K a))).PreservesCoordinateLine
      (j a))
    (c : ℝ) (p : normOneSubgroup F G)
    (hp : (p : AdelicGroupPoints F G) ∈
      (map F (Standard.parabolicScheme i ν (K 0)) G
        (Standard.parabolicHom i ν (K 0))).toMonoidHom.range)
    (hmin : p ∈ chainHeightMinimalSet F G (s + 1) d ρ
      (fun a => Pi.single (j a) 1)
      (closedPrefixRationalSubgroup F G
        (fun a => Standard.parabolicScheme i ν (K a))
        (fun a => Standard.parabolicHom i ν (K a))) c) :
    HasNormalizedStandardParabolicTailMinima F G T i ν K s d ρ j c p := by
  obtain ⟨h, x, hfact⟩ := exists_standardLevi_mul_standardUnipotent_of_mem_range
    F G T i ν hG hi hν (K 0) (hK 0) p hp
  exact ⟨h, x, hfact, hasNormalizedStandardLeviTailMinima_of_factor F G T i ν
    hG hi hν K hK s d ρ j hline c h x p hfact hmin⟩

/-- The same compact subgroup satisfying minimal-parabolic Iwasawa coverage
satisfies coverage for every valid standard parabolic. -/
theorem isParabolicIwasawaCompact_standard_of_minimal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)
    (C : Subgroup (AdelicGroupPoints F G))
    (hC : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) C) :
    IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν J) (Standard.parabolicHom i ν J) C := by
  refine ⟨hC.1, Set.eq_univ_of_forall fun g => ?_⟩
  have hg : g ∈ Set.range (map F (Standard.parabolicScheme i ν ∅) G
      (Standard.parabolicHom i ν ∅)) * (C : Set (AdelicGroupPoints F G)) := by
    rw [hC.2]
    exact Set.mem_univ _
  obtain ⟨_, ⟨u, rfl⟩, k, hk, huk⟩ := hg
  let Q := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))
  have hu :
      map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅) u ∈
        (standardParabolic i ν ∅).carrier Q := by
    rw [← (Standard.isRepresentedBy_parabolicHom i ν ∅).2]
    exact ⟨u, rfl⟩
  have horder : standardParabolic i ν ∅ ≤ standardParabolic i ν J :=
    ((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J (Set.empty_subset _) hJ).1.mp
      (Set.empty_subset J)
  have huJ := horder Q hu
  rw [← (Standard.isRepresentedBy_parabolicHom i ν J).2] at huJ
  obtain ⟨v, hv⟩ := huJ
  change map F (Standard.parabolicScheme i ν J) G (Standard.parabolicHom i ν J) v =
    map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅) u at hv
  exact ⟨_, ⟨v, hv⟩, k, hk, huk⟩

set_option maxHeartbeats 800000 in
/-- With a supplied actual Iwasawa compact, every norm-one adelic point has a
right rational translate whose compact-left parabolic factor satisfies
uniformly controlled minima and has constructed normalized Levi tail data. -/
theorem exists_iwasawa_normalized_standardLevi_tail_minima
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (K : ℕ → Set (characterLattice T))
    (hK : ∀ a, K a ⊆ simpleRelativeRoots i ν)
    (s : ℕ) (d : ℕ → ℕ)
    (ρ : (a : ℕ) → MatrixRepresentation G (Fin (d a)))
    (j : (a : ℕ) → Fin (d a))
    (hline : ∀ a, ((ρ a).restrict (Standard.parabolicHom i ν (K a))).PreservesCoordinateLine
      (j a))
    (C : Subgroup (AdelicGroupPoints F G))
    (hC : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν (K 0)) (Standard.parabolicHom i ν (K 0)) C) :
    ∃ D : ℝ, 0 < D ∧ ∀ g : normOneSubgroup F G,
      ∃ (q : RationalGroupPoints F G) (k : AdelicGroupPoints F G), k ∈ C ∧
        ∃ p : normOneSubgroup F G,
          (g : AdelicGroupPoints F G) * rational F G q = k * p ∧
          p ∈ chainHeightMinimalSet F G (s + 1) d ρ
            (fun a => Pi.single (j a) 1)
            (closedPrefixRationalSubgroup F G
              (fun a => Standard.parabolicScheme i ν (K a))
              (fun a => Standard.parabolicHom i ν (K a))) D ∧
          HasNormalizedStandardParabolicTailMinima F G T i ν K s d ρ j D p := by
  let R := closedPrefixRationalSubgroup F G
    (fun a => Standard.parabolicScheme i ν (K a))
    (fun a => Standard.parabolicHom i ν (K a))
  have hv (a : ℕ) (_ : a < s + 1) : (Pi.single (j a) 1 : Fin (d a) → F) ≠ 0 := by
    intro hz
    have he := congrFun hz (j a)
    simp at he
  obtain ⟨D, hD, htransport⟩ := exists_pos_chainHeightMinimalSet_compact_transport
    F G (s + 1) d ρ (fun a _ => (Nat.zero_le (j a).val).trans_lt (j a).isLt) hC.1.1
  refine ⟨D, hD, ?_⟩
  intro g
  obtain ⟨q, hq⟩ := exists_mul_rational_mem_closedPrefix_minima F G
    (fun a => Standard.parabolicScheme i ν (K a))
    (fun a => Standard.parabolicHom i ν (K a)) d j ρ (by
      intro a A y hy
      obtain ⟨w, hw⟩ := hy
      change w ≫ (Standard.parabolicHom i ν (K a)).hom.hom = y at hw
      apply ((ρ a).affine_coordinateLine_scalar_iff A y (j a)).mp
      simpa only [MatrixRepresentation.pointMatrix_restrict, hw] using hline a _ w)
    (s + 1) g
  let y : normOneSubgroup F G := g * rationalNormOne F G q
  have hymin : y ∈ chainHeightMinimalSet F G (s + 1) d ρ
      (fun a => Pi.single (j a) 1) R 1 := hq
  have hyinv : (y : AdelicGroupPoints F G)⁻¹ ∈
      Set.range (map F (Standard.parabolicScheme i ν (K 0)) G
        (Standard.parabolicHom i ν (K 0))) * (C : Set (AdelicGroupPoints F G)) := by
    rw [hC.2]
    exact Set.mem_univ _
  obtain ⟨_, ⟨u, rfl⟩, k, hk, hku⟩ := hyinv
  have hprod :
      k⁻¹ * map F (Standard.parabolicScheme i ν (K 0)) G
        (Standard.parabolicHom i ν (K 0)) u⁻¹ = (y : AdelicGroupPoints F G) := by
    simpa only [mul_inv_rev, map_inv, inv_inv] using
      congrArg (fun w : AdelicGroupPoints F G => w⁻¹) hku
  have hpone : map F (Standard.parabolicScheme i ν (K 0)) G
      (Standard.parabolicHom i ν (K 0)) u⁻¹ ∈ normOneSubgroup F G := by
    have he :
        map F (Standard.parabolicScheme i ν (K 0)) G
          (Standard.parabolicHom i ν (K 0)) u⁻¹ = k * (y : AdelicGroupPoints F G) := by
      rw [← hprod]
      group
    rw [he]
    exact (normOneSubgroup F G).mul_mem
      (compactSubgroup_le_normOneSubgroup F G C hC.1.1 hk) y.property
  let p : normOneSubgroup F G :=
    ⟨map F (Standard.parabolicScheme i ν (K 0)) G
      (Standard.parabolicHom i ν (K 0)) u⁻¹, hpone⟩
  let k' : normOneSubgroup F G :=
    ⟨k⁻¹, compactSubgroup_le_normOneSubgroup F G C hC.1.1 (C.inv_mem hk)⟩
  have hk'p : k' * p = y := Subtype.ext hprod
  have hpmin : p ∈ chainHeightMinimalSet F G (s + 1) d ρ
      (fun a => Pi.single (j a) 1) R D := by
    have h := (htransport (fun a => Pi.single (j a) 1) hv R k' (C.inv_mem hk)
      p 1 zero_le_one).2 (hk'p.symm ▸ hymin)
    simpa only [mul_one] using h
  refine ⟨q, k⁻¹, C.inv_mem hk, p, hprod.symm, hpmin, ?_⟩
  exact hasNormalizedStandardParabolicTailMinima_of_mem_range F G T i ν
    hG hi hν K hK s d ρ j hline D p ⟨u⁻¹, rfl⟩ hpmin

end Langlands.Global.RepresentationGrowth
