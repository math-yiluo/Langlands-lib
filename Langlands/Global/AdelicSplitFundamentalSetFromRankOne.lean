import Langlands.Global.AdelicSplitChamberReduction
import Langlands.Global.AdelicSplitFundamentalSet
import Langlands.Global.AdelicIwasawaReduction
import Langlands.Global.InfinitePlaceIwasawaProof
import Langlands.Global.IntegralIwasawaFamilyProof

/-! # Springer's split fundamental set from the split rank-one height bound -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- A weak chamber reduction with a compact subgroup `K` gives Springer's right
fundamental set. Apply the reduction to `g⁻¹` and invert: the compact factor is
`K`, the torus factor is the inverse of the positive point, the simple-root bound is
the inverse of the chamber threshold, and the minimal-parabolic factor is the
inverted Levi--unipotent product. -/
theorem HasWeakChamberReduction.hasRightAdelicFundamentalSet
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G)))
    (h : HasWeakChamberReduction F G T i ν T₀ j K) :
    HasRightAdelicFundamentalSet F G T i ν := by
  obtain ⟨t, ht⟩ := h
  have hKone := compactSubgroup_le_normOneSubgroup F G K hK
  refine ⟨{x | (x : AdelicGroupPoints F G) ∈ K}, ?_, t⁻¹, fun g => ?_⟩
  · rw [Subtype.isCompact_iff]
    convert hK using 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hKone hy⟩, hy, rfl⟩
  obtain ⟨q, n, m, a, ha, k, hk, heq⟩ := ht g⁻¹
  let s : AdelicGroupPoints F T.toGrp :=
    (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) (a : AdelicGroupPoints F T₀.toGrp))⁻¹
  have hs : map F T.toGrp G i s = (positiveMap F G T i T₀ j a)⁻¹ := by
    simp only [s, map_inv]
    congr 1
  have hlevi : map F _ _ (Standard.leviToParabolic i ν ∅)
      ((m : AdelicGroupPoints F _)⁻¹) ∈ normOneSubgroup F (Standard.parabolicScheme i ν ∅) :=
    map_normOneSubgroup_le F _ _ (Standard.leviToParabolic i ν ∅)
      ⟨_, (normOneSubgroup F _).inv_mem m.property, rfl⟩
  have hunip : map F _ _ (Standard.unipotentToParabolic i ν ∅) n⁻¹ ∈
      normOneSubgroup F (Standard.parabolicScheme i ν ∅) :=
    range_le_normOne_of_charactersTrivialAlong F _ _ (Standard.unipotentToParabolic i ν ∅)
      (charactersTrivialAlong_of_isUnipotent F _ _ _
        (hS.isUnipotent_standard F G T i ν T₀ j)) ⟨n⁻¹, rfl⟩
  let p : normOneSubgroup F (Standard.parabolicScheme i ν ∅) :=
    ⟨_, (normOneSubgroup F _).mul_mem hlevi hunip⟩
  have hp : map F _ G (Standard.parabolicHom i ν ∅) p =
      (map F _ G (Standard.leviHom i ν ∅) m)⁻¹ *
        (map F _ G (Standard.unipotentHom i ν ∅) n)⁻¹ := by
    change map F _ G (Standard.parabolicHom i ν ∅)
        (map F _ _ (Standard.leviToParabolic i ν ∅) ((m : AdelicGroupPoints F _)⁻¹) *
          map F _ _ (Standard.unipotentToParabolic i ν ∅) n⁻¹) = _
    rw [map_mul, ← adelicPointsMap_comp_apply, ← adelicPointsMap_comp_apply,
      Standard.leviToParabolic_comp, Standard.unipotentToParabolic_comp, map_inv, map_inv]
  refine ⟨q, s, p, ?_, ?_, ⟨k⁻¹, hKone (K.inv_mem hk)⟩, K.inv_mem hk, ?_⟩
  · rw [hs]
    exact (normOneSubgroup F G).inv_mem (hS.positiveMap_mem_normOne F G T i ν T₀ j a)
  · intro α hα
    have h := ha α hα
    rw [PositiveRealTorus.normCharacter_pullback] at h
    simp only [s, map_inv]
    exact inv_le_inv' h
  · rw [hs, hp]
    have hinv := congrArg (fun z : AdelicGroupPoints F G => z⁻¹) heq
    simp only [mul_inv_rev, Subgroup.coe_inv, inv_inv] at hinv
    change k⁻¹ * (positiveMap F G T i T₀ j a)⁻¹ *
      ((map F _ G (Standard.leviHom i ν ∅) m)⁻¹ *
        (map F _ G (Standard.unipotentHom i ν ∅) n)⁻¹) * rational F G q = g
    calc k⁻¹ * (positiveMap F G T i T₀ j a)⁻¹ *
          ((map F _ G (Standard.leviHom i ν ∅) m)⁻¹ *
            (map F _ G (Standard.unipotentHom i ν ∅) n)⁻¹) * rational F G q
        = (map F _ G (Standard.unipotentHom i ν ∅) n *
            map F _ G (Standard.leviHom i ν ∅) m *
            positiveMap F G T i T₀ j a * k)⁻¹ * rational F G q := by group
      _ = g := by rw [heq, Subgroup.coe_inv]; group

/-- **Split fundamental sets from the split rank-one bound and adelic Iwasawa.**
The split rank-one height bound and adelic parabolic Iwasawa existence give
Springer's split fundamental-set theorem. -/
theorem splitAdelicFundamentalSet_of_splitRankOne_of_iwasawa
    (hsplit : SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hiw : AdelicGroupPoints.ParabolicIwasawaStatement.{u}) :
    SplitAdelicFundamentalSetStatement.{u} := by
  intro F _ _ G _ _ hG T i ν T₀ j hS hT
  obtain ⟨K, hK⟩ := hiw F G hG _ (Standard.parabolicHom i ν ∅) hS.2.2.1.1
  exact (hasWeakChamberReduction_of_splitRankOne_height F G T i ν T₀ j hsplit hG hS hT
    K hK).hasRightAdelicFundamentalSet F G T i ν T₀ j hS K hK.1.1

/-- The same conclusion with the only unproved Iwasawa input isolated: finite-place
parabolic Iwasawa existence. The archimedean and integral inputs are the published
theorems. -/
theorem splitAdelicFundamentalSet_of_splitRankOne_of_finitePlaceIwasawa
    (hsplit : SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hfinite : FinitePlaceGroupPoints.ParabolicIwasawaStatement.{u}) :
    SplitAdelicFundamentalSetStatement.{u} :=
  splitAdelicFundamentalSet_of_splitRankOne_of_iwasawa hsplit
    (parabolicIwasawaStatement_of_archimedean_finite_integral
      InfinitePlaceGroupPoints.parabolicIwasawaStatement hfinite
      IntegralIwasawaFamily.existenceStatement)

end Langlands.Global.AdelicSiegelFactors
