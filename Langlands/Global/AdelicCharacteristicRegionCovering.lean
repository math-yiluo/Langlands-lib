import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.ArthurSiegelCoveringProof
import Langlands.Global.ArthurSiegelPartitionProof
import Langlands.Representation.Exponents.MaximalLeviExponentTransport

/-! # Exhaustive characteristic truncation data on the norm-one quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical Pointwise

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  AdelicGroupPoints ArthurParabolicSpaces AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "Γ" => rationalNormOneSubgroup F G
local notation "M₀" => Standard.leviScheme i ν ∅
local notation "N₀" => Standard.unipotentScheme i ν ∅
local notation "Gₐ" => AdelicGroupPoints F G
local notation "H₀" => height hi hK hρ
local notation "nMap" => map F N₀ G (Standard.unipotentHom i ν ∅)
local notation "mMap" => map F M₀ G (Standard.leviHom i ν ∅)

omit [LocallyOfFiniteType G.X.hom] in
include hG in
/-- The minimal Iwasawa height of a norm-one point lies in the relative coroot space. -/
theorem height_mem_realCorootSpan_of_normOne {x : Gₐ} (hx : x ∈ normOneSubgroup F G) :
    H₀ x ∈ D.realCorootSpan := by
  let p := Standard.parabolicHom i ν ∅
  obtain ⟨q, k, hk, rfl⟩ := hK.exists_eq x
  have hkN := compactSubgroup_le_normOneSubgroup F G K hK.isCompact hk
  have hq : map F _ G p q ∈ normOneSubgroup F G := by
    rw [show map F _ G p q = (map F _ G p q * k) * k⁻¹ by group]
    exact (normOneSubgroup F G).mul_mem hx ((normOneSubgroup F G).inv_mem hkN)
  obtain ⟨B, hB⟩ := ArthurRelative.exists_isWeylInvariantInnerProduct hG hi
  rw [D.realCorootSpan_eq_annihilator hi.isSplitSubtorus.1
    (ArthurRelative.isCompl_relativeRootSpanReal hG hi) B hB, mem_cocharacterAnnihilator]
  rintro _ ⟨m, rfl⟩
  have hr : restrictToTorus F i ν ∅ (rationalCharacterRestrictReal p m) = rationalCharacterRestrictReal i m := by
    rw [restrictToTorus, rationalCharacterRestrictReal_comp_apply, torusToParabolic_comp]
  rw [← hr, height, hK.height_mul_right _ hk, pair_toA0, hK.height_map,
    ← realParameterPairing_realCharacterDualMap p, ← characterLog_map,
    (characterLog_eq_zero_iff F G _).mpr hq, map_zero]

/-- For any compact Iwasawa subgroup there are compact factors satisfying the
rational coverings (7.1) and a fixed lower parameter with exhaustive characteristic regions. -/
def CharacteristicRegionCoveringStatement : Prop :=
  IsGenericCocharacter i ν →
  ∃ (C : CompactFactors F G N₀ M₀) (T₀ : V T),
    C.compactSubgroup = K ∧ IsRationalCovering C ∧
    ∀ q : NormOneRationalQuotient F G, ∃ Tp, q ∈ characteristicRegion hG hi D hK hρ C T₀ Tp

/-- The usual Siegel covering gives representatives with the required lower
height bounds. Use their heights as the upper truncation vectors. -/
theorem characteristicRegion_covering : CharacteristicRegionCoveringStatement hG hi D hK hρ := by
  intro hν
  obtain ⟨C, T₀, hC, hcover⟩ := iwasawaSiegelCovering F G T i ν hG hi hν K hK hρ
  obtain ⟨T₁, j, hS⟩ := exists_siegelAlgebraicSetup_of_generic F i ν hG hi hν
  obtain ⟨ΩN, hΩN, hcN⟩ := exists_unipotentCompactCover_of_setup hS
  obtain ⟨ΩM, hΩM, hcM⟩ := exists_leviCompactCover_of_setup centralSplitCompactQuotient hS
  let C' : CompactFactors F G N₀ M₀ :=
    ⟨C.omegaN ∪ ΩN, C.omegaM ∪ ΩM, C.compact_omegaN.union hΩN, C.compact_omegaM.union hΩM, K, hK.isCompact⟩
  refine ⟨C', T₀, rfl, ⟨?_, ?_⟩, ?_⟩
  · intro n
    obtain ⟨r, hr, hn⟩ := hcN n
    exact ⟨r⁻¹, (rationalSubgroup F N₀).inv_mem hr, r * n, Or.inr hn, (inv_mul_cancel_left r n).symm⟩
  · intro m
    obtain ⟨r, hr⟩ := hcM m
    refine ⟨r⁻¹, rationalNormOne F M₀ r * m, Or.inr hr, ?_⟩
    rw [Subgroup.coe_mul, rationalNormOne_val, map_inv, inv_mul_cancel_left]
  intro q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  let SP := simpleFinset ν hG hi
  have hx : x.val ∈ (parabolicRationalImage (Standard.parabolicHom i ν (SP : Set (characterLattice T))) :
      Set Gₐ) * siegelSet hi hK hρ C SP T₀ := by
    rw [hcover SP (Finset.mem_powerset.mpr (Finset.Subset.refl _))]
    exact Set.mem_univ _
  obtain ⟨_, ⟨r, _, rfl⟩, y, hy, hxy⟩ := Set.mem_mul.mp hx
  change r.val * y = x.val at hxy
  have hyN : y ∈ normOneSubgroup F G := by
    rw [show y = r.val⁻¹ * x.val by rw [← hxy, inv_mul_cancel_left]]
    exact (normOneSubgroup F G).mul_mem
      ((normOneSubgroup F G).inv_mem (rationalSubgroup_le_normOneSubgroup F G r.2)) x.2
  let y₁ : normOneSubgroup F G := ⟨y, hyN⟩
  obtain ⟨n, hn, m, hm, a, ha, k, hk, hprod⟩ :=
    (mem_siegelSet_iff hi hK hρ C SP T₀ y).mp hy
  let z := mMap m.val * positiveTorusMap F i a
  have hzg : nMap n * z * k = y := by
    rw [show nMap n * z = nMap n * mMap m.val * positiveTorusMap F i a by simp only [z, mul_assoc]]
    exact hprod
  have hnN : nMap n ∈ normOneSubgroup F G := by
    have hN := RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T i ν hG hi hν ∅
      (Set.empty_subset _)
    rw [← characterLog_eq_zero_iff, characterLog_map, characterLog_eq_zero_of_isUnipotent hN, map_zero]
  have hkK : k ∈ K := hC ▸ hk
  have hkN := compactSubgroup_le_normOneSubgroup F G K hK.isCompact hkK
  have hzN : z ∈ normOneSubgroup F G := by
    rw [show z = (nMap n)⁻¹ * y * k⁻¹ by rw [← hzg]; group]
    exact (normOneSubgroup F G).mul_mem
      ((normOneSubgroup F G).mul_mem ((normOneSubgroup F G).inv_mem hnN) hyN)
      ((normOneSubgroup F G).inv_mem hkN)
  have hzH : H₀ z = H₀ (positiveTorusMap F i a) := by
    simpa only [z, map_one, one_mul, mul_one] using
      height_siegel_product hG hi hν hK hρ (1 : AdelicGroupPoints F N₀) m a K.one_mem
  have hch : H₀ z ∈ characteristicChamber ν hG hi D T₀ (H₀ z) := by
    refine ⟨height_mem_realCorootSpan_of_normOne hG hi D hK hρ hzN, fun α hα => ⟨?_, ?_⟩⟩
    · rw [hzH]
      exact (ha α hα).le
    · rw [sub_self, map_zero]
  have hlevi : z ∈ leviHeightSet hi hK hρ (characteristicChamber ν hG hi D T₀ (H₀ z)) := by
    let aM := map F T.toGrp M₀ (torusToStandardLevi F G T i ν) a.val
    refine ⟨m.val * aM, ?_, hzN, hch⟩
    rw [map_mul]
    congr 1
    rw [positiveTorusMap_apply, ← map_comp_apply_of_hom, torusToStandardLevi_comp]
  refine ⟨H₀ z, y₁, ?_, ?_⟩
  · change y ∈ characteristicProduct hG hi D hK hρ C' T₀ (H₀ z)
    rw [characteristicProduct, Set.mem_mul]
    exact ⟨nMap n * z, Set.mem_mul.mpr ⟨nMap n, ⟨n, Or.inl hn, rfl⟩, z, hlevi, rfl⟩, k, hkK, hzg⟩
  · obtain ⟨r₀, hr₀⟩ := r.2
    have hxy' : rationalNormOne F G r₀ * y₁ = x := Subtype.ext (by
      change rational F G r₀ * y = x.val
      rwa [hr₀])
    rw [← hxy', LeftCosetSpace.mk_subgroup_mul Γ ⟨_, ⟨_, rfl⟩⟩ y₁]

end Langlands.Global.ArthurTruncation
