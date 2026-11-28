import Langlands.Global.AdelicCharacteristicHeightProduct
import Langlands.Global.AdelicMinimalParabolicNormCoordinatesProof
import Langlands.Global.AdelicParabolicPeriodVanishing
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality

/-! # Characteristic height sets in the rational parabolic quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set Topology
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints AdelicSiegelFactors
  ArthurTruncation ArthurParabolicSpaces

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)

local notation "T" => fam.T
local notation "P₀" => Standard.parabolicScheme fam.i fam.ν ∅
local notation "N₀" => Standard.unipotentScheme fam.i fam.ν ∅
local notation "M₀" => Standard.leviScheme fam.i fam.ν ∅
local notation "p₀" => Standard.parabolicHom fam.i fam.ν ∅
local notation "u₀" => Standard.unipotentHom fam.i fam.ν ∅
local notation "Nmap" => map F N₀ G u₀
local notation "Lmap" => map F M₀ G (Standard.leviHom fam.i fam.ν ∅)
local notation "H₀" => fam.minimalHeight hK
local notation "hcan" => fam.isIwasawaCompact_standardBot hK
local notation "hres" => fam.bijective_restrictToTorus_bot
local notation "G₁" => normOneSubgroup F G

/-- The ambient minimal Iwasawa height is right invariant under its compact. -/
theorem minimalHeight_mul_right (g : AdelicGroupPoints F G) {k : AdelicGroupPoints F G}
    (hk : k ∈ K) : H₀ (g * k) = H₀ g := by
  simp only [minimalHeight, height, IsIwasawaCompact.height_mul_right _ _ hk]

/-- Left multiplication by a minimal-parabolic point adds its minimal height. -/
theorem minimalHeight_map_mul (q : AdelicGroupPoints F P₀) (g : AdelicGroupPoints F G) :
    H₀ (map F P₀ G p₀ q * g) = H₀ (map F P₀ G p₀ q) + H₀ g := by
  let hT := fam.maximalSplit.isSplitSubtorus.1
  apply (isPerfPair_of_isSplitTorus hT).bijective_right.injective
  apply LinearMap.ext
  intro χ
  obtain ⟨a, rfl⟩ := (hres).surjective χ
  change pair T (restrictToTorus F fam.i fam.ν ∅ a)
      (toA0 hT hres ((hcan).height (map F P₀ G p₀ q * g))) =
    pair T (restrictToTorus F fam.i fam.ν ∅ a)
      (toA0 hT hres ((hcan).height (map F P₀ G p₀ q)) + toA0 hT hres ((hcan).height g))
  rw [map_add, pair_toA0, pair_toA0, pair_toA0, (hcan).height_map_mul,
    (hcan).height_map, map_add]

/-- The ambient minimal Iwasawa height is left invariant under the minimal radical. -/
theorem minimalHeight_minimalRadical_mul (n : AdelicGroupPoints F N₀) (g : AdelicGroupPoints F G) :
    H₀ (Nmap n * g) = H₀ g := by
  have hN := RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T fam.i fam.ν
    fam.connectedReductive fam.maximalSplit fam.generic ∅ (Set.empty_subset _)
  simp only [minimalHeight, height, ← Standard.unipotentToParabolic_comp,
    map_comp_apply_of_hom, (hcan).height_map_mul, characterLog_map,
    characterLog_eq_zero_of_isUnipotent hN, map_zero, zero_add]

include hK in
private theorem exists_minimalFactors (x : G₁) :
    ∃ n : AdelicGroupPoints F N₀, ∃ m : AdelicGroupPoints F M₀,
      Lmap m ∈ G₁ ∧ ∃ k ∈ K, Nmap n * Lmap m * k = x.val := by
  obtain ⟨A, j, hSetup⟩ := exists_siegelAlgebraicSetup_of_generic F fam.i fam.ν
    fam.connectedReductive fam.maximalSplit fam.generic
  obtain ⟨q, k, hk, hx⟩ := (hcan).exists_eq x.val
  let g := map F P₀ G p₀ q
  have hg : g = x.val * k⁻¹ := by rw [← hx, mul_inv_cancel_right]
  have hg₁ : g ∈ G₁ := by
    rw [hg]
    exact (G₁).mul_mem x.property ((G₁).inv_mem
      (compactSubgroup_le_normOneSubgroup F G K hK.isCompact hk))
  obtain ⟨n, m, a, hnm⟩ := (minimalParabolicNormCoordinates F G fam.connectedReductive T fam.i
    fam.ν A j hSetup).exists_factors F G T fam.i fam.ν A j ⟨g, hg₁⟩ ⟨q, rfl⟩
  let y := Lmap m.val * positiveMap F G T fam.i A j a
  have hn : Nmap n * y = g := by
    rw [← mul_assoc]
    exact hnm
  have hy : y ∈ standardLeviImage F G T fam.i fam.ν :=
    (standardLeviImage F G T fam.i fam.ν).mul_mem ⟨m.val, rfl⟩
      (positiveMap_mem_standardLeviImage F G T fam.i fam.ν A j a)
  have hy₁ : y ∈ G₁ := (G₁).mul_mem (mapNormOne F M₀ G (Standard.leviHom fam.i fam.ν ∅) m).property
    (hSetup.positiveMap_mem_normOne F G T fam.i fam.ν A j a)
  obtain ⟨m', hm'⟩ := hy
  change Lmap m' = y at hm'
  refine ⟨n, m', hm' ▸ hy₁, k, hk, ?_⟩
  rw [hm', hn]
  exact hx

variable (J : StandardIndex F G fam.i fam.ν)

local notation "ΓJ" => parabolicRationalNormOneSubgroup (F := F) (fam.p J)

private theorem rational_minimalRadical_mem (n : RationalGroupPoints F N₀) :
    mapNormOne F N₀ G u₀ (rationalNormOne F N₀ n) ∈ ΓJ := by
  have hle : SubgroupFunctor.range u₀ ≤ SubgroupFunctor.range (fam.p J) := by
    rw [(Standard.isRepresentedBy_unipotentHom fam.i fam.ν ∅).2]
    have hb : standardUnipotent fam.i fam.ν ∅ ≤ SubgroupFunctor.range (fam.p fam.bot) := by
      rw [(fam.isCompatible fam.bot).parabolic_eq]
      exact standardUnipotent_le_standardParabolic fam.i fam.ν ∅
    exact hb.trans ((fam.le_iff_range_le fam.bot J).mp (Set.empty_subset _))
  let : IsClosedImmersion (fam.p J).hom.hom.left := fam.isClosedImmersion_p J
  let j := SubgroupFunctor.rangeFactor u₀ (fam.p J) hle
  have hj : j ≫ fam.p J = u₀ := SubgroupFunctor.rangeFactor_comp _ _ _
  let r : RationalGroupPoints F (fam.P J) := (N₀).affinePointsTarget j _ n
  refine ⟨rationalNormOne F (fam.P J) r, ⟨r, rfl⟩, Subtype.ext ?_⟩
  change map F (fam.P J) G (fam.p J) (rational F (fam.P J) r) = Nmap (rational F N₀ n)
  rw [← map_rational j n, ← map_comp_apply_of_hom, hj]

/-- In the rational quotient of any standard parabolic, the characteristic set with arbitrary
minimal-height restriction has the same image as the full set with that height restriction. -/
def CharacteristicHeightLiftStatement (C : CompactFactors F G N₀ M₀) : Prop :=
  IsRationalCovering C → ∀ W : Set (V T),
    LeftCosetSpace.mk ΓJ '' (Subtype.val ⁻¹' characteristicHeightProduct fam.maximalSplit hcan hres C W) =
      LeftCosetSpace.mk ΓJ '' {x : G₁ | H₀ x.val ∈ W}

set_option maxHeartbeats 1200000 in
/-- Decompose a norm-one point by the minimal Iwasawa formula, then fold its minimal radical
into the given compact set using a rational point of the same standard parabolic. -/
theorem characteristicHeightLift (C : CompactFactors F G N₀ M₀) :
    fam.CharacteristicHeightLiftStatement hK J C := by
  intro hcov W
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨_, ⟨_, ⟨n, _, rfl⟩, m, ⟨_, _, _, hm⟩, rfl⟩, k, hk, hprod⟩ := hx
    refine ⟨x, ?_, rfl⟩
    change H₀ x.val ∈ W
    rw [← hprod, fam.minimalHeight_mul_right hK _ hk, fam.minimalHeight_minimalRadical_mul hK]
    exact hm
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨n, m, hm₁, k, hk, he⟩ := fam.exists_minimalFactors hK x
    have hm : H₀ (Lmap m) ∈ W := by
      change H₀ x.val ∈ W at hx
      rwa [← he, fam.minimalHeight_mul_right hK _ hk, fam.minimalHeight_minimalRadical_mul hK] at hx
    obtain ⟨_, ⟨r, rfl⟩, n₀, hn₀, hn⟩ := hcov.1 n
    let d : G₁ := mapNormOne F N₀ G u₀ (rationalNormOne F N₀ r)
    let y := d⁻¹ * x
    have hy : y.val = Nmap n₀ * Lmap m * k := by
      change (Nmap (rational F N₀ r))⁻¹ * x.val = _
      rw [← he, hn, map_mul]
      group
    refine ⟨y, ?_, ?_⟩
    · change y.val ∈ characteristicHeightProduct fam.maximalSplit hcan hres C W
      exact ⟨_, ⟨Nmap n₀, ⟨n₀, hn₀, rfl⟩, Lmap m, ⟨m, rfl, hm₁, hm⟩, rfl⟩, k, hk, hy.symm⟩
    · exact LeftCosetSpace.mk_subgroup_mul ΓJ
        ⟨d⁻¹, (ΓJ).inv_mem (fam.rational_minimalRadical_mem J r)⟩ x

end Langlands.Global.StandardParabolicFamily
