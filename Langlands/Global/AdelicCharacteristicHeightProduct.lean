import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.ArthurSiegelPartitionProof
import Langlands.Global.ArthurSiegelCoveringProof
import Langlands.Global.AdelicMinimalParabolicNormCoordinatesProof

/-! # Minimal-Levi products and characteristic Siegel representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj Pointwise TensorProduct

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  ArthurParabolicSpaces AdelicGroupPoints AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "Gₐ" => AdelicGroupPoints F G
local notation "N₀" => Standard.unipotentScheme i ν ∅
local notation "M₀" => Standard.leviScheme i ν ∅
local notation "nMap" => map F N₀ G (Standard.unipotentHom i ν ∅)
local notation "mMap" => map F M₀ G (Standard.leviHom i ν ∅)
local notation "H₀" => height hi hK hρ

/-- The characteristic product with the height constrained to a set `A`.
The minimal Levi factor is taken over all of `M₀(A)` as in Delorme's §7. -/
def characteristicHeightProduct (C : CompactFactors F G N₀ M₀) (A : Set (V T)) : Set Gₐ :=
  (nMap '' C.omegaN) * leviHeightSet hi hK hρ A * (K : Set Gₐ)

omit [Mono i.hom.hom.left] in
include hG hi hν in
private theorem exists_minimalLevi_normOne_torus (m : AdelicGroupPoints F M₀) :
    ∃ (b : normOneSubgroup F M₀) (a : PositiveRealTorus.intrinsicSubgroup F T),
      mMap m = mMap b.val * positiveTorusMap F i a := by
  obtain ⟨T₁, j, hS⟩ := exists_siegelAlgebraicSetup_of_generic F i ν hG hi hν
  obtain ⟨_, _, _, hRL, _, hlevi, _⟩ := hS
  let t := torusToStandardLevi F G T i ν
  have hMc := Standard.isClosedSubgroup_leviHom i ν ∅
  let : IsAffineHom (M₀).X.hom := hMc.isAffineHom
  have hmax : IsMaximalSplitTorus t := hi.isMaximalSplitTorus_standardLeviTorusFactor i ν ∅
    (Standard.isRepresentedBy_leviHom i ν ∅) hMc
  have hcent : IsCentral t := by
    apply isCentral_of_range_le_torusCentralizer (Standard.isRepresentedBy_leviHom i ν ∅).1
    rw [torusToStandardLevi_comp, (Standard.isRepresentedBy_leviHom i ν ∅).2, hlevi]
  have hsplit : IsSplitComponent t := ⟨⟨hmax.1, hcent⟩, fun S s hs y hy => hmax.2 S s hs.1 y hy⟩
  let e := PositiveRealTorus.splitComponentNormOneDecomposition centralSplitTorusCharacter F M₀
    hRL.isConnectedReductive T t hsplit
  obtain ⟨⟨a, b⟩, he⟩ := e.surjective m
  refine ⟨b, a, ?_⟩
  rw [← he, PositiveRealTorus.splitComponentNormOneDecomposition_apply,
    (PositiveRealTorus.positivePointMap_commute F M₀ T t hcent a b.val).eq, map_mul]
  congr 1
  rw [PositiveRealTorus.positivePointMap_apply, positiveTorusMap_apply,
    ← map_comp_apply_of_hom, torusToStandardLevi_comp]

include hG hi hν in
/-- A minimal-parabolic rational translate of a point of the characteristic product lies in the
common Siegel set with the same height constraint. -/
theorem exists_siegelRepresentative_of_mem_characteristicHeightProduct
    (C : CompactFactors F G N₀ M₀) (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C)
    {A : Set (V T)} {T₁ : V T}
    (hcut : ∀ X ∈ A, ∀ α ∈ simpleRelativeRoots i ν, 0 < eval T α (X - T₁))
    {x : Gₐ} (hx : x ∈ characteristicHeightProduct hi hK hρ C A) :
    ∃ δ ∈ parabolicRationalImage (Standard.parabolicHom i ν ∅),
      δ * x ∈ siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁ ∧ H₀ (δ * x) ∈ A := by
  classical
  obtain ⟨_, ⟨_, ⟨n, -, rfl⟩, _, ⟨m, rfl, _, hmH⟩, rfl⟩, k, hk, hprod⟩ := hx
  obtain ⟨b, a, hma⟩ := exists_minimalLevi_normOne_torus hG hi hν m
  have ha : H₀ (positiveTorusMap F i a) ∈ A := by
    have he := height_siegel_product hG hi hν hK hρ (1 : AdelicGroupPoints F N₀) b a K.one_mem
    simp only [map_one, one_mul, mul_one] at he
    rwa [hma, he] at hmH
  obtain ⟨r, ωm, hωm, hb⟩ := hcov.2 b
  let rG := (M₀).affinePointsTarget (Standard.leviHom i ν ∅) (CommAlgCat.of F F) r
  let rA := rational F G rG
  have hr : mMap (rational F M₀ r) = rA :=
    (DFunLike.congr_fun (rational_naturality F M₀ (Standard.leviHom i ν ∅)) r).symm
  have hnorm : rA⁻¹ ∈ standardParabolicImage F G T i ν :=
    (standardParabolicImage F G T i ν).inv_mem
      (standardLeviImage_le_parabolic F G T i ν ⟨rational F M₀ r, hr⟩)
  obtain ⟨n', hn'⟩ := (Subgroup.mem_normalizer_iff.mp
    (standardParabolicImage_le_normalizer F G T i ν hnorm) (nMap n)).mp
      (show nMap n ∈ standardUnipotentImage F G T i ν from ⟨n, rfl⟩)
  change nMap n' = rA⁻¹ * nMap n * rA⁻¹⁻¹ at hn'
  obtain ⟨_, ⟨s, rfl⟩, ωn, hωn, hn⟩ := hcov.1 n'
  let sG := (N₀).affinePointsTarget (Standard.unipotentHom i ν ∅) (CommAlgCat.of F F) s
  have hs : nMap (rational F N₀ s) = rational F G sG :=
    (DFunLike.congr_fun (rational_naturality F N₀ (Standard.unipotentHom i ν ∅)) s).symm
  have hrP : rG ∈ (SubgroupFunctor.range (Standard.parabolicHom i ν ∅)).carrier
      ((algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F F))) := by
    rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2]
    apply standardLevi_le_standardParabolic i ν ∅
    rw [← (Standard.isRepresentedBy_leviHom i ν ∅).2]
    exact ⟨r, rfl⟩
  have hsP : sG ∈ (SubgroupFunctor.range (Standard.parabolicHom i ν ∅)).carrier
      ((algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F F))) := by
    rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2]
    apply standardUnipotent_le_standardParabolic i ν ∅
    rw [← (Standard.isRepresentedBy_unipotentHom i ν ∅).2]
    exact ⟨s, rfl⟩
  let y := nMap ωn * mMap ωm.val * positiveTorusMap F i a * k
  have hxy : rational F G (rG * sG) * y = x := by
    rw [← hprod, hma, hb, map_mul mMap, hr, map_mul, ← hs]
    have hnAux : nMap (rational F N₀ s) * nMap ωn = rA⁻¹ * nMap n * rA := by
      rw [← map_mul, ← hn, hn', inv_inv]
    rw [show rA * nMap (rational F N₀ s) * y =
      rA * (nMap (rational F N₀ s) * nMap ωn) * mMap ωm.val * positiveTorusMap F i a * k by
        dsimp only [y]; group, hnAux]
    group
  refine ⟨(rational F G (rG * sG))⁻¹,
    (parabolicRationalImage _).inv_mem (rational_mem_parabolicRationalImage (Subgroup.mul_mem _ hrP hsP)),
    ?_⟩
  rw [← hxy, inv_mul_cancel_left]
  refine ⟨(mem_siegelSet_iff hi hK hρ C _ _ _).mpr
    ⟨ωn, hωn, ωm, hωm, a, fun α hα => hcut _ ha α ((mem_simpleFinset hG hi).mp hα),
      k, hC.symm ▸ hk, rfl⟩, ?_⟩
  dsimp only [y]
  rw [height_siegel_product hG hi hν hK hρ ωn ωm a hk]
  exact ha

omit [LocallyOfFiniteType G.X.hom] in
include hG hi hν in
/-- A norm-one point in Siegel coordinates with height in `A` belongs to the characteristic
product with the same constraint. -/
theorem mem_characteristicHeightProduct_of_siegelRepresentative
    (C : CompactFactors F G N₀ M₀) (hC : C.compactSubgroup = K)
    {A : Set (V T)} {T₁ : V T} {x : Gₐ}
    (hx : x ∈ siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁)
    (hx₁ : x ∈ normOneSubgroup F G) (hxH : H₀ x ∈ A) :
    x ∈ characteristicHeightProduct hi hK hρ C A := by
  obtain ⟨n, hn, b, _, a, _, k, hk, hprod⟩ := (mem_siegelSet_iff hi hK hρ C _ _ _).mp hx
  have hk' : k ∈ K := hC ▸ hk
  have hn₁ : nMap n ∈ normOneSubgroup F G := by
    have hN := RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T i ν hG hi hν ∅
      (Set.empty_subset _)
    rw [← characterLog_eq_zero_iff, characterLog_map, characterLog_eq_zero_of_isUnipotent hN, map_zero]
  have hk₁ : k ∈ normOneSubgroup F G := compactSubgroup_le_normOneSubgroup F G K hK.isCompact hk'
  let aM := map F T.toGrp M₀ (torusToStandardLevi F G T i ν) a.val
  have haM : mMap aM = positiveTorusMap F i a := by
    rw [positiveTorusMap_apply, ← map_comp_apply_of_hom, torusToStandardLevi_comp]
  let z := mMap b.val * positiveTorusMap F i a
  have hz₁ : z ∈ normOneSubgroup F G := by
    have he : z = (nMap n)⁻¹ * x * k⁻¹ := by rw [← hprod]; dsimp only [z]; group
    rw [he]
    exact (normOneSubgroup F G).mul_mem
      ((normOneSubgroup F G).mul_mem ((normOneSubgroup F G).inv_mem hn₁) hx₁)
      ((normOneSubgroup F G).inv_mem hk₁)
  have hz : z ∈ leviHeightSet hi hK hρ A := by
    refine ⟨b.val * aM, by rw [map_mul, haM], hz₁, ?_⟩
    rw [← hprod, height_siegel_product hG hi hν hK hρ n b a hk'] at hxH
    change H₀ (mMap b.val * positiveTorusMap F i a) ∈ A
    simpa only [map_one, one_mul, mul_one] using
      (show H₀ (nMap (1 : AdelicGroupPoints F N₀) * mMap b.val * positiveTorusMap F i a * 1) ∈ A by
        rwa [height_siegel_product hG hi hν hK hρ (1 : AdelicGroupPoints F N₀) b a K.one_mem])
  refine ⟨nMap n * z, ⟨nMap n, ⟨n, hn, rfl⟩, z, hz, rfl⟩, k, hk', ?_⟩
  change (nMap n * (mMap b.val * positiveTorusMap F i a)) * k = x
  rwa [← mul_assoc]

include hG hi hν in
/-- The unrestricted product and the common Siegel representatives have the same image on the
norm-one rational quotient. -/
theorem normOneCharacteristicHeightImage_eq
    (C : CompactFactors F G N₀ M₀) (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C)
    {A : Set (V T)} {T₁ : V T}
    (hcut : ∀ X ∈ A, ∀ α ∈ simpleRelativeRoots i ν, 0 < eval T α (X - T₁)) :
    LeftCosetSpace.mk (rationalNormOneSubgroup F G) ''
        (Subtype.val ⁻¹' characteristicHeightProduct hi hK hρ C A) =
      LeftCosetSpace.mk (rationalNormOneSubgroup F G) ''
        (Subtype.val ⁻¹' (siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁ ∩ H₀ ⁻¹' A)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨δ, hδ, hy, hyH⟩ :=
      exists_siegelRepresentative_of_mem_characteristicHeightProduct hG hi hν hK hρ C hC hcov hcut hx
    have hd : δ ∈ rationalSubgroup F G := by
      obtain ⟨q, _, rfl⟩ := hδ
      exact q.2
    obtain ⟨q, rfl⟩ := hd
    let q₁ := rationalNormOne F G q
    exact ⟨q₁ * x, ⟨hy, hyH⟩,
      LeftCosetSpace.mk_subgroup_mul (rationalNormOneSubgroup F G) ⟨q₁, ⟨q, rfl⟩⟩ x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x,
      mem_characteristicHeightProduct_of_siegelRepresentative hG hi hν hK hρ C hC hx.1 x.2 hx.2,
      rfl⟩

omit [NumberField F] [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- The negative shift by the generic cocharacter converts a closed lower cut to a strict
one. -/
theorem exists_strict_lower_cutoff (T₀ : V T) :
    ∃ T₁ : V T, ∀ (X : V T) (α : characterLattice T), α ∈ simpleRelativeRoots i ν →
      0 ≤ eval T α (X - T₀) → 0 < eval T α (X - T₁) := by
  refine ⟨T₀ - (1 : ℝ) ⊗ₜ[ℤ] ν, ?_⟩
  intro X α hα hx
  have hνpos : (0 : ℝ) < (latticePairing T α ν : ℝ) := by exact_mod_cast hα.1.2
  rw [sub_sub_eq_add_sub, add_sub_right_comm, map_add, eval_tmul, one_mul]
  exact add_pos_of_nonneg_of_pos hx hνpos

end Langlands.Global.ArthurTruncation
