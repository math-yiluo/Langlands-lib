import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.ArthurSiegelPartitionProof
import Langlands.Global.ArthurSiegelCoveringProof
import Langlands.Global.AdelicMinimalParabolicNormCoordinatesProof
import Langlands.LinearAlgebra.ArthurCombinatoricsSigmaSupport

/-! # Compactness of Delorme's characteristic truncation region -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Topology
open scoped CategoryTheory.MonObj Classical Pointwise

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  ArthurRelative ArthurParabolicSpaces AdelicGroupPoints AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "Δ" => simpleRelativeRoots i ν
local notation "Γ" => rationalNormOneSubgroup F G
local notation "M₀" => Standard.leviScheme i ν ∅
local notation "N₀" => Standard.unipotentScheme i ν ∅
local notation "Gₐ" => AdelicGroupPoints F G
local notation "H₀" => height hi hK hρ
local notation "nMap" => map F N₀ G (Standard.unipotentHom i ν ∅)
local notation "mMap" => map F M₀ G (Standard.leviHom i ν ∅)

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
private theorem isCompact_characteristicChamberCoordinates
    (hν : IsGenericCocharacter i ν) (T₀ Tp : V T) :
    let e := (base hG hi hν D).toCoweightBasis.equivFun
    IsCompact ((D.realCorootSpan.subtype.comp e.symm.toLinearMap) ⁻¹'
      characteristicChamber ν hG hi D T₀ Tp) := by
  let := finite_indivisibleRoots hG hi
  let b := base hG hi hν D
  let e := b.toCoweightBasis.equivFun
  let L := D.realCorootSpan.subtype.comp e.symm.toLinearMap
  let A := L ⁻¹' characteristicChamber ν hG hi D T₀ Tp
  change IsCompact A
  have hform : A = ⋂ β : simpleFinset ν hG hi,
      {x | 0 ≤ eval T β.1 (L x - T₀)} ∩
      {x | weight hG hi ν D (simpleFinset ν hG hi : Set (characterLattice T)) β.1 (L x - Tp) ≤ 0} := by
    ext x
    change L x ∈ characteristicChamber ν hG hi D T₀ Tp ↔ _
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun hx β => hx.2 β.1 β.2, fun hx => ⟨(e.symm x).2, fun β hβ => hx ⟨β, hβ⟩⟩⟩
  have hcont (f : V T →ₗ[ℝ] ℝ) (v : V T) : Continuous (fun x => f (L x - v)) := by
    have hf : Continuous (fun x => f (L x)) := (f.comp L).continuous_of_finiteDimensional
    simp only [map_sub]
    exact hf.sub continuous_const
  have hclosed : IsClosed A := by
    rw [hform]
    apply isClosed_iInter
    intro β
    exact (isClosed_le continuous_const (hcont (eval T β.1) T₀)).inter
      (isClosed_le (hcont (weight hG hi ν D (simpleFinset ν hG hi) β.1) Tp) continuous_const)
  let w := weight hG hi ν D Δ
  have hcoord (x : ↥b.support → ℝ) (j : b.support) : w j.1.1 (L x) = x j := by
    change w j.1.1 (e.symm x : V T) = _
    rw [weight_coe hG hi ν D Δ j.1, standardIndex_simpleRelativeRoots hG hi D hν,
      toCorootSpan_apply_coe, ← ArthurCombinatorics.toCoweightBasis_repr_eq b]
    exact congrFun (e.apply_symm_apply x) j
  have hbox : A ⊆ Set.Icc (fun j : b.support => w j.1.1 T₀) (fun j => w j.1.1 Tp) := by
    intro x hx
    change L x ∈ characteristicChamber ν hG hi D T₀ Tp at hx
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [← hcoord x j, ← sub_nonpos, ← map_sub, weight_coe hG hi ν D Δ j.1]
      apply ArthurCombinatorics.weightCoordinate_nonpos b (standardIndex_subset_support hG hi D hν Δ)
      intro k hk
      have hkΔ := ((mem_standardIndex hG hi ν).mp hk).1
      have he := (hx.2 k.1 ((mem_simpleFinset hG hi).mpr hkΔ)).1
      rw [← eval_eq_root' hG hi D hkΔ, map_sub]
      rw [map_sub] at he
      linarith
    · rw [← hcoord x j, ← sub_nonpos, ← map_sub]
      have hj := (mem_support_base hG hi hν D).mp j.2
      simpa only [coe_simpleFinset hG hi] using (hx.2 j.1.1 ((mem_simpleFinset hG hi).mpr hj)).2
  exact isCompact_Icc.of_isClosed_subset hclosed hbox

private def torusLogOf (X : V T) : RealCharacterDual F T.toGrp where
  toFun χ := eval T χ X
  map_zero' := by rw [eval_eq_pair, tmul_zero, map_zero, LinearMap.zero_apply]
  map_add' a b := by simp only [eval_eq_pair, tmul_add, map_add, LinearMap.add_apply]

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
include hi hK hρ in
private theorem height_positive_log (a : PositiveRealTorus.intrinsicSubgroup F T) (X : V T) :
    H₀ (positiveTorusMap F i a) = X ↔ characterLog F T.toGrp a.val = torusLogOf (F := F) X := by
  have hχ (χ : characterLattice T) : eval T χ (H₀ (positiveTorusMap F i a)) =
      characterLog F T.toGrp a.val χ := by
    rw [positiveTorusMap_apply, eval_height_torus, realParameterPairing_tmul, one_mul]
  constructor
  · intro h
    apply AddMonoidHom.ext
    intro χ
    exact (hχ χ).symm.trans (congrArg (eval T χ) h)
  · intro h
    apply (isPerfPair_of_isSplitTorus hi.isSplitSubtorus.1).bijective_right.injective
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r χ =>
      have he : eval T χ (H₀ (positiveTorusMap F i a)) = eval T χ X := by
        rw [hχ, h]
        rfl
      rw [eval_eq_pair] at he
      rw [show r ⊗ₜ[ℤ] χ = r • ((1 : ℝ) ⊗ₜ[ℤ] χ) by rw [smul_tmul', smul_eq_mul, mul_one]]
      simp only [map_smul, smul_eq_mul]
      exact congrArg (fun t : ℝ => r * t) he

omit [LocallyOfFiniteType G.X.hom] in
include hG hi hK hρ in
private theorem isCompact_heightPositivePreimage (hν : IsGenericCocharacter i ν) (T₀ Tp : V T) :
    IsCompact {a : PositiveRealTorus.intrinsicSubgroup F T |
      H₀ (positiveTorusMap F i a) ∈ characteristicChamber ν hG hi D T₀ Tp} := by
  let b := base hG hi hν D
  let u := b.toCoweightBasis.equivFun
  let L := D.realCorootSpan.subtype.comp u.symm.toLinearMap
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.isSplitSubtorus.1
  let := hI
  let := Fintype.ofFinite I
  let Exp := PositiveRealTorus.positiveExp F T I e
  have hlog (X : V T) : characterLog F T.toGrp (Exp (torusLogOf X)).val = torusLogOf X :=
    PositiveRealTorus.characterLog_full_logParameters F T I e _
  have hHx (X : V T) : H₀ (positiveTorusMap F i (Exp (torusLogOf X))) = X :=
    (height_positive_log hi hK hρ _ _).mpr (hlog X)
  have hA : {a : PositiveRealTorus.intrinsicSubgroup F T |
      H₀ (positiveTorusMap F i a) ∈ characteristicChamber ν hG hi D T₀ Tp} =
      (Exp ∘ torusLogOf ∘ L) '' (L ⁻¹' characteristicChamber ν hG hi D T₀ Tp) := by
    ext a
    constructor
    · intro ha
      change H₀ (positiveTorusMap F i a) ∈ characteristicChamber ν hG hi D T₀ Tp at ha
      let x := u ⟨H₀ (positiveTorusMap F i a), ha.1⟩
      have hL : L x = H₀ (positiveTorusMap F i a) := by simp [L, x]
      refine ⟨x, by simpa only [Set.mem_preimage, hL] using ha, ?_⟩
      apply (PositiveRealTorus.positiveLogEquiv F T I e).injective
      change Multiplicative.ofAdd (characterLog F T.toGrp
        (Exp (torusLogOf (L x))).val) =
          Multiplicative.ofAdd (characterLog F T.toGrp a.val)
      rw [hlog, hL, ← (height_positive_log hi hK hρ a _).mp rfl]
    · rintro ⟨X, hX, rfl⟩
      simpa only [Set.mem_ofPred_eq, Function.comp_apply, hHx, Set.mem_preimage] using hX
  rw [hA]
  have hcont : Continuous (torusLogOf (F := F) ∘ L) := by
    apply continuous_induced_rng.mpr
    exact continuous_pi fun χ => ((eval T χ).comp L).continuous_of_finiteDimensional
  exact (isCompact_characteristicChamberCoordinates hG hi D hν T₀ Tp).image
    ((PositiveRealTorus.continuous_positiveExp F T I e).comp hcont)

/-- For fixed compact Siegel factors satisfying the rational coverings of (7.1),
the characteristic region on the norm-one quotient is compact. -/
def CharacteristicRegionCompactStatement : Prop :=
  IsGenericCocharacter i ν →
  ∀ (C : CompactFactors F G N₀ M₀), C.compactSubgroup = K → IsRationalCovering C →
    ∀ T₀ Tp : V T, IsCompact (characteristicRegion hG hi D hK hρ C T₀ Tp)

set_option maxHeartbeats 500000 in
/-- Use both compact factors of the rational covering, splitting the minimal Levi
at its positive central torus. -/
theorem characteristicRegion_compact : CharacteristicRegionCompactStatement hG hi D hK hρ := by
  intro hν C hC hcov T₀ Tp
  let Ch := characteristicChamber ν hG hi D T₀ Tp
  let Pos := PositiveRealTorus.intrinsicSubgroup F T
  let A : Set Pos := {a | H₀ (positiveTorusMap F i a) ∈ Ch}
  let Cpt := productSet F G T i ν (canonicalStandardFactors F G T i ν) C T (𝟙 T) A
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hCpt : IsCompact Cpt := isCompact_productSet F G T i ν (canonicalStandardFactors F G T i ν)
    C T (𝟙 T) (isCompact_heightPositivePreimage hG hi D hK hρ hν T₀ Tp)
  let ambient : normOneSubgroup F G → Gₐ := Subtype.val
  have hclosed : IsClosedEmbedding ambient := (isClosed_normOneSubgroup F G).isClosedEmbedding_subtypeVal
  let R := LeftCosetSpace.mk Γ '' (ambient ⁻¹' Cpt)
  have hRc : IsCompact R := (hclosed.isCompact_preimage hCpt).image (LeftCosetSpace.continuous_mk Γ)
  have hh (m : normOneSubgroup F M₀) (a : Pos) :
      H₀ (mMap m * positiveTorusMap F i a) = H₀ (positiveTorusMap F i a) := by
    simpa only [map_one, one_mul, mul_one] using
      height_siegel_product hG hi hν hK hρ (1 : AdelicGroupPoints F N₀) m a K.one_mem
  have hnNorm (n : AdelicGroupPoints F N₀) : nMap n ∈ normOneSubgroup F G := by
    have hN := RepresentationGrowth.isUnipotent_standardUnipotentScheme F G T i ν hG hi hν ∅
      (Set.empty_subset _)
    rw [← characterLog_eq_zero_iff, characterLog_map, characterLog_eq_zero_of_isUnipotent hN, map_zero]
  have hkNorm (k : Gₐ) (hk : k ∈ K) : k ∈ normOneSubgroup F G :=
    compactSubgroup_le_normOneSubgroup F G K hK.isCompact hk
  have htorus (a : Pos) :
      ∃ m : AdelicGroupPoints F M₀, mMap m = positiveTorusMap F i a := by
    refine ⟨map F T.toGrp M₀ (torusToStandardLevi F G T i ν) a.val, ?_⟩
    rw [positiveTorusMap_apply, ← map_comp_apply_of_hom, torusToStandardLevi_comp]
  suffices hR : characteristicRegion hG hi D hK hρ C T₀ Tp = R by rwa [hR]
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨_, ⟨_, ⟨n, hn, rfl⟩, _, ⟨m, rfl, hm1, hmH⟩, rfl⟩, k, hk, heq⟩ := hx
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
    obtain ⟨⟨a, m₁⟩, he⟩ := e.surjective m
    have hmul : mMap m = mMap m₁.val * positiveTorusMap F i a := by
      rw [← he, PositiveRealTorus.splitComponentNormOneDecomposition_apply,
        (PositiveRealTorus.positivePointMap_commute F M₀ T t hcent a m₁.val).eq, map_mul]
      congr 1
      rw [PositiveRealTorus.positivePointMap_apply, positiveTorusMap_apply,
        ← map_comp_apply_of_hom, torusToStandardLevi_comp]
    have ha : a ∈ A := by
      change H₀ (positiveTorusMap F i a) ∈ Ch
      rwa [hmul, hh] at hmH
    obtain ⟨r, ωm, hωm, hm₁⟩ := hcov.2 m₁
    let rG := (M₀).affinePointsTarget (Standard.leviHom i ν ∅) (CommAlgCat.of F F) r
    let rA := rational F G rG
    have hr : mMap (rational F M₀ r) = rA :=
      (DFunLike.congr_fun (rational_naturality F M₀ (Standard.leviHom i ν ∅)) r).symm
    have hnorm : rA⁻¹ ∈ standardParabolicImage F G T i ν :=
      (standardParabolicImage F G T i ν).inv_mem
        (standardLeviImage_le_parabolic F G T i ν ⟨rational F M₀ r, hr⟩)
    have hn' := (Subgroup.mem_normalizer_iff.mp
      (standardParabolicImage_le_normalizer F G T i ν hnorm) (nMap n)).mp
      (show nMap n ∈ standardUnipotentImage F G T i ν from ⟨n, rfl⟩)
    obtain ⟨n', hn'⟩ := hn'
    change nMap n' = rA⁻¹ * nMap n * rA⁻¹⁻¹ at hn'
    obtain ⟨_, ⟨s, rfl⟩, ωn, hωn, hn''⟩ := hcov.1 n'
    let sG := (N₀).affinePointsTarget (Standard.unipotentHom i ν ∅) (CommAlgCat.of F F) s
    have hs : nMap (rational F N₀ s) = rational F G sG :=
      (DFunLike.congr_fun (rational_naturality F N₀ (Standard.unipotentHom i ν ∅)) s).symm
    let y := nMap ωn * mMap ωm.val * positiveTorusMap F i a * k
    have hy : y ∈ Cpt := (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν)
      C T (𝟙 T) A y).mpr ⟨ωn, hωn, ωm, hωm, a, ha, k, hC.symm ▸ hk, rfl⟩
    have hxy : rational F G (rG * sG) * y = x.val := by
      rw [← heq, hmul, hm₁, map_mul mMap, hr, map_mul, ← hs]
      simp only [y]
      have hnAux : nMap (rational F N₀ s) * nMap ωn = rA⁻¹ * nMap n * rA := by
        rw [← map_mul, ← hn'', hn', inv_inv]
      rw [show rA * nMap (rational F N₀ s) * y =
        rA * (nMap (rational F N₀ s) * nMap ωn) * mMap ωm.val * positiveTorusMap F i a * k by
          dsimp only [y]; group, hnAux]
      group
    have hyN : y ∈ normOneSubgroup F G := by
      rw [show y = (rational F G (rG * sG))⁻¹ * x.val by rw [← hxy, inv_mul_cancel_left]]
      exact (normOneSubgroup F G).mul_mem
        ((normOneSubgroup F G).inv_mem (rationalSubgroup_le_normOneSubgroup F G ⟨_, rfl⟩)) x.2
    let y₁ : normOneSubgroup F G := ⟨y, hyN⟩
    have hexy : rationalNormOne F G (rG * sG) * y₁ = x := Subtype.ext hxy
    exact ⟨y₁, hy, by rw [← hexy, LeftCosetSpace.mk_subgroup_mul Γ ⟨_, ⟨_, rfl⟩⟩ y₁]⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, hn, m, hm, a, ha, k, hk, hy⟩ :=
      (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T (𝟙 T) A y.val).mp hy
    change AdelicGroupPoints F N₀ at n
    change normOneSubgroup F M₀ at m
    change nMap n * mMap m.val * positiveTorusMap F i a * k = y.val at hy
    obtain ⟨aM, haM⟩ := htorus a
    let z := mMap m.val * positiveTorusMap F i a
    have hzN : z ∈ normOneSubgroup F G := by
      have he : z = (nMap n)⁻¹ * y.val * k⁻¹ := by rw [← hy]; dsimp only [z]; group
      rw [he]
      exact (normOneSubgroup F G).mul_mem
        ((normOneSubgroup F G).mul_mem ((normOneSubgroup F G).inv_mem (hnNorm n)) y.2)
        ((normOneSubgroup F G).inv_mem (hkNorm k (hC ▸ hk)))
    have hz : z ∈ leviHeightSet hi hK hρ Ch := by
      refine ⟨m.val * aM, by rw [map_mul, haM], hzN, ?_⟩
      change H₀ (mMap m.val * positiveTorusMap F i a) ∈ Ch
      rw [hh]
      exact ha
    refine ⟨y, ?_, rfl⟩
    change y.val ∈ characteristicProduct hG hi D hK hρ C T₀ Tp
    rw [characteristicProduct, Set.mem_mul]
    refine ⟨nMap n * z, Set.mem_mul.mpr ⟨nMap n, ⟨n, hn, rfl⟩, z, hz, rfl⟩, k, hC ▸ hk, ?_⟩
    change (nMap n * (mMap m.val * positiveTorusMap F i a)) * k = y.val
    rwa [← mul_assoc]

/-- The quotient characteristic region is Borel measurable. -/
theorem measurableSet_characteristicRegion (hν : IsGenericCocharacter i ν)
    (C : CompactFactors F G N₀ M₀) (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C)
    (T₀ Tp : V T) : MeasurableSet (characteristicRegion hG hi D hK hρ C T₀ Tp) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact (characteristicRegion_compact hG hi D hK hρ hν C hC hcov T₀ Tp).isClosed.measurableSet

end Langlands.Global.ArthurTruncation
