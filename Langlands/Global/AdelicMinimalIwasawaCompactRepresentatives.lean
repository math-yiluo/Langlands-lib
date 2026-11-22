import Langlands.Global.AdelicWeightedSiegelSpace
import Langlands.Global.AdelicSpringerCentralCompactnessProof
import Langlands.Global.AdelicNormOneSectionCompactCover
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.Global.AdelicPositiveDecompositionReduction

/-! # Compact representatives in minimal-parabolic Iwasawa coordinates -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Set Topology
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable (F : Type u) [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (j : T₀ ⟶ T)

local notation "P" => Standard.parabolicScheme i ν ∅
local notation "M" => Standard.leviScheme i ν ∅
local notation "p" => Standard.parabolicHom i ν ∅
local notation "levi" => Standard.leviToParabolic i ν ∅
local notation "tM" => torusToStandardLevi F G T i ν
local notation "tP" => torusToStandardParabolic F G T i ν
local notation "A" => intrinsicSubgroup F T
local notation "Gₐ" => AdelicGroupPoints F G

private instance : IsClosedImmersion (p).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν ∅

private instance : IsAffine (P).X.left := isAffine_of_isAffineHom (p).hom.hom.left

/-- The positive torus of the ambient maximal split torus supplies a continuous
section of minimal-parabolic height, and a fixed compact set of norm-one left
factors suffices modulo rational minimal-parabolic translation. -/
def MinimalIwasawaCompactRepresentativesStatement : Prop :=
  IsSiegelAlgebraicSetup F G T i ν T₀ j →
  ∀ (K : Subgroup Gₐ) (hK : IsIwasawaCompact p K),
    ∃ (a : RealCharacterDual F P → A) (Ω : Set (normOneSubgroup F P)),
      Continuous a ∧ IsCompact Ω ∧
      (∀ h, characterLog F P (positivePointMap F P T tP (a h)) = h) ∧
      ∀ x : Gₐ, ∃ (q : RationalGroupPoints F P), ∃ z ∈ Ω, ∃ k ∈ K,
        map F P G p (rational F P q) * x =
          map F P G p z * positivePointMap F G T i (a (hK.height x)) * k

theorem minimalIwasawaCompactRepresentatives :
    MinimalIwasawaCompactRepresentativesStatement F i ν j := by
  classical
  intro hsetup K hK
  have hLevi := hsetup.2.2.2.1
  have hM := hLevi.isConnectedReductive
  let : IsAffineHom (M).X.hom := hM.isAffineHom
  have hmax : IsMaximalSplitTorus tM := hsetup.1.isMaximalSplitTorus_standardLeviTorusFactor
    i ν ∅ (Standard.isRepresentedBy_leviHom i ν ∅) (Standard.isClosedSubgroup_leviHom i ν ∅)
  have hcent : IsCentral tM := by
    apply isCentral_of_range_le_torusCentralizer (Standard.isRepresentedBy_leviHom i ν ∅).1
    rw [torusToStandardLevi_comp, (Standard.isRepresentedBy_leviHom i ν ∅).2, hsetup.2.2.2.2.2.1]
  have hsplit : IsSplitComponent tM :=
    ⟨⟨hmax.1, hcent⟩, fun S s hs x hx => hmax.2 S s hs.1 x hx⟩
  have hresM := characterRestrict_injective_of_centralSplitTorusCharacter
    centralSplitTorusCharacter hM hsplit
  have hresP : Function.Injective (characterRestrict tP) := by
    rw [torusToStandardParabolic, characterRestrict_comp]
    exact hresM.comp hLevi.characterRestrict_bijective.injective
  have hrange : (characterRestrict tP).range = (characterRestrict tM).range := by
    rw [torusToStandardParabolic, characterRestrict_comp]
    ext χ
    change (∃ ψ, characterRestrict tM (characterRestrict levi ψ) = χ) ↔
      (∃ ψ, characterRestrict tM ψ = χ)
    constructor
    · rintro ⟨ψ, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨ψ, rfl⟩
      obtain ⟨ξ, rfl⟩ := hLevi.characterRestrict_bijective.surjective ψ
      exact ⟨ξ, rfl⟩
  have hfin := hsplit.finiteIndex_range_characterRestrict hM
  let : (characterRestrict tP).range.FiniteIndex := hrange ▸ hfin
  obtain ⟨I, hI, ⟨e⟩⟩ := hmax.1.1
  let : Fintype I := Fintype.ofFinite I
  let eA := positiveAmbientLogEquiv F P T tP hresP I e
  let a : RealCharacterDual F P → A := fun h => eA.symm (Multiplicative.ofAdd h)
  have ha : Continuous a := eA.symm.continuous
  have halog (h : RealCharacterDual F P) :
      characterLog F P (positivePointMap F P T tP (a h)) = h := by
    change characterLogHom F P (positivePointMap F P T tP (a h)) = Multiplicative.ofAdd h
    rw [characterLogHom_positivePointMap F P T tP hresP I e]
    exact eA.apply_symm_apply (Multiplicative.ofAdd h)
  obtain ⟨Ω, hΩ, hrep⟩ := hasCompactNormOneRationalCover_of_rationalLevi hLevi
    (exists_leviCompactCover_of_setup centralSplitCompactQuotient hsetup)
  refine ⟨a, Ω, ha, hΩ, halog, fun x => ?_⟩
  obtain ⟨y, k, hk, hyk⟩ := hK.exists_eq x
  let u := positivePointMap F P T tP (a (hK.height x))
  have hfactor : (y * u⁻¹) * u = y := inv_mul_cancel_right _ _
  have hylog := hK.height_eq hk hyk
  have hlog : characterLog F P (y * u⁻¹) = 0 := by
    conv at hylog => rhs; rw [← hfactor, characterLog_mul, show characterLog F P u = _ from halog _]
    exact add_right_cancel (by simpa only [zero_add] using hylog.symm)
  let y₁ : normOneSubgroup F P := ⟨y * u⁻¹, (characterLog_eq_zero_iff F P _).mp hlog⟩
  obtain ⟨q, hq⟩ := hrep y₁
  refine ⟨q, rationalNormOne F P q * y₁, hq, k, hk, ?_⟩
  have hu : map F P G p u = positivePointMap F G T i (a (hK.height x)) := by
    change map F P G p (map F T.toGrp P tP (a (hK.height x)).val) = _
    rw [← map_comp_apply_of_hom («p» := p), torusToStandardParabolic_comp]
    rfl
  rw [← hu, ← hyk, ← mul_assoc, ← map_mul, ← map_mul]
  congr 2
  change rational F P q * y = (rational F P q * (y * u⁻¹)) * u
  rw [mul_assoc, hfactor]

/-- A compact height set has compact inverse image in the rational
minimal-parabolic quotient. -/
theorem isCompact_domainHeight_preimage
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    {K : Subgroup Gₐ} (hK : IsIwasawaCompact p K)
    {B : Set (RealCharacterDual F P)} (hB : IsCompact B) :
    IsCompact (WeightedSiegel.domainHeight F p hK ⁻¹' B) := by
  obtain ⟨a, Ω, ha, hΩ, _, hrep⟩ := minimalIwasawaCompactRepresentatives F i ν j hsetup K hK
  let Z := WeightedSiegel.parabolicPrincipalSubgroup F p
  let C : Set Gₐ := ((fun z : normOneSubgroup F P => map F P G p z) '' Ω) *
    ((positivePointMap F G T i ∘ a) '' B) * (K : Set Gₐ)
  have hC : IsCompact C := ((hΩ.image ((map F P G p).continuous.comp continuous_subtype_val)).mul
    (hB.image ((positivePointMap F G T i).continuous.comp ha))).mul hK.isCompact
  refine (hC.image (LeftCosetSpace.continuous_mk Z)).of_isClosed_subset
    (hB.isClosed.preimage (WeightedSiegel.continuous_domainHeight F p hK)) ?_
  intro z hz
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Z z
  obtain ⟨q, b, hb, k, hk, hq⟩ := hrep x
  have hqmem : map F P G p (rational F P q) ∈ Z := ⟨_, ⟨q, rfl⟩, rfl⟩
  refine ⟨_, ⟨_, ⟨_, ⟨b, hb, rfl⟩, _, ⟨_, hz, rfl⟩, rfl⟩, k, hk, rfl⟩, ?_⟩
  change LeftCosetSpace.mk Z
    (map F P G p b * positivePointMap F G T i (a (hK.height x)) * k) = _
  rw [← hq]
  exact LeftCosetSpace.mk_subgroup_mul Z ⟨_, hqmem⟩ x

end Langlands.Global.AdelicSiegelFactors
