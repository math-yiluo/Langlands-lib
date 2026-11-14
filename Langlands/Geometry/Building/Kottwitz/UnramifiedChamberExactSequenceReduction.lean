import Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceStatement
import Langlands.Geometry.Building.Kottwitz.ZeroKernelReduction
import Langlands.Geometry.Building.IntegerValuationNormalizerSharpReduction
import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof
import Langlands.Geometry.Building.IntegerChamberStabilizerReduction
import Langlands.Geometry.Building.IntegerValuationAffineWeylProof
import Langlands.Geometry.Building.AffineChamberTransitivity
import Langlands.Geometry.Building.IwahoriWeylChamberLemmas
import Langlands.Geometry.Building.UnramifiedSimplyConnectedChamberStabilizerStatement
import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylStatement
import Langlands.GroupScheme.SimplyConnected.DerivedCoverProof

/-! # KP Proposition 11.6.1 from its Kottwitz-theoretic and normalizer inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  (B : IntegerValuationBuildingData v G)

/-- The quotient coordinate change of `exists_normalizer_eq_on_translated_facet`,
also recording that the normalizer element differs from the given point by an
element of the sharp fixer of the facet. -/
theorem exists_normalizer_sharp_eq_on_translated_facet
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    {a b : B.Apartment} (ha : a ∈ Fa) (g : rationalPoints G)
    (hab : g • B.apartmentMap a = B.apartmentMap b) :
    ∃ n : normalizerPoints B.i, n • a = b ∧
      g⁻¹ * (n : rationalPoints G) ∈ B.apartment.sharpFixer Fa ∧
      ∀ y ∈ Fa, g • B.apartmentMap y = B.apartmentMap (n • y) := by
  have hab' :
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (g, a) =
        ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, b) := by
    have h :
        ApartmentQuotient.mk B.apartment.sharpFixerFamily (g * 1, a) =
          ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, b) := hab
    simpa only [mul_one] using h
  obtain ⟨n, hn, hp⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff B.apartment.sharpFixerFamily g 1 a b).mp hab'
  have hp' : g⁻¹ * (n : rationalPoints G) ∈ B.apartment.sharpFixer Fa := by
    rw [B.apartment.sharpFixer_eq_singleton_of_isFacet
      B.affineRoot_mem_or_two_smul_mem hFa ha]
    change g⁻¹ * 1 * (n : rationalPoints G) ∈ B.apartment.sharpFixer {a} at hp
    simpa only [mul_one] using hp
  refine ⟨n, hn, hp', fun y hy => ?_⟩
  have hfix : (g⁻¹ * (n : rationalPoints G)) • B.apartmentMap y =
      B.apartmentMap y :=
    B.apartment.mem_reducedFixer.mp (B.apartment.sharpFixer_le_reducedFixer y
      (B.apartment.sharpFixer_anti (Set.singleton_subset_iff.mpr hy) hp'))
  have heq := congrArg (g • ·) hfix
  rw [mul_smul, smul_inv_smul, B.normalizer_smul_apartmentMap] at heq
  exact heq.symm

/-- A stabilizer of a translated full facet lying in a normal subgroup `Z` that
contains every sharp fixer agrees there with a normalizer element of `Z`
stabilizing the original apartment facet. -/
theorem exists_normalizer_mem_stabilizes_eq_on_translated_facet
    (Z : Subgroup (rationalPoints G)) [Z.Normal]
    (hZ : ∀ Ω : Set B.Apartment, B.apartment.sharpFixer Ω ≤ Z)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (h g : rationalPoints G) (hgZ : g ∈ Z)
    (hg : (g • ·) '' ((fun y => h • B.apartmentMap y) '' Fa) =
      (fun y => h • B.apartmentMap y) '' Fa) :
    ∃ n : normalizerPoints B.i, (n : rationalPoints G) ∈ Z ∧ n • Fa = Fa ∧
      ∀ y ∈ Fa, g • (h • B.apartmentMap y) =
        h • B.apartmentMap (n • y) := by
  have hnonempty : Fa.Nonempty := by
    obtain ⟨a, rfl⟩ := hFa
    exact ⟨a, AffineRootSystem.mem_facet_self _ _⟩
  obtain ⟨a, ha⟩ := hnonempty
  have hga : g • (h • B.apartmentMap a) ∈
      (fun y => h • B.apartmentMap y) '' Fa := by
    rw [← hg]
    exact ⟨h • B.apartmentMap a, ⟨a, ha, rfl⟩, rfl⟩
  obtain ⟨b, hb, hab⟩ := hga
  have hab' : (h⁻¹ * g * h) • B.apartmentMap a = B.apartmentMap b := by
    have H := congrArg (h⁻¹ • ·) hab
    simpa only [mul_smul, inv_smul_smul] using H.symm
  obtain ⟨n, hn, hsharp, heq⟩ :=
    B.exists_normalizer_sharp_eq_on_translated_facet hFa ha (h⁻¹ * g * h) hab'
  have hconj : h⁻¹ * g * h ∈ Z := by
    have H := ‹Z.Normal›.conj_mem g hgZ h⁻¹
    simpa only [inv_inv] using H
  have hnZ : (n : rationalPoints G) ∈ Z := by
    have H := Z.mul_mem hconj (hZ Fa hsharp)
    simpa only [mul_inv_cancel_left] using H
  have hnFa : n • Fa = Fa :=
    (B.normalizer_smul_isFacet hFa n).eq_of_mem_mem hFa
      (hn ▸ Set.smul_mem_smul_set ha) hb
  refine ⟨n, hnZ, hnFa, fun y hy => ?_⟩
  have H := congrArg (h • ·) (heq y hy)
  simpa only [mul_smul, smul_inv_smul] using H

/-- Assume some unit of `k` has valuation order one. If the normalizer elements
of a normal subgroup `Z` containing every sharp fixer act through the affine Weyl
group, then every element of `Z` stabilizing a chamber fixes it pointwise. -/
theorem mem_pointwiseFixer_of_mem_of_stabilizes_chamber
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (Z : Subgroup (rationalPoints G)) [Z.Normal]
    (hZ : ∀ Ω : Set B.Apartment, B.apartment.sharpFixer Ω ≤ Z)
    (hNW : ∀ n : normalizerPoints B.i, (n : rationalPoints G) ∈ Z →
      B.apartment.normalizerAffineEquiv n ∈ AffineRootSystem.affineWeylGroup B.affineRoots)
    {Y : Set B.ReducedBuilding} (hY : B.IsChamber Y)
    {g : rationalPoints G} (hgZ : g ∈ Z) (hg : (g • ·) '' Y = Y) :
    g ∈ B.pointwiseFixer Y := by
  obtain ⟨h, Ca, hCa, rfl⟩ := hY
  obtain ⟨n, hnZ, hn, heq⟩ :=
    B.exists_normalizer_mem_stabilizes_eq_on_translated_facet Z hZ hCa.isFacet h g hgZ hg
  obtain ⟨w₀, -, huniq⟩ := affineChamberSimpleTransitivity _ _ _
    (B.isAffineRootSystemWithRankZero_affineRoots hunit) Ca Ca hCa hCa
  have h₁ : (⟨B.apartment.normalizerAffineEquiv n, hNW n hnZ⟩ :
      AffineRootSystem.affineWeylGroup B.affineRoots) = w₀ := huniq _ hn
  have h₂ : (1 : AffineRootSystem.affineWeylGroup B.affineRoots) = w₀ :=
    huniq _ (by simp)
  have hn₁ : B.apartment.normalizerAffineEquiv n = 1 :=
    congrArg Subtype.val (h₁.trans h₂.symm)
  rw [IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer]
  rintro z ⟨x, hx, rfl⟩
  rw [heq x hx]
  have hx' : n • x = x := by
    rw [← B.apartment.normalizerAffineEquiv_apply, hn₁]
    rfl
  rw [hx']

/-- Every affine Weyl element is the action of a normalizer element lying in any
subgroup that contains every sharp fixer. -/
theorem affineWeylGroup_le_map_subgroupOf
    (Z : Subgroup (rationalPoints G))
    (hZ : ∀ Ω : Set B.Apartment, B.apartment.sharpFixer Ω ≤ Z) :
    AffineRootSystem.affineWeylGroup B.affineRoots ≤
      (Z.subgroupOf (normalizerPoints B.i)).map B.apartment.normalizerAffineEquiv := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨ψ, hψ, w, hw, rfl⟩
  obtain ⟨m, hm, hmeq⟩ :=
    B.exists_sharpFixer_normalizer_eq_affineReflection (Ω := ∅) hψ (by simp) hw
  exact ⟨m, hZ ∅ hm, hmeq⟩

/-- Assume some unit of `k` has valuation order one. A normal subgroup
containing every sharp fixer carries every building chamber onto the image of any
prescribed apartment chamber. -/
theorem exists_mem_smul_chamber_eq_apartmentMap_image
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (Z : Subgroup (rationalPoints G)) [Z.Normal]
    (hZ : ∀ Ω : Set B.Apartment, B.apartment.sharpFixer Ω ≤ Z)
    {Y : Set B.ReducedBuilding} (hY : B.IsChamber Y)
    {C₀ : Set B.Apartment} (hC₀ : AffineRootSystem.IsChamber B.affineRoots C₀) :
    ∃ z ∈ Z, (z • ·) '' Y = B.apartmentMap '' C₀ := by
  obtain ⟨g, Ca, hCa, rfl⟩ := hY
  have hg : g ∈ Z ⊔ normalizerPoints B.i := by
    have htop := B.sharpFixer_sup_normalizer_eq_top hunit hC₀
    have hg' : g ∈ B.apartment.sharpFixer C₀ ⊔ normalizerPoints B.i := by
      rw [htop]
      exact Subgroup.mem_top g
    exact sup_le_sup_right (hZ C₀) _ hg'
  obtain ⟨z, hz, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  let n' : normalizerPoints B.i := ⟨n, hn⟩
  have hC₁ : AffineRootSystem.IsChamber B.affineRoots (n' • Ca) :=
    hCa.image (B.apartment.normalizerAffineEquiv_mem_rootStabilizer n')
  obtain ⟨w, hw, -⟩ := affineChamberSimpleTransitivity _ _ _
    (B.isAffineRootSystemWithRankZero_affineRoots hunit) _ _ hC₁ hC₀
  obtain ⟨m, hm, hmw⟩ := B.affineWeylGroup_le_map_subgroupOf Z hZ w.property
  refine ⟨(m : rationalPoints G) * z⁻¹, Z.mul_mem hm (Z.inv_mem hz), ?_⟩
  have hmC : (m • ·) '' (n' • Ca) = C₀ := by
    rw [← hw, ← hmw]
    rfl
  rw [Set.image_image, ← hmC]
  change _ = B.apartmentMap '' ((m • ·) '' ((n' • ·) '' Ca))
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  rw [← mul_smul, show (m : rationalPoints G) * z⁻¹ * (z * n) =
      (m : rationalPoints G) * (n' : rationalPoints G) by
    change (m : rationalPoints G) * z⁻¹ * (z * n) = (m : rationalPoints G) * n
    group]
  rw [mul_smul, B.normalizer_smul_apartmentMap n', B.normalizer_smul_apartmentMap m]

/-- Assume some unit of `k` has valuation order one. A normal subgroup
containing every sharp fixer acts transitively on the chambers of the
building. -/
theorem exists_mem_smul_chamber_eq
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1)
    (Z : Subgroup (rationalPoints G)) [Z.Normal]
    (hZ : ∀ Ω : Set B.Apartment, B.apartment.sharpFixer Ω ≤ Z)
    {Y Y' : Set B.ReducedBuilding} (hY : B.IsChamber Y) (hY' : B.IsChamber Y') :
    ∃ z ∈ Z, (z • ·) '' Y = Y' := by
  obtain ⟨-, C₀, hC₀, -⟩ := id hY'
  obtain ⟨z₁, hz₁, h₁⟩ := B.exists_mem_smul_chamber_eq_apartmentMap_image hunit Z hZ hY hC₀
  obtain ⟨z₂, hz₂, h₂⟩ := B.exists_mem_smul_chamber_eq_apartmentMap_image hunit Z hZ hY' hC₀
  refine ⟨z₂⁻¹ * z₁, Z.mul_mem (Z.inv_mem hz₂) hz₁, ?_⟩
  have H : (fun y => (z₂⁻¹ * z₁) • y) '' Y = (z₂⁻¹ • ·) '' ((z₁ • ·) '' Y) := by
    rw [Set.image_image]
    simp only [mul_smul]
  rw [H, h₁, ← h₂, Set.image_image]
  simp only [inv_smul_smul, Set.image_id']

end IntegerValuationBuildingData

section ChamberExactSequence

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]

/-- The two conclusions of KP Proposition 11.6.1 for a homomorphism `κ` on
`H(K)` and a subset `Cch` of the building of `B`. First, `κ` stays surjective on
the setwise stabilizer `H(K)_C` of `Cch`. Second, for every unramified zero
datum `E`, the zero points fixing `Cch` pointwise are exactly the kernel of `κ`
inside `H(K)_C`. -/
def Kottwitz.ChamberExactSequence (B : MaximalUnramified.BuildingData F H)
    {M : Type*} [MulOneClass M] (κ : rationalPoints H →* M)
    (Cch : Set B.ReducedBuilding) : Prop :=
  Function.Surjective (κ.domRestrict (MulAction.stabilizer (rationalPoints H) Cch)) ∧
    ∀ E : UnramifiedZeroDatum F H,
      E.zeroPoints ⊓ B.pointwiseFixer Cch =
        κ.ker ⊓ MulAction.stabilizer (rationalPoints H) Cch

namespace UnramifiedZeroDatum

/-- The chamber exact sequence for any homomorphism `κ` on `H(K)` that is
surjective and whose kernel is the zero subgroup of every supplied datum,
given one such datum and the simply connected normalizer assertion. -/
theorem chamberExactSequence_of_zeroPoints_eq_ker
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u})
    (B : MaximalUnramified.BuildingData F H) {M : Type*} [MulOneClass M]
    (κ : rationalPoints H →* M) (hκ : Function.Surjective κ)
    (E₀ : UnramifiedZeroDatum F H)
    (hZK : ∀ E : UnramifiedZeroDatum F H, E.zeroPoints = κ.ker)
    {Cch : Set B.ReducedBuilding} (hCch : B.IsChamber Cch) :
    Kottwitz.ChamberExactSequence B κ Cch := by
  have hunit := MaximalUnramified.exists_order_eq_one F
  unfold Kottwitz.ChamberExactSequence
  refine ⟨?_, ?_⟩
  · have := E₀.normal_zeroPoints
    intro t
    obtain ⟨x, rfl⟩ := hκ t
    obtain ⟨z, hz, hzx⟩ := B.exists_mem_smul_chamber_eq hunit E₀.zeroPoints
      (E₀.sharpFixer_le_zeroPoints B) (IntegerValuationBuildingData.IsChamber.smul B hCch x) hCch
    have hzP : z * x ∈ MulAction.stabilizer (rationalPoints H) Cch := by
      change (fun y => (z * x) • y) '' Cch = Cch
      have H : (fun y => (z * x) • y) '' Cch = (z • ·) '' ((x • ·) '' Cch) := by
        rw [Set.image_image]
        simp only [mul_smul]
      rw [H, hzx]
    refine ⟨⟨z * x, hzP⟩, ?_⟩
    have hzκ : κ z = 1 := by
      rw [← MonoidHom.mem_ker, ← hZK E₀]
      exact hz
    rw [MonoidHom.domRestrict_apply, map_mul, hzκ, one_mul]
  · intro E
    have := E.normal_zeroPoints
    rw [← hZK E]
    apply le_antisymm
    · rintro g ⟨hgz, hgfix⟩
      exact ⟨hgz, B.smul_image_eq_of_mem_pointwiseFixer hgfix⟩
    · rintro g ⟨hgz, hgP⟩
      exact ⟨hgz, B.mem_pointwiseFixer_of_mem_of_stabilizes_chamber hunit E.zeroPoints
        (E.sharpFixer_le_zeroPoints B) (E.normalizer_mem_affineWeylGroup_of_mem_zeroPoints B hsc)
        hCch hgz hgP⟩

end UnramifiedZeroDatum

end ChamberExactSequence

namespace Kottwitz

private instance unramifiedChamberExactSequenceReductionAffineHom
    {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- Surjectivity of the actual Kottwitz map on `K`-points
(`ReductiveKottwitzExistenceStatement`) transported to the rational-point carrier
of the base change. -/
theorem surjective_reductiveKottwitzOnBaseChange
    (hexist : ReductiveKottwitzExistenceStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    Function.Surjective (reductiveKottwitzOnBaseChange F G hG) := by
  unfold reductiveKottwitzOnBaseChange
  rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (hexist F F G hG).2.2.2.1.comp
    (baseChangeCoeffEquiv F (inertiaFixedField F) G).surjective

/-- `UnramifiedZeroKernelStatement` with `k = F`, rewritten as the kernel of the
Kottwitz map on the rational-point carrier of the base change. -/
theorem zeroPoints_eq_ker_reductiveKottwitzOnBaseChange
    (hkernel : UnramifiedZeroKernelStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom]
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G)) :
    E.zeroPoints = (reductiveKottwitzOnBaseChange F G hG).ker := by
  rw [hkernel F F G hG E, MonoidHom.comap_ker]
  rfl

/-- The base change of a connected reductive group to the maximal unramified
field carries an unramified zero datum, built from a simply connected derived
cover. -/
theorem nonempty_unramifiedZeroDatum_baseChanged
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom] :
    Nonempty (UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G)) := by
  have hGK := connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  obtain ⟨Dd, Cc, dK, π, hcover⟩ :=
    simplyConnectedDerivedCoverExistence (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G) hGK
  exact ⟨UnramifiedZeroDatum.ofDerivedCover dK π hcover⟩

/-- **KP Proposition 11.6.1 from its inputs.** Surjectivity of the Kottwitz map
(part of `ReductiveKottwitzExistenceStatement`), the identification of every
unramified zero subgroup with the Kottwitz kernel (`UnramifiedZeroKernelStatement`)
and the simply connected normalizer assertion over the maximal unramified field
imply the exact sequence on every supplied chamber. -/
theorem unramifiedChamberExactSequence_of_statements
    (hexist : ReductiveKottwitzExistenceStatement.{u})
    (hkernel : UnramifiedZeroKernelStatement.{u})
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u}) :
    UnramifiedChamberExactSequenceStatement.{u} := by
  intro F _ _ _ _ G hG T iT hiT D C h6 B Cch hCch P κ
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨E₀⟩ := nonempty_unramifiedZeroDatum_baseChanged F G hG
  have hfin := UnramifiedZeroDatum.chamberExactSequence_of_zeroPoints_eq_ker hsc B
    (reductiveKottwitzOnBaseChange F G hG)
    (surjective_reductiveKottwitzOnBaseChange hexist F G hG) E₀
    (zeroPoints_eq_ker_reductiveKottwitzOnBaseChange hkernel F G hG) hCch
  exact ⟨hfin.1, fun E => hfin.2 E⟩

end Kottwitz

end Langlands.Geometry.Building
