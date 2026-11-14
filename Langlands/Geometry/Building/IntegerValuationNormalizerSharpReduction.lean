import Langlands.Geometry.Building.IntegerValuationFiniteSharpReduction
import Langlands.Geometry.Building.IntegerValuationSharpCoverImage
import Langlands.Geometry.Building.AffineWeylPointStabilizer
import Langlands.Geometry.Building.UnramifiedZeroNormalizerComparison

/-! # Normalizer sharp-fixer comparison from affine Weyl containment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- An affine-root reflection vanishing on Ω lifts to the actual normalizer
inside the sharp fixer of Ω. -/
theorem exists_sharpFixer_normalizer_eq_affineReflection
    {Ω : Set B.Apartment} {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots)
    (hΩ : ∀ y ∈ Ω, ψ y = 0) {w : TranslationSpace B.i}
    (hw : AffineRootSystem.IsCoroot B.affineRoots ψ w) :
    ∃ m : normalizerPoints B.i, (m : rationalPoints G) ∈ B.sharpFixer Ω ∧
      B.apartment.normalizerAffineEquiv m = AffineRootSystem.affineReflection ψ hw.1 := by
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨α, u, hu, hu1, rfl⟩ := hψ'
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs α α.property u hu hu1
  have hflip : weylAction B.i (B.reflectionElement hp) α = -(α : characterLattice B.S) :=
    hp.weylAction_eq_neg B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hu hu1
  have hneg : -(α : characterLattice B.S) ∈ relativeRoots B.i :=
    hflip ▸ weylAction_mapsTo_relativeRoots B.i (B.reflectionElement hp) α.property
  have hval (y : B.Apartment) (hy : y ∈ Ω) : y.val α u = 0 := by
    rw [← B.coe_reflectionFunctional_apply hu hu1 y, hΩ y hy, WithTop.coe_zero]
  have hfix : u ∈ B.rootFixer α Ω := by
    refine B.apartment.mem_rootFixer.2 ⟨hu, fun y hy => ⟨hu, ?_⟩⟩
    simp only [hval y hy, WithTop.coe_zero, le_refl]
  have hp1 : p.1 ∈ B.rootFixer (-(α : characterLattice B.S)) Ω := by
    refine B.apartment.mem_rootFixer.2 ⟨hp.1, fun y hy => ⟨hp.1, ?_⟩⟩
    have h5 := y.isValuation.opposite α α.property u hu hu1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    rw [hval y hy, add_zero] at h5
    simp only [h5, WithTop.coe_zero, le_refl]
  have hp2 : p.2 ∈ B.rootFixer (-(α : characterLattice B.S)) Ω := by
    refine B.apartment.mem_rootFixer.2 ⟨hp.2.1, fun y hy => ⟨hp.2.1, ?_⟩⟩
    have h5 := y.isValuation.opposite_snd α.property hu hu1 hp.1 hp.2.1 hp.2.2
    rw [hval y hy, add_zero] at h5
    simp only [h5, WithTop.coe_zero, le_refl]
  refine ⟨B.reflectionElement hp, ?_, ?_⟩
  · rw [B.coe_reflectionElement]
    exact (B.sharpFixer Ω).mul_mem ((B.sharpFixer Ω).mul_mem
      (B.apartment.rootFixer_le_sharpFixer ⟨_, hneg⟩ Ω hp1)
      (B.apartment.rootFixer_le_sharpFixer α Ω hfix))
      (B.apartment.rootFixer_le_sharpFixer ⟨_, hneg⟩ Ω hp2)
  · have heq := B.reflectionCoroot_eq_of_isCoroot hu hu1 hp hw
    simpa only [heq] using B.normalizerAffineEquiv_reflectionElement hu hu1 hp

/-- A normalizer element of H fixing finite Ω belongs to the sharp-fixer/kernel
join whenever its original apartment action belongs to the affine Weyl group. -/
theorem normalizer_mem_kernel_sup_sharpFixer
    (H : Subgroup (rationalPoints G))
    (hS : ∀ Ω : Set B.Apartment, B.sharpFixer Ω ≤ H)
    {Ω : Set B.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty)
    (n : normalizerPoints B.i) (hnH : (n : rationalPoints G) ∈ H)
    (hnW : B.apartment.normalizerAffineEquiv n ∈
      AffineRootSystem.affineWeylGroup B.affineRoots)
    (hfix : ∀ x ∈ Ω, n • x = x) :
    (n : rationalPoints G) ∈
      (H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker).map
        (normalizerPoints B.i).subtype ⊔ B.sharpFixer Ω := by
  classical
  have hΨ := B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    B.hasOppositeFactorPairs
  obtain ⟨z, hzfix, hzgen⟩ := AffineRootSystem.exists_generic_point hΨ hΩ.toFinset
    (hΩ.toFinset_nonempty.2 hne)
  let a : AffineRootSystem.affineWeylGroup B.affineRoots :=
    ⟨B.apartment.normalizerAffineEquiv n, hnW⟩
  have haz : (a : B.Apartment ≃ᵃ[ℝ] B.Apartment) z = z :=
    hzfix _ fun y hy => hfix y (hΩ.mem_toFinset.1 hy)
  have hcl := AffineRootSystem.mem_closure_pointReflections_of_apply_eq hΨ a haz
  have hle : Subgroup.closure (AffineRootSystem.pointReflections B.affineRoots z) ≤
      ((B.sharpFixer Ω).subgroupOf (normalizerPoints B.i)).map
        B.apartment.normalizerAffineEquiv := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨ψ, hψ, hψz, w, hw, rfl⟩
    obtain ⟨m, hm, hmeq⟩ := B.exists_sharpFixer_normalizer_eq_affineReflection hψ
      (fun y hy => hzgen ψ hψ hψz y (hΩ.mem_toFinset.2 hy)) hw
    exact ⟨m, Subgroup.mem_subgroupOf.2 hm, hmeq⟩
  obtain ⟨m, hm, hmeq⟩ := hle hcl
  have hmS : (m : rationalPoints G) ∈ B.sharpFixer Ω := hm
  have hk : m⁻¹ * n ∈
      H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker := by
    constructor
    · change ((m⁻¹ * n : normalizerPoints B.i) : rationalPoints G) ∈ H
      exact H.mul_mem (H.inv_mem (hS Ω hmS)) hnH
    · change B.apartment.normalizerAffineEquiv (m⁻¹ * n) = 1
      rw [map_mul, map_inv, hmeq]
      exact inv_mul_cancel _
  have hmul := (show (m : rationalPoints G) ∈
      (H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker).map
        (normalizerPoints B.i).subtype ⊔ B.sharpFixer Ω from
      (show B.sharpFixer Ω ≤
        (H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker).map
          (normalizerPoints B.i).subtype ⊔ B.sharpFixer Ω from le_sup_right) hmS)
  have hkP : ((m⁻¹ * n : normalizerPoints B.i) : rationalPoints G) ∈
      (H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker).map
        (normalizerPoints B.i).subtype ⊔ B.sharpFixer Ω :=
    (show
      (H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker).map
        (normalizerPoints B.i).subtype ≤
      (H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker).map
        (normalizerPoints B.i).subtype ⊔ B.sharpFixer Ω from le_sup_left)
      ⟨m⁻¹ * n, hk, rfl⟩
  have := (show Subgroup (rationalPoints G) from
    (H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker).map
      (normalizerPoints B.i).subtype ⊔ B.sharpFixer Ω).mul_mem hmul hkP
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using this

/-- Affine Weyl containment of N ∩ H supplies the precise generic normalizer premise. -/
theorem hasNormalizerSharpFixers_of_mem_affineWeylGroup
    (H : Subgroup (rationalPoints G))
    (hS : ∀ Ω : Set B.Apartment, B.sharpFixer Ω ≤ H)
    (hNW : ∀ n : normalizerPoints B.i, (n : rationalPoints G) ∈ H →
      B.apartment.normalizerAffineEquiv n ∈ AffineRootSystem.affineWeylGroup B.affineRoots) :
    B.apartment.HasNormalizerSharpFixers H
      (H.subgroupOf (normalizerPoints B.i) ⊓ B.apartment.normalizerAffineEquiv.ker) :=
  fun _ hΩ hne n hnH hfix =>
    B.normalizer_mem_kernel_sup_sharpFixer H hS hΩ hne n hnH (hNW n hnH) hfix

/-- The bounded whole-apartment comparison reduced only to ambient sharp containment
and affine Weyl containment of N ∩ H. -/
theorem subgroup_pointwiseFixer_eq_wholeApartment_sup_sharpFixer_of_mem_affineWeylGroup
    (H : Subgroup (rationalPoints G))
    (hS : ∀ Ω : Set B.Apartment, B.sharpFixer Ω ≤ H)
    (hNW : ∀ n : normalizerPoints B.i, (n : rationalPoints G) ∈ H →
      B.apartment.normalizerAffineEquiv n ∈ AffineRootSystem.affineWeylGroup B.affineRoots)
    {Ω : Set B.Apartment} (hne : Ω.Nonempty) (hb : B.IsBoundedSubset Ω) :
    H ⊓ B.pointwiseFixer (B.apartmentMap '' Ω) =
      (H ⊓ B.pointwiseFixer (B.apartmentMap '' Set.univ)) ⊔ B.sharpFixer Ω :=
  B.subgroup_pointwiseFixer_eq_wholeApartment_sup_sharpFixer_of_bounded H hS
    (B.hasNormalizerSharpFixers_of_mem_affineWeylGroup H hS hNW) hne hb

end IntegerValuationBuildingData

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom G.X.hom]
    (E : UnramifiedZeroDatum F G) (B : MaximalUnramified.BuildingData F G)

/-- The unramified bounded zero/sharp comparison, conditional only on the converse
normalizer affine Weyl containment. -/
theorem wholeApartmentZeroFixer_sup_sharpFixer_eq_of_mem_affineWeylGroup
    (hNW : ∀ n : normalizerPoints B.i, (n : rationalPoints G) ∈ E.zeroPoints →
      B.apartment.normalizerAffineEquiv n ∈ AffineRootSystem.affineWeylGroup B.affineRoots)
    {Ω : Set B.Apartment} (hne : Ω.Nonempty)
    (hb : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    E.zeroPoints ⊓ B.pointwiseFixer (B.apartmentMap '' Ω) =
      (E.zeroPoints ⊓ B.pointwiseFixer (B.apartmentMap '' Set.univ)) ⊔ B.sharpFixer Ω :=
  B.subgroup_pointwiseFixer_eq_wholeApartment_sup_sharpFixer_of_mem_affineWeylGroup
    E.zeroPoints (E.sharpFixer_le_zeroPoints B) hNW hne hb

/-- The bounded zero/sharp comparison follows from the explicit simply connected
normalizer assertion, with all other comparison inputs constructed. -/
theorem wholeApartmentZeroFixer_sup_sharpFixer_eq_of_simplyConnectedNormalizer
    (hsc : MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement.{u})
    {Ω : Set B.Apartment} (hne : Ω.Nonempty)
    (hb : ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    E.zeroPoints ⊓ B.pointwiseFixer (B.apartmentMap '' Ω) =
      (E.zeroPoints ⊓ B.pointwiseFixer (B.apartmentMap '' Set.univ)) ⊔ B.sharpFixer Ω :=
  E.wholeApartmentZeroFixer_sup_sharpFixer_eq_of_mem_affineWeylGroup B
    (E.normalizer_mem_affineWeylGroup_of_mem_zeroPoints B hsc) hne hb

end UnramifiedZeroDatum

end Langlands.Geometry.Building
