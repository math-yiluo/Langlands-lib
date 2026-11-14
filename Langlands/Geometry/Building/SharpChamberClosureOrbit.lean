import Langlands.Geometry.Building.ChamberClosureOrbit
import Langlands.Geometry.Building.IntegerValuationNormalizerSharpReduction

/-! # Chambers through a point form an orbit of the sharp-generated point fixer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- Products of reflections in affine roots vanishing at `p` are apartment actions of
normalizer points in `G(k)^♯_p`. -/
theorem closure_pointReflections_le_map_sharpFixer (p : B.Apartment) :
    Subgroup.closure (AffineRootSystem.pointReflections B.affineRoots p) ≤
      ((B.sharpFixer {p}).subgroupOf (normalizerPoints B.i)).map
        B.apartment.normalizerAffineEquiv := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨ψ, hψ, hψp, w, hw, rfl⟩
  obtain ⟨m, hm, hmeq⟩ := B.exists_sharpFixer_normalizer_eq_affineReflection hψ
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hψp) hw
  exact ⟨m, Subgroup.mem_subgroupOf.2 hm, hmeq⟩

/-- Two regular facets incident to the same apartment point are related by a normalizer
point that lies in the sharp fixer of that point. -/
theorem exists_sharpFixer_normalizer_fixing_facet
    {p x₀ x₁ : B.Apartment}
    (h₀ : AffineRootSystem.GalleryGeometry.IsRegular B.affineRoots x₀)
    (h₁ : AffineRootSystem.GalleryGeometry.IsRegular B.affineRoots x₁)
    (hp₀ : p ∈ AffineRootSystem.facetClosure B.affineRoots x₀)
    (hp₁ : p ∈ AffineRootSystem.facetClosure B.affineRoots x₁) :
    ∃ m : normalizerPoints B.i, (m : rationalPoints G) ∈ B.sharpFixer {p} ∧ m • p = p ∧
      (m • ·) '' AffineRootSystem.facet B.affineRoots x₀ =
        AffineRootSystem.facet B.affineRoots x₁ := by
  obtain ⟨w, hw, hwrel⟩ := AffineRootSystem.exists_facetRel_closure_pointReflections
    (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
      B.hasOppositeFactorPairs) h₀ h₁ hp₀ hp₁
  obtain ⟨m, hm, hmeq⟩ := B.closure_pointReflections_le_map_sharpFixer p hw
  refine ⟨m, Subgroup.mem_subgroupOf.1 hm, ?_, ?_⟩
  · change B.apartment.normalizerAffineEquiv m p = p
    rw [hmeq]
    exact AffineRootSystem.apply_eq_of_mem_closure_pointReflections hw
  · change (B.apartment.normalizerAffineEquiv m : B.Apartment → B.Apartment) ''
      AffineRootSystem.facet B.affineRoots x₀ =
        AffineRootSystem.facet B.affineRoots x₁
    rw [AffineRootSystem.image_facet
      (B.apartment.normalizerAffineEquiv_mem_rootStabilizer m)]
    apply AffineRootSystem.facet_eq_facet_iff.mpr
    change AffineRootSystem.facetRel B.affineRoots
      (B.apartment.normalizerAffineEquiv m x₀) x₁
    rw [hmeq]
    exact hwrel

/-- Chambers with a closure presentation through `y` are related by an element fixing `y`
that is a `G(k)`-conjugate of a point sharp fixer element. -/
theorem exists_conj_sharpFixer_smul_chamber_eq
    {y : B.ReducedBuilding} {Y₀ Y₁ : Set B.ReducedBuilding}
    (hY₀ : B.HasChamberClosurePresentation Y₀ y)
    (hY₁ : B.HasChamberClosurePresentation Y₁ y) :
    ∃ (h : rationalPoints G) (a : B.Apartment) (s : rationalPoints G),
      s ∈ B.sharpFixer {a} ∧ (h * s * h⁻¹) • y = y ∧
        ((h * s * h⁻¹) • ·) '' Y₀ = Y₁ := by
  obtain ⟨g₀, x₀, a₀, h₀, rfl, ha₀, hy₀⟩ := hY₀
  obtain ⟨g₁, x₁, a₁, h₁, rfl, ha₁, hy₁⟩ := hY₁
  have heq : (g₀⁻¹ * g₁) • B.apartmentMap a₁ = B.apartmentMap a₀ := by
    rw [mul_smul, hy₁, ← hy₀, inv_smul_smul]
  have heq' :
      ApartmentQuotient.mk B.apartment.sharpFixerFamily (g₀⁻¹ * g₁, a₁) =
        ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, a₀) := by
    have h :
        ApartmentQuotient.mk B.apartment.sharpFixerFamily ((g₀⁻¹ * g₁) * 1, a₁) =
          ApartmentQuotient.mk B.apartment.sharpFixerFamily (1, a₀) := heq
    simpa only [mul_one] using h
  obtain ⟨n, hna, hs⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff B.apartment.sharpFixerFamily
      (g₀⁻¹ * g₁) 1 a₁ a₀).mp heq'
  have hs' : (g₀⁻¹ * g₁)⁻¹ * 1 * (n : rationalPoints G) ∈ B.sharpFixer {a₁} := hs
  have hnroot := B.apartment.normalizerAffineEquiv_mem_rootStabilizer n
  have hnregular :
      AffineRootSystem.GalleryGeometry.IsRegular B.affineRoots (n • x₁) :=
    AffineRootSystem.GalleryGeometry.IsRegular.apply hnroot h₁
  have hnclosure : a₀ ∈ AffineRootSystem.facetClosure B.affineRoots (n • x₁) := by
    rw [← hna]
    exact (AffineRootSystem.mem_facetClosure_apply_iff hnroot a₁ x₁).mpr ha₁
  obtain ⟨m, hmS, hmfix, hmimage⟩ :=
    B.exists_sharpFixer_normalizer_fixing_facet h₀ hnregular ha₀ hnclosure
  have hconj : (n : rationalPoints G)⁻¹ * (m : rationalPoints G) * (n : rationalPoints G) ∈
      B.sharpFixer {a₁} := by
    have h := B.apartment.sharpFixer_le_comap n⁻¹ {a₀} hmS
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Set.smul_set_singleton, ← hna, inv_smul_smul] at h
    simpa only [Subgroup.coe_inv, inv_inv] using h
  let s := (n : rationalPoints G)⁻¹ * (m : rationalPoints G) * (n : rationalPoints G) *
    ((g₀⁻¹ * g₁)⁻¹ * 1 * (n : rationalPoints G))⁻¹
  have hsS : s ∈ B.sharpFixer {a₁} :=
    (B.sharpFixer {a₁}).mul_mem hconj ((B.sharpFixer {a₁}).inv_mem hs')
  have hg : g₁ * s * g₁⁻¹ =
      g₁ * (n : rationalPoints G)⁻¹ * (m : rationalPoints G) * g₀⁻¹ := by
    simp only [s]
    group
  refine ⟨g₁, a₁, s, hsS, ?_, ?_⟩
  · have hbase : g₀⁻¹ • y = B.apartmentMap a₀ := by
      rw [← hy₀, inv_smul_smul]
    rw [hg]
    simp only [mul_smul, hbase]
    rw [B.normalizer_smul_apartmentMap, hmfix, ← hna,
      ← B.normalizer_smul_apartmentMap, inv_smul_smul, hy₁]
  · rw [hg, Set.image_image]
    calc
      (fun x => (g₁ * (n : rationalPoints G)⁻¹ * (m : rationalPoints G) * g₀⁻¹) •
          (g₀ • B.apartmentMap x)) ''
          AffineRootSystem.facet B.affineRoots x₀ =
        (fun x => g₁ • ((n : rationalPoints G)⁻¹ • B.apartmentMap x)) ''
          ((m • ·) '' AffineRootSystem.facet B.affineRoots x₀) := by
            rw [Set.image_image]
            congr 1
            funext x
            rw [← B.normalizer_smul_apartmentMap]
            simp only [mul_smul, inv_smul_smul]
      _ = (fun x => g₁ • ((n : rationalPoints G)⁻¹ • B.apartmentMap x)) ''
          AffineRootSystem.facet B.affineRoots (n • x₁) := by rw [hmimage]
      _ = (fun x => g₁ • B.apartmentMap x) ''
          AffineRootSystem.facet B.affineRoots x₁ := by
            change (fun x => g₁ • ((n : rationalPoints G)⁻¹ • B.apartmentMap x)) ''
                AffineRootSystem.facet B.affineRoots
                  (B.apartment.normalizerAffineEquiv n x₁) = _
            rw [← AffineRootSystem.image_facet hnroot x₁, Set.image_image]
            congr 1
            funext x
            change g₁ • ((n : rationalPoints G)⁻¹ • B.apartmentMap (n • x)) =
              g₁ • B.apartmentMap x
            rw [← B.normalizer_smul_apartmentMap, inv_smul_smul]

/-- Every normal subgroup containing all point sharp fixers acts transitively, through
elements fixing `y`, on the chambers with a closure presentation through `y`. -/
theorem exists_normal_fixer_smul_chamber_eq
    (H : Subgroup (rationalPoints G)) (hHn : H.Normal)
    (hH : ∀ a : B.Apartment, B.sharpFixer {a} ≤ H)
    {y : B.ReducedBuilding} {Y₀ Y₁ : Set B.ReducedBuilding}
    (hY₀ : B.HasChamberClosurePresentation Y₀ y)
    (hY₁ : B.HasChamberClosurePresentation Y₁ y) :
    ∃ g ∈ H ⊓ B.fixer y, (g • ·) '' Y₀ = Y₁ := by
  obtain ⟨h, a, s, hs, hfix, himage⟩ := B.exists_conj_sharpFixer_smul_chamber_eq hY₀ hY₁
  exact ⟨h * s * h⁻¹, ⟨hHn.conj_mem s (hH a hs) h, B.mem_fixer.mpr hfix⟩, himage⟩

end IntegerValuationBuildingData

/-- For every supplied integer-valued building, every normal subgroup `H` of `G(k)` containing
the sharp fixer `G(k)^♯_a` of every apartment point `a` satisfies: `H ∩ G(k)_y` acts
transitively on the chambers with an exact closure presentation through `y`. -/
def IntegerValuationNormalFixerChamberOrbitStatement : Prop :=
  ∀ (k : Type u) [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G) (H : Subgroup (rationalPoints G)),
    H.Normal → (∀ a : B.Apartment, B.sharpFixer {a} ≤ H) →
    ∀ (y : B.ReducedBuilding) (Y₀ Y₁ : Set B.ReducedBuilding),
      B.HasChamberClosurePresentation Y₀ y →
      B.HasChamberClosurePresentation Y₁ y →
      ∃ g ∈ H ⊓ B.fixer y, (g • ·) '' Y₀ = Y₁

/-- The normal-subgroup chamber orbit statement is proved without extra building axioms. -/
theorem integerValuationNormalFixerChamberOrbit :
    IntegerValuationNormalFixerChamberOrbitStatement.{u} := by
  intro k _ v G _ B H hHn hH y Y₀ Y₁ hY₀ hY₁
  exact B.exists_normal_fixer_smul_chamber_eq H hHn hH hY₀ hY₁

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom] (E : UnramifiedZeroDatum F H)

/-- Over the maximal unramified field, `G(K)^0 ∩ G(K)_y` acts transitively on the chambers
with a closure presentation through `y`. -/
theorem exists_zeroPoints_fixer_smul_chamber_eq (B : MaximalUnramified.BuildingData F H)
    {y : B.ReducedBuilding} {Y₀ Y₁ : Set B.ReducedBuilding}
    (hY₀ : B.HasChamberClosurePresentation Y₀ y)
    (hY₁ : B.HasChamberClosurePresentation Y₁ y) :
    ∃ g ∈ E.zeroPoints ⊓ B.fixer y, (g • ·) '' Y₀ = Y₁ :=
  B.exists_normal_fixer_smul_chamber_eq E.zeroPoints E.normal_zeroPoints
    (fun a => E.sharpFixer_le_zeroPoints B {a}) hY₀ hY₁

end UnramifiedZeroDatum

end Langlands.Geometry.Building
