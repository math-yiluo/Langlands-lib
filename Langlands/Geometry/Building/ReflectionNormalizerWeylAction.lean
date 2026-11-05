import Langlands.Geometry.Building.NormalizerAffineRootAction
import Langlands.Geometry.Building.AffineChamberWallComparisonProof
import Langlands.Geometry.Building.AffineWeylFacetFixing

/-! # The actual reflection-normalizer Weyl action from explicit AS 4 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

variable (h4 : ∀ ψ ∈ B.apartment.extendedAffineRoots,
  ψ ∈ B.affineRoots ∨ (2 : ℝ) • ψ ∈ B.affineRoots)

include h4

/-- Explicit AS 4 suffices for the affine Weyl membership of each actual
opposite-pair reflection; no other apartment axiom is used. -/
theorem normalizerAffineEquiv_reflectionElement_mem_affineWeylGroup_of_AS4
    {a : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p) :
    B.apartment.normalizerAffineEquiv (B.reflectionElement hp) ∈
      AffineRootSystem.affineWeylGroup B.affineRoots := by
  have hψ : B.reflectionFunctional a g ∈ B.apartment.extendedAffineRoots := by
    rw [← B.reflectionAffineRoots_eq]
    exact ⟨a, g, hg, hg1, rfl⟩
  have hv := B.isCoroot_reflectionCoroot_without_apartment_axioms hg hg1 hp
  rw [B.normalizerAffineEquiv_reflectionElement hg hg1 hp]
  rcases h4 _ hψ with hm | hm
  · exact AffineRootSystem.affineReflection_mem_affineWeylGroup hm hv
  · have hv2 := hv.smul (by norm_num : (2 : ℝ) ≠ 0)
    rw [← AffineRootSystem.affineReflection_smul _ hv.1
      (by norm_num : (2 : ℝ) ≠ 0) hv2.1]
    exact AffineRootSystem.affineReflection_mem_affineWeylGroup hm hv2

/-- AS 4 puts the entire actual reflection-generated image in the affine
Weyl group, without AS 5 or an affine-root-system hypothesis. -/
theorem reflectionNormalizer_map_le_affineWeylGroup_of_AS4 :
    B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv ≤
      AffineRootSystem.affineWeylGroup B.affineRoots := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).2 ?_
  rintro n ⟨a, g, hg, hg1, p, hp, rfl⟩
  exact B.normalizerAffineEquiv_reflectionElement_mem_affineWeylGroup_of_AS4
    h4 hg hg1 hp

/-- The actual apartment action of the reflection-generated normalizer,
restricted to the affine Weyl group using only explicit AS 4. -/
def reflectionWeylActionOfAS4 :
    B.reflectionNormalizer →* AffineRootSystem.affineWeylGroup B.affineRoots where
  toFun n := ⟨B.apartment.normalizerAffineEquiv n.val,
    B.reflectionNormalizer_map_le_affineWeylGroup_of_AS4 h4
      ⟨n.val, n.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one B.apartment.normalizerAffineEquiv)
  map_mul' n m := Subtype.ext (map_mul B.apartment.normalizerAffineEquiv n.val m.val)

@[simp]
theorem reflectionWeylActionOfAS4_coe (n : B.reflectionNormalizer) :
    (B.reflectionWeylActionOfAS4 h4 n : B.Apartment ≃ᵃ[ℝ] B.Apartment) =
      B.apartment.normalizerAffineEquiv n.val :=
  rfl

@[simp]
theorem reflectionWeylActionOfAS4_apply (n : B.reflectionNormalizer) (x : B.Apartment) :
    (B.reflectionWeylActionOfAS4 h4 n : B.Apartment ≃ᵃ[ℝ] B.Apartment) x =
      n.val • x :=
  rfl

omit h4 in
/-- Local arrangement geometry identifies the actual integral coroot with any
coroot of the same point functional. -/
theorem reflectionCoroot_eq_of_isCoroot_of_locallyFinite
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots)
    {a : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional a g) v) :
    B.reflectionCoroot hg hg1 hp = v :=
  AffineRootSystem.GalleryGeometry.isCoroot_unique hΨ
    (B.isCoroot_reflectionCoroot_without_apartment_axioms hg hg1 hp) hv

omit h4 in
/-- The actual opposite-pair action is the reflection defined by any coroot
of its point functional, under local arrangement geometry alone. -/
theorem normalizerAffineEquiv_reflectionElement_eq_of_locallyFinite
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots)
    {a : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional a g) v) :
    B.apartment.normalizerAffineEquiv (B.reflectionElement hp) =
      AffineRootSystem.affineReflection (B.reflectionFunctional a g) hv.1 := by
  have hv' := B.reflectionCoroot_eq_of_isCoroot_of_locallyFinite hΨ hg hg1 hp hv
  simpa only [hv'] using B.normalizerAffineEquiv_reflectionElement hg hg1 hp

omit h4 in
/-- Opposite-pair existence realizes all affine Weyl generators using only
local reflection-arrangement geometry. -/
theorem affineWeylGroup_le_reflectionNormalizer_map_of_locallyFinite
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    AffineRootSystem.affineWeylGroup B.affineRoots ≤
      B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv := by
  refine (Subgroup.closure_le _).2 ?_
  rintro e ⟨ψ, hψ, v, hv, rfl⟩
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ'
  obtain ⟨p, hp⟩ := hF a a.property g hg hg1
  exact ⟨B.reflectionElement hp,
    B.reflectionElement_mem_reflectionNormalizer hg hg1 hp,
    B.normalizerAffineEquiv_reflectionElement_eq_of_locallyFinite hΨ hg hg1 hp hv⟩

/-- The actual reflection-generated image is exactly the affine Weyl group
under explicit AS 4, local arrangement geometry and opposite-pair existence. -/
theorem reflectionNormalizer_map_eq_affineWeylGroup_of_AS4
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  le_antisymm (B.reflectionNormalizer_map_le_affineWeylGroup_of_AS4 h4)
    (B.affineWeylGroup_le_reflectionNormalizer_map_of_locallyFinite hΨ hF)

/-- The action constructed from AS 4 is surjective when local arrangement
geometry and actual opposite-pair existence are supplied. -/
theorem reflectionWeylActionOfAS4_surjective
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    Function.Surjective (B.reflectionWeylActionOfAS4 h4) := by
  intro w
  have hw : w.val ∈ B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv := by
    rw [B.reflectionNormalizer_map_eq_affineWeylGroup_of_AS4 h4 hΨ hF]
    exact w.property
  obtain ⟨n, hn, heq⟩ := hw
  exact ⟨⟨n, hn⟩, Subtype.ext heq⟩

/-- Under these explicit hypotheses, the full preimage of the affine Weyl
group is precisely the reflection-normalizer enlarged by the action kernel. -/
theorem comap_affineWeylGroup_eq_reflectionNormalizer_sup_ker_of_AS4
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    (AffineRootSystem.affineWeylGroup B.affineRoots).comap
        B.apartment.normalizerAffineEquiv =
      B.reflectionNormalizer ⊔ B.apartment.normalizerAffineEquiv.ker := by
  rw [← B.reflectionNormalizer_map_eq_affineWeylGroup_of_AS4 h4 hΨ hF,
    Subgroup.comap_map_eq]

/-- A reflection-normalizer element preserving a facet fixes it pointwise.
Opposite-pair existence is not needed for this implication. -/
theorem reflectionNormalizer_facet_fixing_of_AS4
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (n : B.reflectionNormalizer) (hfix : (fun x : B.Apartment => n.val • x) '' Fa = Fa) :
    ∀ x ∈ Fa, n.val • x = x :=
  AffineRootSystem.affineWeyl_facet_fixing hΨ hFa
    (B.reflectionWeylActionOfAS4 h4 n) hfix

end Langlands.Geometry.Building.ValuationBuildingData
