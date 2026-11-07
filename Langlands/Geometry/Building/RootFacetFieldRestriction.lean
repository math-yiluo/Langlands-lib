import Langlands.Geometry.Building.RootAffineFieldRestriction
import Langlands.Geometry.Building.AffineRootDoubling

/-! # Ordinary walls and facets under actual field restriction -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.KPApartmentData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

/-- Original opposite pairs exclude quadruple roots after literal field extension. -/
theorem no_quadruple_root_fieldExtend
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i) :
    ∀ a ∈ relativeRoots (T := S_K) i_K,
      (4 : ℕ) • a ∉ relativeRoots (T := S_K) i_K := by
  intro a ha
  obtain ⟨c, rfl⟩ := (characterLattice.baseChangeEquiv b S hS).surjective a
  have hc := (mem_roots_baseChange_iff (K := K) G S hS i c).mp ha
  intro h4c
  apply no_quadruple_root_of_oppositePairs hS hE c hc
  apply (mem_roots_baseChange_iff (K := K) G S hS i ((4 : ℕ) • c)).mp
  simpa only [characterLattice.baseChangeEquiv_apply, map_nsmul, relativeRoots] using h4c

variable (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
  (ω : Kˣ →* Multiplicative ℝ)
  (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)

/-- Choose an actual ordinary upstairs root with the same wall and signs as
the extension of an original extended root. -/
def fieldExtendedOrdinaryAffineRoot
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ)
    (hψ : ψ ∈ (fieldRestrict i hS hE ω hω D).extendedAffineRoots) :
    D.affineRoots :=
  D.ordinaryAffineRootForExtended (no_quadruple_root_fieldExtend i hS hE)
    (fieldExtendAffineFunctional i hS hE ω hω D ψ)
    (fieldExtendAffineFunctional_mem_extendedAffineRoots i hS hE ω hω D ψ hψ)

/-- The selected root is the actual extended functional or twice that functional. -/
theorem fieldExtendedOrdinaryAffineRoot_eq_or_eq_two_smul
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ)
    (hψ : ψ ∈ (fieldRestrict i hS hE ω hω D).extendedAffineRoots) :
    (fieldExtendedOrdinaryAffineRoot i hS hE ω hω D ψ hψ :
        D.Apartment →ᵃ[ℝ] ℝ) =
        fieldExtendAffineFunctional i hS hE ω hω D ψ ∨
      (fieldExtendedOrdinaryAffineRoot i hS hE ω hω D ψ hψ :
        D.Apartment →ᵃ[ℝ] ℝ) =
        (2 : ℝ) • fieldExtendAffineFunctional i hS hE ω hω D ψ :=
  D.ordinaryAffineRootForExtended_eq_or_eq_two_smul
    (no_quadruple_root_fieldExtend i hS hE) _ _

/-- Evaluation of the selected ordinary root has exactly the original sign. -/
theorem fieldExtendedOrdinaryAffineRoot_sign
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ)
    (hψ : ψ ∈ (fieldRestrict i hS hE ω hω D).extendedAffineRoots)
    (x : D.Apartment) :
    SignType.sign ((fieldExtendedOrdinaryAffineRoot i hS hE ω hω D ψ hψ :
        D.Apartment →ᵃ[ℝ] ℝ) x) =
      SignType.sign (ψ (fieldRestrictPoint i hS hE ω hω D x)) :=
  D.ordinaryAffineRootForExtended_sign
    (no_quadruple_root_fieldExtend i hS hE) _ _ x

/-- The full upstairs ordinary wall is the inverse image of the original wall. -/
theorem fieldExtendedOrdinaryAffineRoot_hyperplane
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ)
    (hψ : ψ ∈ (fieldRestrict i hS hE ω hω D).extendedAffineRoots) :
    AffineRootSystem.hyperplane (fieldExtendedOrdinaryAffineRoot i hS hE ω hω D ψ hψ) =
      (AffineRootSystem.hyperplane ψ).comap
        (fieldRestrictAffineEquiv i hS hE ω hω D).toAffineMap := by
  rw [fieldExtendedOrdinaryAffineRoot,
    D.ordinaryAffineRootForExtended_hyperplane]
  ext x
  rfl

/-- Every upstairs ordinary-root sign facet refines an original extended-root
sign facet. No apartment-axiom package is needed. -/
theorem facetRel_affineRoots_fieldRestrict_extended
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    {x y : D.Apartment}
    (hxy : AffineRootSystem.facetRel D.affineRoots x y) :
    AffineRootSystem.facetRel (fieldRestrict i hS hE ω hω D).extendedAffineRoots
      (fieldRestrictPoint i hS hE ω hω D x)
      (fieldRestrictPoint i hS hE ω hω D y) := by
  intro ψ hψ
  have h := hxy (fieldExtendedOrdinaryAffineRoot i hS hE ω hω D ψ hψ)
    (fieldExtendedOrdinaryAffineRoot i hS hE ω hω D ψ hψ).property
  simpa only [fieldExtendedOrdinaryAffineRoot_sign] using h

/-- Actual field restriction preserves the ordinary-root facet relation. -/
theorem facetRel_affineRoots_fieldRestrict
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    {x y : D.Apartment}
    (hxy : AffineRootSystem.facetRel D.affineRoots x y) :
    AffineRootSystem.facetRel (fieldRestrict i hS hE ω hω D).affineRoots
      (fieldRestrictPoint i hS hE ω hω D x)
      (fieldRestrictPoint i hS hE ω hω D y) := by
  intro ψ hψ
  exact facetRel_affineRoots_fieldRestrict_extended i hS hE ω hω D hxy ψ
    ((fieldRestrict i hS hE ω hω D).affineRoots_subset_extendedAffineRoots hψ)

/-- The image of an upstairs ordinary facet lies in its original ordinary facet. -/
theorem image_facet_affineRoots_fieldRestrict_subset
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : D.Apartment) :
    fieldRestrictPoint i hS hE ω hω D '' AffineRootSystem.facet D.affineRoots x ⊆
      AffineRootSystem.facet (fieldRestrict i hS hE ω hω D).affineRoots
        (fieldRestrictPoint i hS hE ω hω D x) := by
  rintro _ ⟨y, hy, rfl⟩
  exact facetRel_affineRoots_fieldRestrict i hS hE ω hω D hy

/-- Weak sign conditions for ordinary roots restrict to those for every
original extended root. -/
theorem mem_facetClosure_affineRoots_fieldRestrict_extended
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    {x y : D.Apartment}
    (hy : y ∈ AffineRootSystem.facetClosure D.affineRoots x) :
    fieldRestrictPoint i hS hE ω hω D y ∈
      AffineRootSystem.facetClosure (fieldRestrict i hS hE ω hω D).extendedAffineRoots
        (fieldRestrictPoint i hS hE ω hω D x) := by
  intro ψ hψ
  have h := hy (fieldExtendedOrdinaryAffineRoot i hS hE ω hω D ψ hψ)
    (fieldExtendedOrdinaryAffineRoot i hS hE ω hω D ψ hψ).property
  simpa only [fieldExtendedOrdinaryAffineRoot_sign] using h

/-- The entire upstairs ordinary facet closure maps into the original one. -/
theorem image_facetClosure_affineRoots_fieldRestrict_subset
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : D.Apartment) :
    fieldRestrictPoint i hS hE ω hω D ''
        AffineRootSystem.facetClosure D.affineRoots x ⊆
      AffineRootSystem.facetClosure (fieldRestrict i hS hE ω hω D).affineRoots
        (fieldRestrictPoint i hS hE ω hω D x) := by
  rintro _ ⟨y, hy, rfl⟩ ψ hψ
  exact mem_facetClosure_affineRoots_fieldRestrict_extended i hS hE ω hω D hy ψ
    ((fieldRestrict i hS hE ω hω D).affineRoots_subset_extendedAffineRoots hψ)

/-- If the original facet is a vertex, its unique upstairs preimage is also a vertex. -/
theorem isVertex_of_fieldRestrictPoint
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : D.Apartment)
    (hx : AffineRootSystem.IsVertex (fieldRestrict i hS hE ω hω D).affineRoots
      (fieldRestrictPoint i hS hE ω hω D x)) :
    AffineRootSystem.IsVertex D.affineRoots x := by
  ext y
  constructor
  · intro hy
    have hy' : fieldRestrictPoint i hS hE ω hω D y ∈
        AffineRootSystem.facet (fieldRestrict i hS hE ω hω D).affineRoots
          (fieldRestrictPoint i hS hE ω hω D x) :=
      facetRel_affineRoots_fieldRestrict i hS hE ω hω D hy
    rw [hx, Set.mem_singleton_iff] at hy'
    exact Set.mem_singleton_iff.mpr (fieldRestrictPoint_injective i hS hE ω hω D hy')
  · rintro rfl
    exact AffineRootSystem.mem_facet_self D.affineRoots _

end Langlands.Geometry.Building.KPApartmentData
