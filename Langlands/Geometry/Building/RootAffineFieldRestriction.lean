import Langlands.Geometry.Building.RootApartmentFieldDescent
import Langlands.Geometry.Building.AffineFacetTransport

/-! # Actual affine root groups under literal field restriction -/

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

variable (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
  (ω : Kˣ →* Multiplicative ℝ)
  (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)

/-- Extend an original affine functional by actual apartment restriction. -/
def fieldExtendAffineFunctional
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ) :
    D.Apartment →ᵃ[ℝ] ℝ :=
  ψ.comp (fieldRestrictAffineEquiv i hS hE ω hω D).toAffineMap

@[simp] theorem fieldExtendAffineFunctional_apply
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ) (x : D.Apartment) :
    fieldExtendAffineFunctional i hS hE ω hω D ψ x =
      ψ (fieldRestrictPoint i hS hE ω hω D x) := rfl

/-- The construction is the existing inverse-precomposition transport along
the inverse actual restriction equivalence. -/
theorem fieldExtendAffineFunctional_eq_transport
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ) :
    fieldExtendAffineFunctional i hS hE ω hω D ψ =
      AffineRootSystem.affineFunctionalTransport
        (fieldRestrictAffineEquiv i hS hE ω hω D).symm ψ := by
  ext x
  rfl

/-- The derivative is the actual base change of the original root form. -/
theorem fieldExtendAffineFunctional_linear
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (α : relativeRoots i) (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ)
    (hψ : ψ.linear = rootForm i α) :
    (fieldExtendAffineFunctional i hS hE ω hω D ψ).linear =
      rootForm (S := S_K) i_K (rootsBaseChangeEquiv (K := K) G S hS i α) := by
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (splitTranslationBaseChange (K := K) hS i).surjective v
  change ψ.linear ((splitTranslationBaseChange (K := K) hS i).symm
    (splitTranslationBaseChange (K := K) hS i w)) = _
  rw [LinearEquiv.symm_apply_apply, hψ, rootForm_splitTranslationBaseChange]

@[simp] theorem fieldExtendAffineFunctional_add_const
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ) (c : ℝ) :
    fieldExtendAffineFunctional i hS hE ω hω D
        (ψ + AffineMap.const ℝ (fieldRestrict i hS hE ω hω D).Apartment c) =
      fieldExtendAffineFunctional i hS hE ω hω D ψ +
        AffineMap.const ℝ D.Apartment c := by
  ext x
  rfl

/-- Affine root groups are exact scalar-extension preimages for every
nonzero character; no derivative assumption is needed. -/
theorem affineRootGroup_fieldRestrict
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (a : characterLattice S) (ha : a ≠ 0)
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ) :
    (fieldRestrict i hS hE ω hω D).affineRootGroup a ψ =
      (D.affineRootGroup (characterLattice.baseChange b S a)
        (fieldExtendAffineFunctional i hS hE ω hω D ψ)).comap
          (rationalExtend k K G) := by
  ext g
  simp only [affineRootGroup, Subgroup.mem_comap, Subgroup.mem_iInf]
  constructor
  · intro hg x
    have hx := hg (fieldRestrictPoint i hS hE ω hω D x)
    rwa [filtration_fieldRestrictPoint i hS hE ω hω D x a ha] at hx
  · intro hg x
    obtain ⟨y, rfl⟩ := fieldRestrictPoint_surjective i hS hE ω hω D x
    rw [filtration_fieldRestrictPoint i hS hE ω hω D y a ha]
    exact hg y

/-- Strict affine root groups have the same exact preimage formula. The
positive constant witnessing membership is retained unchanged. -/
theorem affineRootGroupPlus_fieldRestrict
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (a : characterLattice S) (ha : a ≠ 0)
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ) :
    (fieldRestrict i hS hE ω hω D).affineRootGroupPlus a ψ =
      (D.affineRootGroupPlus (characterLattice.baseChange b S a)
        (fieldExtendAffineFunctional i hS hE ω hω D ψ)).comap
          (rationalExtend k K G) := by
  ext g
  change g ∈ (fieldRestrict i hS hE ω hω D).affineRootGroupPlus a ψ ↔
    rationalExtend k K G g ∈ D.affineRootGroupPlus
      (characterLattice.baseChange b S a) (fieldExtendAffineFunctional i hS hE ω hω D ψ)
  rw [mem_affineRootGroupPlus, mem_affineRootGroupPlus]
  constructor
  · rintro ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    rw [affineRootGroup_fieldRestrict i hS hE ω hω D a ha,
      fieldExtendAffineFunctional_add_const] at hg
    exact hg
  · rintro ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    rw [affineRootGroup_fieldRestrict i hS hE ω hω D a ha,
      fieldExtendAffineFunctional_add_const]
    exact hg

/-- Every extended affine root downstairs remains an extended affine root
upstairs under the actual affine comparison. -/
theorem fieldExtendAffineFunctional_mem_extendedAffineRoots
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ)
    (hψ : ψ ∈ (fieldRestrict i hS hE ω hω D).extendedAffineRoots) :
    fieldExtendAffineFunctional i hS hE ω hω D ψ ∈ D.extendedAffineRoots := by
  obtain ⟨α, hlin, hne⟩ := hψ
  refine ⟨rootsBaseChangeEquiv (K := K) G S hS i α,
    fieldExtendAffineFunctional_linear i hS hE ω hω D α ψ hlin, ?_⟩
  intro heq
  apply hne
  rw [affineRootGroupPlus_fieldRestrict i hS hE ω hω D α.val α.property.1,
    affineRootGroup_fieldRestrict i hS hE ω hω D α.val α.property.1]
  exact congrArg (fun H : Subgroup (rationalPoints G_K) =>
    H.comap (rationalExtend k K G)) heq

/-- The transported original extended root arrangement is contained in the
upstairs arrangement; equality of arrangements is not asserted. -/
theorem transported_extendedAffineRoots_subset
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    AffineRootSystem.transportedRoots (fieldRestrictAffineEquiv i hS hE ω hω D).symm
        (fieldRestrict i hS hE ω hω D).extendedAffineRoots ⊆
      D.extendedAffineRoots := by
  rintro _ ⟨ψ, hψ, rfl⟩
  rw [← fieldExtendAffineFunctional_eq_transport]
  exact fieldExtendAffineFunctional_mem_extendedAffineRoots i hS hE ω hω D ψ hψ

/-- Equality of all upstairs extended-root signs implies equality of all
original extended-root signs after actual restriction. -/
theorem facetRel_extendedAffineRoots_fieldRestrict
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    {x y : D.Apartment}
    (hxy : AffineRootSystem.facetRel D.extendedAffineRoots x y) :
    AffineRootSystem.facetRel (fieldRestrict i hS hE ω hω D).extendedAffineRoots
      (fieldRestrictPoint i hS hE ω hω D x)
      (fieldRestrictPoint i hS hE ω hω D y) := by
  intro ψ hψ
  exact hxy (fieldExtendAffineFunctional i hS hE ω hω D ψ)
    (fieldExtendAffineFunctional_mem_extendedAffineRoots i hS hE ω hω D ψ hψ)

/-- The image of an upstairs sign facet lies in the original sign facet
through the restricted point. -/
theorem image_facet_extendedAffineRoots_fieldRestrict_subset
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : D.Apartment) :
    fieldRestrictPoint i hS hE ω hω D '' AffineRootSystem.facet D.extendedAffineRoots x ⊆
      AffineRootSystem.facet (fieldRestrict i hS hE ω hω D).extendedAffineRoots
        (fieldRestrictPoint i hS hE ω hω D x) := by
  rintro _ ⟨y, hy, rfl⟩
  exact facetRel_extendedAffineRoots_fieldRestrict i hS hE ω hω D hy

end Langlands.Geometry.Building.KPApartmentData
