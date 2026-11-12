import Langlands.Geometry.Building.ValuationBuildingChartIso
import Langlands.Geometry.Building.RootBuildingFieldExtension
import Langlands.Geometry.Building.RootAffineFieldRestriction

/-!
# Field restriction of apartment data as a chart isomorphism

For a field extension `K / k` whose rational-point extension `G(k) → G(K)` is bijective and
reflects the normalizer of the torus (for instance an isomorphism of fields), the literal field
restriction of apartment data `D` for `i_K` is related to `D` by a chart isomorphism along the
rational-point extension.
-/

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

open scoped Pointwise in
/-- Under a bijective homomorphism, `A ⊆ B * C` holds for subgroups exactly when it holds for
their preimages. -/
theorem coe_comap_subset_mul_iff {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Bijective f) (A B C : Subgroup N) :
    ((A.comap f : Set M) ⊆ (B.comap f : Set M) * (C.comap f : Set M)) ↔
      ((A : Set N) ⊆ (B : Set N) * (C : Set N)) := by
  constructor
  · intro h a ha
    obtain ⟨m, rfl⟩ := hf.2 a
    obtain ⟨p, hp, q, hq, hpq⟩ := h (show m ∈ A.comap f from ha)
    exact ⟨f p, hp, f q, hq, by rw [← hpq]; exact (map_mul f p q).symm⟩
  · intro h m hm
    obtain ⟨p, hp, q, hq, hpq⟩ := h (show f m ∈ A from hm)
    obtain ⟨p', rfl⟩ := hf.2 p
    obtain ⟨q', rfl⟩ := hf.2 q
    exact ⟨p', hp, q', hq, hf.1 (by rw [map_mul]; exact hpq)⟩

/-- Preimages along a bijective homomorphism commute with suprema of subgroups. -/
theorem comap_iSup_of_bijective {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Bijective f) {J : Sort*} (H : J → Subgroup N) :
    (⨆ a, H a).comap f = ⨆ a, (H a).comap f := by
  let θ : M ≃* N := MulEquiv.ofBijective f hf
  have hθ : ∀ H : Subgroup N, H.comap f = H.map θ.symm.toMonoidHom := fun H =>
    Subgroup.comap_equiv_eq_map_symm θ H
  rw [hθ, Subgroup.map_iSup]
  exact iSup_congr fun a => (hθ (H a)).symm

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
  (hθ : Function.Bijective (rationalExtend k K G))

include hθ

/-- For a bijective rational-point extension, the sharp fixer of a restricted point is the exact
preimage of the upstairs sharp fixer at the extended point. -/
theorem sharpFixer_fieldRestrict_eq
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : (fieldRestrict i hS hE ω hω D).Apartment) :
    (fieldRestrict i hS hE ω hω D).sharpFixer {x} =
      (D.sharpFixer {fieldExtendPoint i hS hE ω hω D x}).comap (rationalExtend k K G) := by
  change (⨆ a : relativeRoots i, (fieldRestrict i hS hE ω hω D).rootFixer a {x}) =
    (⨆ β : relativeRoots (T := S_K) i_K,
      D.rootFixer β {fieldExtendPoint i hS hE ω hω D x}).comap (rationalExtend k K G)
  rw [comap_iSup_of_bijective _ hθ]
  refine (iSup_congr fun a : relativeRoots i => ?_).trans
    ((rootsBaseChangeEquiv (K := K) G S hS i).surjective.iSup_comp
      (fun β : relativeRoots (T := S_K) i_K =>
        (D.rootFixer β {fieldExtendPoint i hS hE ω hω D x}).comap (rationalExtend k K G)))
  rw [rootFixer_singleton, rootFixer_singleton,
    filtration_fieldExtendPoint i hS hE ω hω D x a.val a.property.1 0]
  rfl

omit [Mono i.hom.hom.left] in
/-- For a bijective rational-point extension, the double root groups are exact preimages. -/
theorem doubleRootGroupPoints_eq_comap (α : relativeRoots i) :
    doubleRootGroupPoints i α =
      (doubleRootGroupPoints (S := S_K) i_K
        (rootsBaseChangeEquiv (K := K) G S hS i α)).comap (rationalExtend k K G) := by
  have h2 : characterLattice.baseChange b S (2 • α.val) =
      2 • (rootsBaseChangeEquiv (K := K) G S hS i α).val :=
    map_nsmul _ _ _
  unfold doubleRootGroupPoints
  by_cases h : 2 • α.val ∈ relativeRoots i
  · have hK : 2 • (rootsBaseChangeEquiv (K := K) G S hS i α).val ∈
        relativeRoots (T := S_K) i_K := by
      rw [← h2]
      exact (mem_roots_baseChange_iff (K := K) G S hS i _).mpr h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true hK)]
    ext g
    rw [Subgroup.mem_comap, ← h2]
    exact (rationalExtend_mem_rootGroupPoints_iff (K := K) i hS (2 • α.val) h.1 g).symm
  · have hK : 2 • (rootsBaseChangeEquiv (K := K) G S hS i α).val ∉
        relativeRoots (T := S_K) i_K := by
      rw [← h2]
      exact fun hK => h ((mem_roots_baseChange_iff (K := K) G S hS i _).mp hK)
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false hK)]
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_bot, Subgroup.mem_bot]
    exact ⟨fun hg => by rw [hg, map_one], fun hg => hθ.1 (by rw [hg, map_one])⟩

omit hθ in
/-- The derivative of the extended functional is the base-changed root form exactly when the
derivative of the original functional is the root form. -/
theorem fieldExtendAffineFunctional_linear_iff
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (α : relativeRoots i) (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ) :
    (fieldExtendAffineFunctional i hS hE ω hω D ψ).linear =
        rootForm (S := S_K) i_K (rootsBaseChangeEquiv (K := K) G S hS i α) ↔
      ψ.linear = rootForm i α := by
  refine ⟨fun h => ?_, fieldExtendAffineFunctional_linear i hS hE ω hω D α ψ⟩
  apply LinearMap.ext
  intro w
  have hw := congrArg (fun l => l (splitTranslationBaseChange (K := K) hS i w)) h
  change ψ.linear ((splitTranslationBaseChange (K := K) hS i).symm
      (splitTranslationBaseChange (K := K) hS i w)) = _ at hw
  rw [LinearEquiv.symm_apply_apply, rootForm_splitTranslationBaseChange] at hw
  exact hw

/-- For a bijective rational-point extension, the extended functional is an affine root
upstairs exactly when the original functional is an affine root of the restricted data. -/
theorem fieldExtendAffineFunctional_mem_affineRoots_iff
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (ψ : (fieldRestrict i hS hE ω hω D).Apartment →ᵃ[ℝ] ℝ) :
    fieldExtendAffineFunctional i hS hE ω hω D ψ ∈ D.affineRoots ↔
      ψ ∈ (fieldRestrict i hS hE ω hω D).affineRoots := by
  constructor
  · rintro ⟨β, hβ, hnot⟩
    obtain ⟨α, rfl⟩ := (rootsBaseChangeEquiv (K := K) G S hS i).surjective β
    refine ⟨α, (fieldExtendAffineFunctional_linear_iff i hS hE ω hω D α ψ).1 hβ,
      fun hsub => hnot ?_⟩
    rw [affineRootGroup_fieldRestrict i hS hE ω hω D α.val α.property.1,
      affineRootGroupPlus_fieldRestrict i hS hE ω hω D α.val α.property.1,
      doubleRootGroupPoints_eq_comap i hS hθ α] at hsub
    exact (coe_comap_subset_mul_iff _ hθ _ _ _).1 hsub
  · rintro ⟨α, hα, hnot⟩
    refine ⟨rootsBaseChangeEquiv (K := K) G S hS i α,
      (fieldExtendAffineFunctional_linear_iff i hS hE ω hω D α ψ).2 hα, fun hsub => hnot ?_⟩
    rw [affineRootGroup_fieldRestrict i hS hE ω hω D α.val α.property.1,
      affineRootGroupPlus_fieldRestrict i hS hE ω hω D α.val α.property.1,
      doubleRootGroupPoints_eq_comap i hS hθ α]
    exact (coe_comap_subset_mul_iff _ hθ _ _ _).2 hsub

/-- For a bijective rational-point extension, the inverse restriction equivalence carries the
affine roots of the restricted data onto the affine roots upstairs. -/
theorem transportedRoots_fieldRestrict
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    AffineRootSystem.transportedRoots (fieldRestrictAffineEquiv i hS hE ω hω D).symm
        (fieldRestrict i hS hE ω hω D).affineRoots = D.affineRoots := by
  ext ψ'
  obtain ⟨ψ, rfl⟩ := (AffineRootSystem.affineFunctionalTransport
    (fieldRestrictAffineEquiv i hS hE ω hω D).symm).surjective ψ'
  rw [AffineRootSystem.transportedRoots,
    (AffineRootSystem.affineFunctionalTransport
      (fieldRestrictAffineEquiv i hS hE ω hω D).symm).injective.mem_set_image,
    ← fieldExtendAffineFunctional_eq_transport]
  exact (fieldExtendAffineFunctional_mem_affineRoots_iff i hS hE ω hω hθ D ψ).symm

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- The rational-point extension as a group isomorphism, when it is bijective. -/
def rationalExtendEquiv : rationalPoints G ≃* rationalPoints G_K :=
  MulEquiv.ofBijective (rationalExtend k K G) hθ

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
@[simp] theorem rationalExtendEquiv_apply (g : rationalPoints G) :
    rationalExtendEquiv hθ g = rationalExtend k K G g :=
  rfl

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
theorem rationalExtendEquiv_toMonoidHom :
    (rationalExtendEquiv hθ).toMonoidHom = rationalExtend k K G :=
  MonoidHom.ext fun _ => rfl

/-- Sharp fixers correspond under the rational-point extension and the inverse restriction. -/
theorem mem_sharpFixer_fieldRestrictAffineEquiv_symm_iff
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd))
    (x : (fieldRestrict i hS hE ω hω D).Apartment) (g : rationalPoints G) :
    rationalExtendEquiv hθ g ∈
        D.sharpFixer {(fieldRestrictAffineEquiv i hS hE ω hω D).symm x} ↔
      g ∈ (fieldRestrict i hS hE ω hω D).sharpFixer {x} := by
  rw [rationalExtendEquiv_apply, sharpFixer_fieldRestrict_eq i hS hE ω hω hθ D x]
  rfl

/-- For a bijective rational-point extension reflecting the normalizer, the equivalence of the
reduced buildings of the literal field restriction of `D` and of `D`, `[(g, x)] ↦ [(g_K, x_K)]`. -/
def fieldRestrictBuildingEquiv
    (hN : ∀ g : rationalPoints G,
      rationalExtendEquiv hθ g ∈ normalizerPoints (T := S_K) i_K ↔ g ∈ normalizerPoints i)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    (fieldRestrict i hS hE ω hω D).ReducedBuilding ≃ D.ReducedBuilding :=
  congrBuildingEquiv (fieldRestrict i hS hE ω hω D) D (rationalExtendEquiv hθ)
    (fieldRestrictAffineEquiv i hS hE ω hω D).symm hN
    (fun n x => fieldExtendPoint_normalizer i hS hE ω hω D n x)
    (mem_sharpFixer_fieldRestrictAffineEquiv_symm_iff i hS hE ω hω hθ D)

/-- For a bijective rational-point extension reflecting the normalizer, the literal field
restriction of `D` and `D` are related by a chart isomorphism along the rational-point
extension, with base point `1` and apartment map the inverse restriction. -/
theorem isChartIso_fieldRestrictBuildingEquiv
    (hN : ∀ g : rationalPoints G,
      rationalExtendEquiv hθ g ∈ normalizerPoints (T := S_K) i_K ↔ g ∈ normalizerPoints i)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (fun t => (ω t).toAdd)) :
    IsChartIso (fieldRestrict i hS hE ω hω D) D (rationalExtend k K G) 1
      (fieldRestrictAffineEquiv i hS hE ω hω D).symm
      (fieldRestrictBuildingEquiv i hS hE ω hω hθ hN D) := by
  rw [← rationalExtendEquiv_toMonoidHom hθ]
  exact isChartIso_congrBuildingEquiv (fieldRestrict i hS hE ω hω D) D (rationalExtendEquiv hθ)
    (fieldRestrictAffineEquiv i hS hE ω hω D).symm hN _ _
    (transportedRoots_fieldRestrict i hS hE ω hω hθ D)

end Langlands.Geometry.Building.KPApartmentData
