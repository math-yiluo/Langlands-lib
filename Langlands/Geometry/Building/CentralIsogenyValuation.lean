import Langlands.Geometry.Building.CentralIsogenyFunctionsAction
import Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion

/-! # Valuation axioms under actual central-isogeny pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  (q : C ⟶ G) (hq : IsCentralIsogeny q)
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (t : S ⟶ T) (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))

open RootFunctionFamily

omit [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
include hq hS h ht in
private theorem rootPoint_map_eq_one_iff (a : relativeRoots j)
    (g : rationalPoints C) (hg : g ∈ rootGroupPoints i (t ≫ a.val)) :
    rationalPoints.map q g = 1 ↔ g = 1 := by
  have he := (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a).map_eq_one_iff
    (x := ⟨g, hg⟩)
  simpa only [← Subtype.val_inj, centralIsogenyRootGroupPointsEquiv_coe,
    OneMemClass.coe_one] using he

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
/-- The sets of values on corresponding root groups are equal. -/
theorem image_centralIsogenyPullback_root (φ : RootFunctionFamily T G)
    (a : relativeRoots j) :
    centralIsogenyPullback q hq hS hT t h ht φ (t ≫ a.val) ''
        (rootGroupPoints i (t ≫ a.val) : Set (rationalPoints C)) =
      φ a.val '' (rootGroupPoints j a.val : Set (rationalPoints G)) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨rationalPoints.map q g,
      (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a ⟨g, hg⟩).property,
      (centralIsogenyPullback_apply_root q hq hS hT t h ht φ a g hg).symm⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨g', hg'⟩ :=
      (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a).surjective ⟨g, hg⟩
    refine ⟨g'.val, g'.property, ?_⟩
    rw [centralIsogenyPullback_apply_root q hq hS hT t h ht φ a g'.val g'.property,
      ← centralIsogenyRootGroupPointsEquiv_coe q hq hS t h ht a g', hg']

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
include q hq hS hT h ht in
/-- Character restriction preserves and reflects actual root membership. -/
theorem centralIsogenyRoot_mem_iff (a : characterLattice T) :
    t ≫ a ∈ relativeRoots i ↔ a ∈ relativeRoots j := by
  let : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  let : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  let : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hc := characterRestrict_injective_of_epi t
  have hb := hq.roots_bijOn_of_torusRestriction hS hT t h ht
  constructor
  · intro ha
    obtain ⟨b, hb, he⟩ := hb.2.2 ha
    exact hc he ▸ hb
  · exact fun ha => hb.1 ha

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
/-- Normalized pullback evaluates correctly at every target character on its
actual source subgroup, including characters outside the root support. -/
theorem centralIsogenyPullback_apply_character {φ : RootFunctionFamily T G}
    (hφ : IsNormalized j φ) (a : characterLattice T)
    (g : rationalPoints C) (hg : g ∈ rootGroupPoints i (t ≫ a)) :
    centralIsogenyPullback q hq hS hT t h ht φ (t ≫ a) g =
      φ a (rationalPoints.map q g) := by
  by_cases ha : a ∈ relativeRoots j
  · exact centralIsogenyPullback_apply_root q hq hS hT t h ht φ ⟨a, ha⟩ g hg
  · rw [(centralIsogenyPullback_isNormalized q hq hS hT t h ht φ).1 _
      (fun ha' => ha ((centralIsogenyRoot_mem_iff q hq hS hT t h ht a).mp ha')) g,
      hφ.1 a ha]

namespace IsRootDatumValuation

variable {φ : RootFunctionFamily T G} (hφ : IsRootDatumValuation j φ)

include hφ

omit [Mono i.hom.hom.left] in
/-- V0 is preserved, since the actual root-point map is onto. -/
theorem centralIsogenyPullback_three_le_encard (a : relativeRoots j) :
    3 ≤ (centralIsogenyPullback q hq hS hT t h ht φ (t ≫ a.val) ''
      (rootGroupPoints i (t ≫ a.val) : Set (rationalPoints C))).encard := by
  rw [image_centralIsogenyPullback_root]
  exact hφ.three_le_encard a.val a.property

omit [Mono i.hom.hom.left] in
/-- V1: the pulled-back filtration contains the identity. -/
theorem centralIsogenyPullback_one_mem (a : relativeRoots j) (r : ℝ) :
    (1 : rationalPoints C) ∈
      rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r := by
  apply (rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht φ a r 1).mpr
  exact ⟨(rootGroupPoints i _).one_mem, by simpa only [map_one] using hφ.one_mem _ a.property r⟩

omit [Mono i.hom.hom.left] in
/-- V1: the pulled-back filtration is closed under products. -/
theorem centralIsogenyPullback_mul_mem (a : relativeRoots j) (r : ℝ)
    (g g' : rationalPoints C)
    (hg : g ∈ rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r)
    (hg' : g' ∈ rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r) :
    g * g' ∈ rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r := by
  have hgq := (rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht φ a r g).mp hg
  have hgq' := (rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht φ a r g').mp hg'
  apply (rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht φ a r (g * g')).mpr
  exact ⟨(rootGroupPoints i _).mul_mem hg.1 hg'.1, by
    rw [map_mul]
    exact hφ.mul_mem _ a.property r _ _ hgq.2 hgq'.2⟩

omit [Mono i.hom.hom.left] in
/-- V1: the pulled-back filtration is closed under inverses. -/
theorem centralIsogenyPullback_inv_mem (a : relativeRoots j) (r : ℝ)
    (g : rationalPoints C)
    (hg : g ∈ rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r) :
    g⁻¹ ∈ rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r := by
  have hgq := (rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht φ a r g).mp hg
  apply (rootFiltration_centralIsogenyPullback_iff q hq hS hT t h ht φ a r g⁻¹).mpr
  exact ⟨(rootGroupPoints i _).inv_mem hg.1, by
    rw [map_inv]
    exact hφ.inv_mem _ a.property r _ hgq.2⟩

omit [Mono i.hom.hom.left] in
/-- The actual pulled-back root filtration, bundled as a subgroup using V1. -/
def centralIsogenyPullbackRootFiltration (a : relativeRoots j) (r : ℝ) :
    Subgroup (rationalPoints C) where
  carrier := rootFiltration i (centralIsogenyPullback q hq hS hT t h ht φ) (t ≫ a.val) r
  one_mem' := hφ.centralIsogenyPullback_one_mem q hq hS hT t h ht a r
  mul_mem' := fun hg hg' =>
    hφ.centralIsogenyPullback_mul_mem q hq hS hT t h ht a r _ _ hg hg'
  inv_mem' := fun hg =>
    hφ.centralIsogenyPullback_inv_mem q hq hS hT t h ht a r _ hg

omit [Mono i.hom.hom.left] in
/-- V1 at infinity uses injectivity only on the corresponding root subgroup. -/
theorem centralIsogenyPullback_eq_top_iff (a : relativeRoots j)
    (g : rationalPoints C) (hg : g ∈ rootGroupPoints i (t ≫ a.val)) :
    centralIsogenyPullback q hq hS hT t h ht φ (t ≫ a.val) g = ⊤ ↔ g = 1 := by
  have hgq : rationalPoints.map q g ∈ rootGroupPoints j a.val :=
    (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a ⟨g, hg⟩).property
  rw [centralIsogenyPullback_apply_root q hq hS hT t h ht φ a g hg,
    hφ.eq_top_iff a.val a.property (rationalPoints.map q g) hgq]
  exact rootPoint_map_eq_one_iff q hq hS t h ht a g hg

/-- V2 uses the actual mapped normalizer and its conjugation action. -/
theorem centralIsogenyPullback_reflection (a : relativeRoots j)
    (n : normalizerPoints i) (hn : RealizesReflection i (t ≫ a.val) n) :
    ∃ c : ℝ, ∀ g ∈ rootGroupPoints i (t ≫ a.val), g ≠ 1 →
      centralIsogenyPullback q hq hS hT t h ht φ (t ≫ a.val) g =
        centralIsogenyPullback q hq hS hT t h ht φ (-(t ≫ a.val))
          ((n : rationalPoints C) * g * (n : rationalPoints C)⁻¹) + (c : WithTop ℝ) := by
  let n' := splitTorusIsogenyNormalizerMap q hS hT t h ht n
  obtain ⟨c, hc⟩ := hφ.reflection a.val a.property n'
    ((realizesReflection_splitTorusIsogenyNormalizerMap_iff q hS hT t h ht n a.val).mpr hn)
  refine ⟨c, fun g hg hg1 => ?_⟩
  have hcg : (n : rationalPoints C) * g * (n : rationalPoints C)⁻¹ ∈
      rootGroupPoints i (t ≫ (-a.val)) := by
    rw [Preadditive.comp_neg, ← hn.1]
    simpa only [rootGroupPoints, GroupScheme.constantPoint_self] using
      (RelativeRoot.normalizer_conj_mem_iff i (t ≫ a.val) n g).mpr hg
  rw [← Preadditive.comp_neg,
    centralIsogenyPullback_apply_root q hq hS hT t h ht φ a g hg,
    centralIsogenyPullback_apply_character q hq hS hT t h ht hφ.isNormalized _ _ hcg]
  have hgq := (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a ⟨g, hg⟩).property
  have hgq1 : rationalPoints.map q g ≠ 1 :=
    fun he => hg1 ((rootPoint_map_eq_one_iff q hq hS t h ht a g hg).mp he)
  simpa only [map_mul, map_inv, n', splitTorusIsogenyNormalizerMap_coe] using
    hc (rationalPoints.map q g) hgq hgq1

omit [Mono i.hom.hom.left] in
/-- V4 uses the positive-multiple inclusion and exact character restriction. -/
theorem centralIsogenyPullback_double (a : relativeRoots j)
    (h2a : 2 • (t ≫ a.val) ∈ relativeRoots i)
    (g : rationalPoints C) (hg : g ∈ rootGroupPoints i (2 • (t ≫ a.val))) :
    centralIsogenyPullback q hq hS hT t h ht φ (2 • (t ≫ a.val)) g =
      2 • centralIsogenyPullback q hq hS hT t h ht φ (t ≫ a.val) g := by
  have h2a' : 2 • a.val ∈ relativeRoots j := by
    apply (centralIsogenyRoot_mem_iff q hq hS hT t h ht (2 • a.val)).mp
    simpa only [Preadditive.comp_nsmul] using h2a
  have hg' : g ∈ rootGroupPoints i (t ≫ a.val) :=
    RelativeRoot.subgroup_nsmul_le i (t ≫ a.val) (by omega) _ hg
  have hg2 : g ∈ rootGroupPoints i (t ≫ (2 • a.val)) := by
    simpa only [Preadditive.comp_nsmul] using hg
  rw [← Preadditive.comp_nsmul,
    centralIsogenyPullback_apply_root q hq hS hT t h ht φ ⟨2 • a.val, h2a'⟩ g hg2,
    centralIsogenyPullback_apply_root q hq hS hT t h ht φ a g hg']
  exact hφ.double a.val a.property h2a' _ 
    (centralIsogenyRootGroupPointsEquiv q hq hS t h ht ⟨2 • a.val, h2a'⟩ ⟨g, hg2⟩).property

omit [Mono i.hom.hom.left] in
/-- V5 maps the actual opposite-root factorization and its normalizer. -/
theorem centralIsogenyPullback_opposite (a : relativeRoots j)
    (g : rationalPoints C) (hg : g ∈ rootGroupPoints i (t ≫ a.val)) (hg1 : g ≠ 1)
    (g' : rationalPoints C) (hg' : g' ∈ rootGroupPoints i (-(t ≫ a.val)))
    (g'' : rationalPoints C) (hg'' : g'' ∈ rootGroupPoints i (-(t ≫ a.val)))
    (hn : g' * g * g'' ∈ normalizerPoints i) :
    centralIsogenyPullback q hq hS hT t h ht φ (-(t ≫ a.val)) g' +
      centralIsogenyPullback q hq hS hT t h ht φ (t ≫ a.val) g = 0 := by
  have hnq := (splitTorusIsogenyNormalizerMap q hS hT t h ht ⟨g' * g * g'', hn⟩).property
  have hneg (g0 : rationalPoints C) (hg0 : g0 ∈ rootGroupPoints i (-(t ≫ a.val))) :
      rationalPoints.map q g0 ∈ rootGroupPoints j (-a.val) := by
    let : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
    let : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
    exact RelativeRoot.comp_mem_subgroup_of_flatSurjective_transport j (-a.val) t q h
      (by simpa only [rootGroupPoints, Preadditive.comp_neg] using hg0)
  rw [← Preadditive.comp_neg,
    centralIsogenyPullback_apply_character q hq hS hT t h ht hφ.isNormalized _ _
      (by simpa only [Preadditive.comp_neg] using hg'),
    centralIsogenyPullback_apply_root q hq hS hT t h ht φ a g hg]
  exact hφ.opposite a.val a.property (rationalPoints.map q g)
    (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a ⟨g, hg⟩).property
    (fun he => hg1 ((rootPoint_map_eq_one_iff q hq hS t h ht a g hg).mp he))
    _ (hneg g' hg') _ (hneg g'' hg'') (by
      simpa only [splitTorusIsogenyNormalizerMap_coe, map_mul] using hnq)

end IsRootDatumValuation

end Langlands.Geometry.Building
