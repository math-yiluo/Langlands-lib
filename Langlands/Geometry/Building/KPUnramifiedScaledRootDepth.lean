import Langlands.Geometry.Building.KPUnramifiedComparisonRootHelpers
import Langlands.Geometry.Building.RootValueTorusUniformBlocks
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor
import Langlands.GroupScheme.Reductive.RootDatumGaloisRoots

/-! # Scaled upper root depth factors of a concrete unramified lift -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance scaledRootDepthAffineHom {F : Type u} [Field F]
    {K : Type u} [Field K] [Algebra F K]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F K))
  infer_instance

private theorem scaledRootDepth_galois_map_le
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)
    [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
    {φ : RootFunctionFamily ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      (baseChanged k K G)}
    (hφ : IsRootDatumValuation ((GroupScheme.baseChange (algebraBaseMap k K)).map i) φ)
    (f : S ⟶ T) (σ : K ≃ₐ[k] K)
    (hfixed : RootFunctionFamily.galoisAction k K T G σ φ = φ)
    (a : characterLattice S) (r : ℝ) (g : rationalPoints (baseChanged k K G))
    (hg : g ∈ torusRestrictedRootDepthSubgroup hφ
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)
      (characterLattice.baseChange (algebraBaseMap k K) S a) r) :
    rationalConjugate k K G σ g ∈ torusRestrictedRootDepthSubgroup hφ
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)
      (characterLattice.baseChange (algebraBaseMap k K) S a) r := by
  have hmap : (torusRestrictedRootDepthSubgroup hφ
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)
      (characterLattice.baseChange (algebraBaseMap k K) S a) r).map
      (rationalConjugate k K G σ).toMonoidHom ≤
    torusRestrictedRootDepthSubgroup hφ
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)
      (characterLattice.baseChange (algebraBaseMap k K) S a) r := by
    unfold torusRestrictedRootDepthSubgroup
    simp only [Subgroup.map_iSup]
    refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun m =>
      iSup_le fun hm => iSup_le fun heq => ?_
    have hχ' := (mem_roots_galois_iff k K i σ χ).mpr hχ
    have heq' : ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f) ≫
        characterLattice.galoisRepresentation k K T σ χ =
        m • (characterLattice.baseChange (algebraBaseMap k K) S a) := by
      rw [← characterLattice.galoisRepresentation_naturality k K f σ χ,
        heq, map_nsmul, characterLattice.galoisRepresentation_baseChange]
    refine le_iSup_of_le (characterLattice.galoisRepresentation k K T σ χ)
      (le_iSup_of_le hχ' (le_iSup_of_le m
        (le_iSup_of_le hm (le_iSup_of_le heq' ?_))))
    rintro x ⟨z, hz, rfl⟩
    have htransport := (rationalConjugate_mem_rootFiltration_iff k K i σ
      φ χ (m * r) z).mpr hz
    rw [hfixed] at htransport
    exact htransport
  exact hmap (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

namespace ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} {t : P.UnramifiedComparisonTorus}
    (L : t.ApartmentLift)

local notation "Fur" => UnramifiedClosure F
local notation "fK" =>
  CategoryTheory.Functor.map
    (CommGroupScheme.baseChange (algebraBaseMap F Fur)) t.f
local notation "aK" a =>
  characterLattice.baseChange (algebraBaseMap F Fur) P.S a

/-- The actual upper multiplier-scaled depth subgroup at a lower character. -/
def scaledRootDepth (y : P.Apartment) (a : characterLattice P.S) (r : ℝ) :
    Subgroup (rationalPoints (baseChanged F Fur G)) :=
  torusRestrictedRootDepthSubgroup
    (L.apartment.isRootDatumValuation_of_mem (L.e y).mem) fK (aK a) r

set_option maxHeartbeats 4000000 in
/-- Each scaled upper factor is stable under coefficient conjugation. -/
theorem rationalConjugate_mem_scaledRootDepth
    (y : P.Apartment) (a : characterLattice P.S) (r : ℝ)
    (σ : Fur ≃ₐ[F] Fur) (g : rationalPoints (baseChanged F Fur G))
    (hg : g ∈ L.scaledRootDepth y a r) :
    rationalConjugate F Fur G σ g ∈ L.scaledRootDepth y a r := by
  unfold scaledRootDepth at hg ⊢
  have h := @scaledRootDepth_galois_map_le F Fur _ _ _ P.S t.T G _ t.iT
    t.extendedMono (L.e y).val
    (L.apartment.isRootDatumValuation_of_mem (L.e y).mem) t.f σ
    (L.fixed y σ) a r g hg
  exact h

/-- Stability is an equivalence, at every lower character and real depth. -/
theorem rationalConjugate_mem_scaledRootDepth_iff
    (y : P.Apartment) (a : characterLattice P.S) (r : ℝ)
    (σ : Fur ≃ₐ[F] Fur) (g : rationalPoints (baseChanged F Fur G)) :
    rationalConjugate F Fur G σ g ∈ L.scaledRootDepth y a r ↔
      g ∈ L.scaledRootDepth y a r := by
  constructor
  · intro hg
    have h := L.rationalConjugate_mem_scaledRootDepth y a r σ⁻¹ _ hg
    simpa only [← rationalConjugate_mul, inv_mul_cancel, rationalConjugate_one] using h
  · exact L.rationalConjugate_mem_scaledRootDepth y a r σ g

set_option maxHeartbeats 1000000 in
/-- The common part of the two nonnegative-depth factors has doubled depth. -/
theorem scaledRootDepth_inf_double
    (y : P.Apartment) (a : relativeRoots P.i) {r : ℝ} (hr : 0 ≤ r) :
    L.scaledRootDepth y a r ⊓ L.scaledRootDepth y (2 • a.val) r =
      L.scaledRootDepth y (2 • a.val) (2 * r) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have haK : (aK a.val) ≠ 0 :=
    ((mem_roots_baseChange_iff (K := Fur) G P.S
      P.isMaximalSplitTorus.isSplitSubtorus.1 P.i a.val).mpr a.property).1
  simpa only [scaledRootDepth, map_nsmul] using
    torusRestrictedRootDepthSubgroup_inf_double
      (P.isMaximalSplitTorus.isSplitSubtorus.1.baseChange (algebraBaseMap F Fur))
      t.isMaximalSplitTorus.isSplitSubtorus.1 L.oppositeFactorPairs
      (L.apartment.isRootDatumValuation_of_mem (L.e y).mem) fK (aK a.val) haK hr

set_option maxHeartbeats 4000000 in
/-- The uniform positive fibre is the join of its two scaled factors. -/
theorem rootFiltrationSpan_eq_scaledRootDepth_sup
    (y : P.Apartment) (a : relativeRoots P.i) {r : ℝ} (hr : 0 ≤ r) :
    L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) r =
      L.scaledRootDepth y a r ⊔ L.scaledRootDepth y (2 • a.val) r := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  calc
    _ = torusUniformRootDepthSubgroup
        (L.apartment.isRootDatumValuation_of_mem (L.e y).mem) fK (aK a.val) r := by
      unfold torusUniformRootDepthSubgroup MaximalUnramified.BuildingData.rootFiltrationSpan
      rw [iSup_subtype]
      rfl
    _ = _ := by
      have h := @torusUniformRootDepthSubgroup_eq_block F Fur _ _ _ P.S G _ _ P.i _
        t.upstairsTorus t.upstairsInclusion t.extendedMono (L.e y).val
        (L.apartment.isRootDatumValuation_of_mem (L.e y).mem)
        P.isMaximalSplitTorus.isSplitSubtorus.1
        (relativeRootSystem F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
        fK (fieldFactorization (t := t)) a.val a.property r hr
      unfold torusRestrictedRootDepthBlock at h
      unfold scaledRootDepth
      rw [map_nsmul]
      exact h

set_option maxHeartbeats 1000000 in
private theorem scaledRootDepth_noHigherRoots (a : relativeRoots P.i) :
    ∀ n : ℕ, 3 ≤ n →
      n • (aK a.val) ∉ relativeRoots (CommGroupScheme.groupHom fK ≫ t.upstairsInclusion) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  intro n hn hnroot
  rw [fieldFactorization (t := t)] at hnroot
  have hnroot' : (aK (n • a.val)) ∈ relativeRoots
      ((GroupScheme.baseChange (algebraBaseMap F Fur)).map P.i) := by
    simpa only [map_nsmul] using hnroot
  have hnF := (mem_roots_baseChange_iff (K := Fur) G P.S
    P.isMaximalSplitTorus.isSplitSubtorus.1 P.i (n • a.val)).mp hnroot'
  exact (relativeRootSystem F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus).nsmul_not_mem_of_three_le a.property hn hnF

set_option maxHeartbeats 1000000 in
/-- The scaled join has a two-factor product description at every real depth. -/
theorem mem_scaledRootDepth_sup_iff_exists_mul
    (y : P.Apartment) (a : relativeRoots P.i) (r : ℝ)
    (g : rationalPoints (baseChanged F Fur G)) :
    g ∈ L.scaledRootDepth y a r ⊔ L.scaledRootDepth y (2 • a.val) r ↔
      ∃ x ∈ L.scaledRootDepth y a r,
        ∃ z ∈ L.scaledRootDepth y (2 • a.val) r, x * z = g := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have haK : (aK a.val) ≠ 0 :=
    ((mem_roots_baseChange_iff (K := Fur) G P.S
      P.isMaximalSplitTorus.isSplitSubtorus.1 P.i a.val).mpr a.property).1
  simpa only [scaledRootDepth, torusRestrictedRootDepthBlock, map_nsmul] using
    mem_torusRestrictedRootDepthBlock_iff_exists_mul_of_noHigherRoots
      (P.isMaximalSplitTorus.isSplitSubtorus.1.baseChange (algebraBaseMap F Fur))
      t.isMaximalSplitTorus.isSplitSubtorus.1
      (L.apartment.isRootDatumValuation_of_mem (L.e y).mem) fK (aK a.val) haK
      (scaledRootDepth_noHigherRoots (t := t) a) r g

/-- A uniform nonnegative-depth point factors in the two scaled subgroups. -/
theorem mem_rootFiltrationSpan_iff_exists_scaled_mul
    (y : P.Apartment) (a : relativeRoots P.i) {r : ℝ} (hr : 0 ≤ r)
    (g : rationalPoints (baseChanged F Fur G)) :
    g ∈ L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) r ↔
      ∃ x ∈ L.scaledRootDepth y a r,
        ∃ z ∈ L.scaledRootDepth y (2 • a.val) r, x * z = g := by
  rw [L.rootFiltrationSpan_eq_scaledRootDepth_sup y a hr]
  exact L.mem_scaledRootDepth_sup_iff_exists_mul y a r g

/-- The doubled factor may be placed first, as needed for coset correction. -/
theorem mem_rootFiltrationSpan_iff_exists_double_scaled_mul
    (y : P.Apartment) (a : relativeRoots P.i) {r : ℝ} (hr : 0 ≤ r)
    (g : rationalPoints (baseChanged F Fur G)) :
    g ∈ L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) r ↔
      ∃ z ∈ L.scaledRootDepth y (2 • a.val) r,
        ∃ x ∈ L.scaledRootDepth y a r, z * x = g := by
  constructor
  · intro hg
    obtain ⟨x, hx, z, hz, hxz⟩ :=
      (L.mem_rootFiltrationSpan_iff_exists_scaled_mul y a hr g⁻¹).mp
        ((L.buildingData.rootFiltrationSpan (L.e y) (L.rootFiber a) r).inv_mem hg)
    refine ⟨z⁻¹, (L.scaledRootDepth y (2 • a.val) r).inv_mem hz,
      x⁻¹, (L.scaledRootDepth y a r).inv_mem hx, ?_⟩
    rw [← mul_inv_rev, hxz, inv_inv]
  · rintro ⟨z, hz, x, hx, rfl⟩
    rw [L.rootFiltrationSpan_eq_scaledRootDepth_sup y a hr]
    exact (L.scaledRootDepth y a r ⊔ L.scaledRootDepth y (2 • a.val) r).mul_mem
      ((show L.scaledRootDepth y (2 • a.val) r ≤
        L.scaledRootDepth y a r ⊔ L.scaledRootDepth y (2 • a.val) r from le_sup_right) hz)
      ((show L.scaledRootDepth y a r ≤
        L.scaledRootDepth y a r ⊔ L.scaledRootDepth y (2 • a.val) r from le_sup_left) hx)

end ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

end Langlands.Geometry.Building
