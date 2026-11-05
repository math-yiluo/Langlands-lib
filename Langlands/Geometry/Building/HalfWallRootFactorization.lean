import Langlands.Geometry.Building.ChamberWallRootGroups
import Langlands.Geometry.Building.ChamberPositiveCollection

/-! # The half-root factor at a chamber-simple wall -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Failure to be an affine root gives a strict factor followed by a
doubled-root factor at twice the original depth. -/
theorem affineRootGroup_subset_mul_double_of_not_mem_affineRoots
    {b : relativeRoots i} (h2b : 2 • (b : characterLattice S) ∈ relativeRoots i)
    {eta : D.Apartment →ᵃ[ℝ] ℝ} (hlin : eta.linear = rootForm i b)
    (hnot : eta ∉ D.affineRoots) :
    (D.affineRootGroup b eta : Set (rationalPoints G)) ⊆
      (D.affineRootGroupPlus b eta : Set (rationalPoints G)) *
        (D.affineRootGroup (2 • (b : characterLattice S)) ((2 : ℝ) • eta) :
          Set (rationalPoints G)) := by
  have hsub : (D.affineRootGroup b eta : Set (rationalPoints G)) ⊆
      (D.affineRootGroupPlus b eta : Set (rationalPoints G)) *
        (doubleRootGroupPoints i b : Set (rationalPoints G)) := by
    by_contra h
    exact hnot ⟨b, hlin, h⟩
  intro g hg
  obtain ⟨v, hv, u, hu, hvu⟩ := hsub hg
  have huRoot : u ∈ rootGroupPoints i (2 • (b : characterLattice S)) := by
    change u ∈ doubleRootGroupPoints i (b : characterLattice S) at hu
    rw [doubleRootGroupPoints, ite_eq_left h2b] at hu
    exact hu
  have huEta : u ∈ D.affineRootGroup b eta := by
    have h := (D.affineRootGroup b eta).mul_mem
      ((D.affineRootGroup b eta).inv_mem (D.affineRootGroupPlus_le b eta hv)) hg
    simpa only [← hvu, inv_mul_cancel_left] using h
  refine ⟨v, hv, u, ?_, hvu⟩
  have hlin2 : ((2 : ℝ) • eta).linear = rootForm i ⟨2 • (b : characterLattice S), h2b⟩ := by
    rw [AffineMap.smul_linear, hlin, rootForm_nsmul b.property 2 h2b]
    norm_num
  obtain ⟨x⟩ := (inferInstance : Nonempty D.Apartment)
  refine (mem_affineRootGroup_iff hlin2 x).2 ⟨huRoot, ?_⟩
  rw [x.isValuation.double b b.property h2b u huRoot, two_nsmul]
  have hx := ((mem_affineRootGroup_iff hlin x).1 huEta).2
  change ((2 * eta x : ℝ) : WithTop ℝ) ≤ _
  simpa only [two_mul, WithTop.coe_add] using add_le_add hx hx

variable (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
    eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {c : ℝ} (hc : 0 < c) {b : relativeRoots i}
    (hlin : (c • psi).linear = rootForm i b)

include hAS4 hpsi hc hlin

/-- Positive scalar multiples of the wall functional describe the
chamber fixer in their own derivative direction. -/
theorem rootFixer_eq_affineRootGroup_of_pos_smul_simpleAffineRoot :
    D.rootFixer b C = D.affineRootGroup b (c • psi) := by
  obtain ⟨x, y, hxC, hy, hzero⟩ :=
    AffineRootSystem.exists_mem_facetClosure_of_mem_simpleAffineRoots hpsi
  have hx : x ∈ C := hxC ▸ AffineRootSystem.mem_facet_self D.affineRoots x
  apply D.rootFixer_eq_affineRootGroup_of_mem_facetClosure hAS4 hx hy hlin
  · change c * psi y = 0
    rw [hzero, mul_zero]
  · intro z hz
    exact (mul_pos hc (hpsi.1.2 z hz)).le

/-- The reflected chamber gives the strict group for every positive
scalar multiple of the wall functional with a relative-root derivative. -/
theorem rootFixer_reflection_eq_affineRootGroupPlus_of_pos_smul_simpleAffineRoot
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    D.rootFixer b (AffineRootSystem.affineReflection psi hv.1 '' C) =
      D.affineRootGroupPlus b (c • psi) := by
  obtain ⟨x, y, hxC, hy, hzero⟩ :=
    AffineRootSystem.exists_mem_facetClosure_of_mem_simpleAffineRoots hpsi
  have hx : x ∈ C := hxC ▸ AffineRootSystem.mem_facet_self D.affineRoots x
  let s := AffineRootSystem.affineReflection psi hv.1
  have hs : s ∈ AffineRootSystem.affineWeylGroup D.affineRoots :=
    AffineRootSystem.affineReflection_mem_affineWeylGroup hpsi.1.1 hv
  have hsC : AffineRootSystem.IsChamber D.affineRoots (s '' C) :=
    hpsi.2.2.1.image_affineWeylGroup ⟨s, hs⟩
  have hsy : s y = y := AffineRootSystem.affineReflection_apply_of_mem psi hv.1 hzero
  have hyref : y ∈ AffineRootSystem.facetClosure D.affineRoots (s x) := by
    intro xi hxi
    have hcomp : xi.comp (s : D.Apartment →ᵃ[ℝ] D.Apartment) ∈ D.affineRoots := by
      rw [show s = AffineRootSystem.affineReflection psi hv.1 from rfl,
        AffineRootSystem.comp_affineReflection]
      exact hv.2 xi hxi
    have h := hy _ hcomp
    simpa only [AffineMap.comp_apply, AffineEquiv.coe_toAffineMap, hsy] using h
  have hneg : (c • psi) (s x) < 0 := by
    change c * psi (s x) < 0
    rw [show s = AffineRootSystem.affineReflection psi hv.1 from rfl,
      AffineRootSystem.apply_affineReflection]
    exact mul_neg_of_pos_of_neg hc (neg_neg_of_pos (hpsi.1.2 x hx))
  apply D.rootFixer_eq_affineRootGroupPlus_of_mem_facetClosure hAS4 hsC
    (Set.mem_image_of_mem s hx) hyref hlin
  · change c * psi y = 0
    rw [hzero, mul_zero]
  · exact hneg

omit hc hlin in
/-- An indivisible affine wall has no missing half-root factor: its
half-direction chamber fixer factors through the reflected fixer and `U_psi`. -/
theorem rootFixer_half_subset_reflection_mul_affineRootGroup
    (h2b : 2 • (b : characterLattice S) ∈ relativeRoots i)
    (hlin2 : psi.linear = rootForm i ⟨2 • (b : characterLattice S), h2b⟩)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    (D.rootFixer b C : Set (rationalPoints G)) ⊆
      (D.rootFixer b (AffineRootSystem.affineReflection psi hv.1 '' C) :
        Set (rationalPoints G)) *
      (D.affineRootGroup (2 • (b : characterLattice S)) psi : Set (rationalPoints G)) := by
  have hhalf : ((2 : ℝ)⁻¹ • psi).linear = rootForm i b := by
    rw [AffineMap.smul_linear, hlin2, rootForm_nsmul b.property 2 h2b, smul_smul]
    norm_num
  have hpos : 0 < (2 : ℝ)⁻¹ := by norm_num
  rw [D.rootFixer_eq_affineRootGroup_of_pos_smul_simpleAffineRoot hAS4 hpsi hpos hhalf,
    D.rootFixer_reflection_eq_affineRootGroupPlus_of_pos_smul_simpleAffineRoot
      hAS4 hpsi hpos hhalf hv]
  have h := D.affineRootGroup_subset_mul_double_of_not_mem_affineRoots h2b hhalf hpsi.2.1.2
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul] using h

omit hc hlin in
/-- The half-direction inclusion preserves the ambient rational point. -/
def halfWallRootGroupInclusion
    (h2b : 2 • (b : characterLattice S) ∈ relativeRoots i)
    (hlin2 : psi.linear = rootForm i ⟨2 • (b : characterLattice S), h2b⟩)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    D.rootFixer b C →
      ↥((D.rootFixer b (AffineRootSystem.affineReflection psi hv.1 '' C) :
        Set (rationalPoints G)) *
        (D.affineRootGroup (2 • (b : characterLattice S)) psi : Set (rationalPoints G))) :=
  fun g => ⟨g, D.rootFixer_half_subset_reflection_mul_affineRootGroup
    hAS4 hpsi h2b hlin2 hv g.property⟩

end Langlands.Geometry.Building.KPApartmentData
