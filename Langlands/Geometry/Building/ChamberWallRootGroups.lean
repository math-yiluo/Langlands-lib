import Langlands.Geometry.Building.AffineIwahoriTitsAssembly
import Langlands.Geometry.Building.ChamberFiltration

/-! # Root groups in the direction of a chamber wall -/

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
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)

include hAS4

/-- A nonnegative affine functional with a zero in the chamber closure
defines exactly the chamber root fixer in its own direction. -/
theorem rootFixer_eq_affineRootGroup_of_mem_facetClosure
    {C : Set D.Apartment} {x : D.Apartment} (hx : x ∈ C)
    {y : D.Apartment} (hy : y ∈ AffineRootSystem.facetClosure D.affineRoots x)
    {a : relativeRoots i} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hlin : psi.linear = rootForm i a) (hzero : psi y = 0)
    (hpos : ∀ z ∈ C, 0 ≤ psi z) :
    D.rootFixer a C = D.affineRootGroup a psi := by
  apply le_antisymm
  · intro g hg
    rw [D.affineRootGroup_eq_filtration hlin y, hzero]
    exact (D.filtration_comparison_of_mem_facetClosure hAS4 hy a.property).2
      ((D.mem_rootFixer.1 hg).2 x hx)
  · intro g hg
    have hgroot := D.affineRootGroup_le_rootGroupPoints a psi hg
    refine D.mem_rootFixer.2 ⟨hgroot, fun z hz => ?_⟩
    exact mem_filtration.2 ⟨hgroot, (WithTop.coe_le_coe.2 (hpos z hz)).trans
      ((mem_affineRootGroup_iff hlin z).1 hg).2⟩

/-- On the negative side of such a wall the chamber root fixer is the
strict affine root group. -/
theorem rootFixer_eq_affineRootGroupPlus_of_mem_facetClosure
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C)
    {y : D.Apartment} (hy : y ∈ AffineRootSystem.facetClosure D.affineRoots x)
    {a : relativeRoots i} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hlin : psi.linear = rootForm i a) (hzero : psi y = 0)
    (hneg : psi x < 0) :
    D.rootFixer a C = D.affineRootGroupPlus a psi := by
  apply le_antisymm
  · intro g hg
    by_cases hg1 : g = 1
    · subst g
      exact one_mem _
    have hgroot := (D.mem_rootFixer.1 hg).1
    obtain ⟨eta, heta, hlineta, hval⟩ :=
      D.exists_extendedAffineRoot_of_ne_one x a.property hgroot hg1
    have hxge : 0 ≤ eta x := by
      simpa only [hval x, WithTop.coe_le_coe] using
        ((D.mem_rootFixer.1 hg).2 x hx).2
    have hdiff : eta y - eta x = psi y - psi x := by
      have hd := congrArg (fun f : TranslationSpace i →ₗ[ℝ] ℝ => f (y -ᵥ x))
        (hlineta.trans hlin.symm)
      simpa only [AffineMap.linearMap_vsub, vsub_eq_sub] using hd
    have hypos : 0 < eta y := by
      rw [hzero] at hdiff
      linarith
    refine (mem_affineRootGroupPlus_iff hlin y).2 ⟨hgroot, ?_⟩
    rw [hzero, hval y, WithTop.coe_lt_coe]
    exact hypos
  · intro g hg
    have hgy : g ∈ D.filtrationPlus y a 0 := by
      have hg' := (mem_affineRootGroupPlus_iff hlin y).1 hg
      exact mem_filtrationPlus.2 ⟨hg'.1, by simpa only [hzero] using hg'.2⟩
    have hgx := (D.filtration_comparison_of_mem_facetClosure hAS4 hy a.property).1 hgy
    rw [(D.rootFixer_eq_filtration_of_isFacet hAS4 hC.isFacet hx a.property).1]
    exact D.filtrationPlus_le_filtration x a 0 hgx

variable {C : Set D.Apartment}
    {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {a : relativeRoots i} (hlin : psi.linear = rootForm i a)

include hpsi hlin

/-- The wall's own affine root group is the chamber root fixer,
including when its relative-root derivative is divisible. -/
theorem rootFixer_eq_affineRootGroup_of_simpleAffineRoot :
    D.rootFixer a C = D.affineRootGroup a psi := by
  obtain ⟨x, y, hxC, hy, hzero⟩ :=
    AffineRootSystem.exists_mem_facetClosure_of_mem_simpleAffineRoots hpsi
  have hx : x ∈ C := hxC ▸ AffineRootSystem.mem_facet_self D.affineRoots x
  exact D.rootFixer_eq_affineRootGroup_of_mem_facetClosure hAS4 hx hy hlin hzero
    (fun z hz => (hpsi.1.2 z hz).le)

/-- Reflection changes the wall-direction chamber group to its strict
affine root group. -/
theorem rootFixer_reflection_eq_affineRootGroupPlus_of_simpleAffineRoot
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    D.rootFixer a (AffineRootSystem.affineReflection psi hv.1 '' C) =
      D.affineRootGroupPlus a psi := by
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
  have hneg : psi (s x) < 0 := by
    rw [show s = AffineRootSystem.affineReflection psi hv.1 from rfl,
      AffineRootSystem.apply_affineReflection]
    exact neg_neg_of_pos (hpsi.1.2 x hx)
  exact D.rootFixer_eq_affineRootGroupPlus_of_mem_facetClosure hAS4 hsC
    (Set.mem_image_of_mem s hx) hyref hlin hzero hneg

/-- The own-direction wall comparison is the identity on rational points. -/
def rootFixerEquivAffineRootGroup_of_simpleAffineRoot :
    D.rootFixer a C ≃* D.affineRootGroup a psi :=
  MulEquiv.subgroupCongr
    (D.rootFixer_eq_affineRootGroup_of_simpleAffineRoot hAS4 hpsi hlin)

end Langlands.Geometry.Building.KPApartmentData
