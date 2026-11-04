import Langlands.Geometry.Building.KPFacetFixersStatement
import Langlands.Geometry.Building.ChamberParahoricConstancy

/-!
# Constancy of the actual root fixers and parahorics on facets

The comparison uses actual valuation jumps and the relation between the
affine roots and the extended affine roots.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {D : KPApartmentData i (localFieldOrder F)}
  {Z : CentralizerDatum i}

/-- AS 4 transports the facet relation from `Ψ` to `Ψ′`. -/
theorem SatisfiesApartmentAxioms.facetRel_extendedAffineRoots
    (hD : D.SatisfiesApartmentAxioms Z) {x y : D.Apartment}
    (hxy : AffineRootSystem.facetRel D.affineRoots x y) :
    AffineRootSystem.facetRel D.extendedAffineRoots x y := by
  intro ψ hψ
  rcases hD.mem_or_two_smul_mem ψ hψ with h | h
  · exact hxy ψ h
  · have hs := hxy ((2 : ℝ) • ψ) h
    simpa only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul, sign_mul,
      show SignType.sign (2 : ℝ) = 1 from sign_pos (by norm_num), one_mul] using hs

/-- A finite value of an actual root valuation determines an extended affine root.
Its value at every apartment point equals the valuation of the same element. -/
theorem affineFunctional_mem_extendedAffineRoots_of_value
    (a : relativeRoots i) (x : D.Apartment) {g : rationalPoints G}
    (hg : g ∈ rootGroupPoints i a) {r : ℝ} (hr : x.val a g = (r : WithTop ℝ)) :
    D.affineFunctional a x r ∈ D.extendedAffineRoots ∧
      ∀ y : D.Apartment,
        y.val a g = ((D.affineFunctional a x r y : ℝ) : WithTop ℝ) := by
  let ψ := D.affineFunctional a x r
  have hψ : ψ.linear = rootForm i a := D.affineFunctional_linear a x r
  have hψx : ψ x = r := by simp [ψ]
  have hmem : g ∈ D.affineRootGroup a ψ :=
    (D.mem_affineRootGroup_iff hψ x).2 ⟨hg, by rw [hψx, hr]⟩
  have hnot : g ∉ D.affineRootGroupPlus a ψ := by
    intro h
    have hlt := ((D.mem_affineRootGroupPlus_iff hψ x).1 h).2
    rw [hψx, hr] at hlt
    exact (lt_irrefl _ hlt)
  refine ⟨⟨a, hψ, fun heq => hnot (heq.symm ▸ hmem)⟩, fun y => ?_⟩
  apply le_antisymm
  · apply le_of_not_gt
    intro hlt
    exact hnot ((D.mem_affineRootGroupPlus_iff hψ y).2 ⟨hg, hlt⟩)
  · exact ((D.mem_affineRootGroup_iff hψ y).1 hmem).2

/-- The actual zero-depth filtration is constant on a `Ψ′` facet. -/
theorem filtration_zero_eq_of_facetRel_extendedAffineRoots
    {x y : D.Apartment}
    (hxy : AffineRootSystem.facetRel D.extendedAffineRoots x y)
    (a : relativeRoots i) :
    D.filtration x a 0 = D.filtration y a 0 := by
  have key : ∀ {x y : D.Apartment},
      AffineRootSystem.facetRel D.extendedAffineRoots x y →
        D.filtration x a 0 ≤ D.filtration y a 0 := by
    intro x y hxy g hg
    obtain ⟨hroot, hx⟩ := D.mem_filtration.1 hg
    apply D.mem_filtration.2
    refine ⟨hroot, ?_⟩
    by_contra hy
    have hylt : y.val a g < (0 : WithTop ℝ) := lt_of_not_ge hy
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hylt)
    obtain ⟨hψ, hval⟩ :=
      D.affineFunctional_mem_extendedAffineRoots_of_value a y hroot hr.symm
    have hrlt : r < 0 := by
      rw [← hr, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hylt
      exact hylt
    have hsign := hxy (D.affineFunctional a y r) hψ
    have hsigny : SignType.sign (D.affineFunctional a y r y) = -1 := by
      simpa using sign_neg hrlt
    have hxlt : D.affineFunctional a y r x < 0 :=
      sign_eq_neg_one_iff.1 (hsign.trans hsigny)
    rw [hval x, WithTop.coe_le_coe] at hx
    exact (not_le_of_gt hxlt) hx
  exact le_antisymm (key hxy)
    (key ((AffineRootSystem.facetRel_equivalence _).symm hxy))

/-- The actual root zero-depth subgroup depends only on the affine facet. -/
theorem SatisfiesApartmentAxioms.filtration_zero_eq_of_facetRel
    (hD : D.SatisfiesApartmentAxioms Z) {x y : D.Apartment}
    (hxy : AffineRootSystem.facetRel D.affineRoots x y) (a : relativeRoots i) :
    D.filtration x a 0 = D.filtration y a 0 :=
  filtration_zero_eq_of_facetRel_extendedAffineRoots
    (hD.facetRel_extendedAffineRoots hxy) a

/-- A nonempty subset of one facet has the same actual root fixer as any point in it. -/
theorem SatisfiesApartmentAxioms.rootFixer_eq_of_subset_facet
    (hD : D.SatisfiesApartmentAxioms Z) {Ω : Set D.Apartment} {x : D.Apartment}
    (hx : x ∈ Ω) (hΩ : Ω ⊆ AffineRootSystem.facet D.affineRoots x)
    (a : relativeRoots i) :
    D.rootFixer a Ω = D.filtration x a 0 := by
  apply le_antisymm
  · intro g hg
    exact (D.mem_rootFixer.1 hg).2 x hx
  · intro g hg
    apply D.mem_rootFixer.2
    refine ⟨D.filtration_le_rootGroupPoints x a 0 hg, fun y hy => ?_⟩
    rw [← hD.filtration_zero_eq_of_facetRel (hΩ hy) a]
    exact hg

/-- The actual sharp subgroup is constant on every nonempty subset of a facet. -/
theorem SatisfiesApartmentAxioms.sharpFixer_eq_of_subset_facet
    (hD : D.SatisfiesApartmentAxioms Z) {Ω : Set D.Apartment} {x : D.Apartment}
    (hx : x ∈ Ω) (hΩ : Ω ⊆ AffineRootSystem.facet D.affineRoots x) :
    D.sharpFixer Ω = D.sharpFixer {x} := by
  unfold sharpFixer
  congr 1
  funext a
  rw [hD.rootFixer_eq_of_subset_facet hx hΩ a, D.rootFixer_singleton]

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The exact facet-constancy statement for the actual full parahoric. -/
theorem facetFixerConstancy : P.FacetFixerConstancyStatement := by
  intro hP Fa hFa x hx
  exact P.parahoric_eq_parahoricAt_of_isFacet hP hFa hx

end Langlands.Geometry.Building.ParahoricBuildingData
