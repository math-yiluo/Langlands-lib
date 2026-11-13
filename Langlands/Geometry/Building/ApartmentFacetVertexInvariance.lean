import Langlands.Geometry.Building.BuildingFacetIncidence
import Langlands.Geometry.Building.NormalizerAffineRootAction

/-! # Closed-facet coordinate changes and vertex-set invariance over any field -/

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

/-- A quotient coordinate change at one point agrees on its whole closed
facet. The extended-root AS4 condition is the only additional hypothesis. -/
theorem exists_normalizer_eq_on_translated_facetClosure
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {a b : D.Apartment} (g : rationalPoints G)
    (hab : g • D.apartmentMap a = D.apartmentMap b) :
    ∃ n : normalizerPoints i, n • a = b ∧
      ∀ y ∈ AffineRootSystem.facetClosure D.affineRoots a,
        g • D.apartmentMap y = D.apartmentMap (n • y) := by
  have hab' :
      ApartmentQuotient.mk D.sharpFixerFamily (g, a) =
        ApartmentQuotient.mk D.sharpFixerFamily (1, b) := by
    have h :
        ApartmentQuotient.mk D.sharpFixerFamily (g * 1, a) =
          ApartmentQuotient.mk D.sharpFixerFamily (1, b) := hab
    simpa only [mul_one] using h
  obtain ⟨n, hn, hp⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff D.sharpFixerFamily g 1 a b).mp hab'
  have hp' : g⁻¹ * (n : rationalPoints G) ∈ D.sharpFixer {a} := by
    change g⁻¹ * 1 * (n : rationalPoints G) ∈ D.sharpFixer {a} at hp
    simpa only [mul_one] using hp
  refine ⟨n, hn, fun y hy => ?_⟩
  have hfix : (g⁻¹ * (n : rationalPoints G)) • D.apartmentMap y =
      D.apartmentMap y :=
    D.mem_reducedFixer.mp (D.sharpFixer_le_reducedFixer y
      (D.sharpFixer_singleton_le_of_mem_facetClosure hAS4 hy hp'))
  have heq := congrArg (g • ·) hfix
  rw [mul_smul, smul_inv_smul, ← D.apartmentMap_smul] at heq
  exact heq.symm

/-- Images of all original apartment vertices in closures of facets meeting
`Ω`, inside the apartment translated by `g`. -/
def facetClosureVertexImage (g : rationalPoints G) (Ω : Set D.Apartment) :
    Set D.ReducedBuilding :=
  (fun q => g • D.apartmentMap q) ''
    {q | ∃ p ∈ Ω, q ∈ AffineRootSystem.facetClosure D.affineRoots p ∧
      AffineRootSystem.IsVertex D.affineRoots q}

/-- Every pointwise fixer of the original subset preserves the full vertex
image of the closed facets meeting it. No affine-root-system or chart
injectivity premise is needed. -/
theorem smul_mem_facetClosureVertexImage
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    (g : rationalPoints G) (Ω : Set D.Apartment)
    {h : rationalPoints G}
    (hfix : h ∈ D.pointwiseFixer ((fun x => g • D.apartmentMap x) '' Ω))
    {y : D.ReducedBuilding} (hy : y ∈ D.facetClosureVertexImage g Ω) :
    h • y ∈ D.facetClosureVertexImage g Ω := by
  obtain ⟨q, ⟨p, hp, hq, hv⟩, rfl⟩ := hy
  have hpt : (g⁻¹ * h * g) • D.apartmentMap p = D.apartmentMap p := by
    rw [mul_smul, mul_smul,
      D.mem_pointwiseFixer.mp hfix _ ⟨p, hp, rfl⟩, inv_smul_smul]
  obtain ⟨n, hn, heq⟩ :=
    D.exists_normalizer_eq_on_translated_facetClosure hAS4 (g⁻¹ * h * g) hpt
  have hroot := D.normalizerAffineEquiv_mem_rootStabilizer n
  have hclosure : n • q ∈ AffineRootSystem.facetClosure D.affineRoots (n • p) := by
    intro ψ hψ
    exact hq (ψ.comp (D.normalizerAffineEquiv n : D.Apartment →ᵃ[ℝ] D.Apartment))
      ((AffineRootSystem.comp_mem_iff hroot ψ).2 hψ)
  have hvertex : AffineRootSystem.IsVertex D.affineRoots (n • q) := by
    change AffineRootSystem.facet D.affineRoots (D.normalizerAffineEquiv n q) = _
    rw [← AffineRootSystem.image_facet hroot, hv, Set.image_singleton]
    rfl
  refine ⟨n • q, ⟨p, hp, hn ▸ hclosure, hvertex⟩, ?_⟩
  have H := congrArg (g • ·) (heq q hq)
  simpa only [mul_smul, smul_inv_smul] using H.symm

end Langlands.Geometry.Building.KPApartmentData
