import Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedRadicalRootGenerationProof
import Langlands.Geometry.Building.IntegerBuildingFacetPartition
import Langlands.Geometry.Building.ChamberFiltration
import Langlands.Geometry.Building.FacetClosureUnionClosedProof

/-! # Positive radical inclusion along descended facet incidence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

private instance unramifiedFacetPositiveProofAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

private theorem affine_mem_facetClosure
    {V W P P' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddTorsor W P']
    {Ψ : Set (P →ᵃ[ℝ] ℝ)} {Φ : Set (P' →ᵃ[ℝ] ℝ)}
    (a : P →ᵃ[ℝ] P') {x y : P}
    (hfacet : a '' AffineRootSystem.facet Ψ x ⊆ AffineRootSystem.facet Φ (a x))
    (hy : y ∈ AffineRootSystem.facetClosure Ψ x) :
    a y ∈ AffineRootSystem.facetClosure Φ (a x) := by
  have hycl := AffineRootSystem.facetClosure_subset_closure_facet Ψ x hy
  intro ψ hψ
  let f : P →ᵃ[ℝ] ℝ := ψ.comp a
  have hf : Continuous f := f.continuous_of_finiteDimensional
  have hsign : ∀ z ∈ AffineRootSystem.facet Ψ x,
      SignType.sign (f z) = SignType.sign (f x) :=
    fun z hz => (hfacet ⟨z, hz, rfl⟩ ψ hψ).symm
  rcases lt_trichotomy (f x) 0 with hx | hx | hx
  · have hsub : AffineRootSystem.facet Ψ x ⊆ {z | f z ≤ 0} := by
      intro z hz
      exact (sign_eq_neg_one_iff.1 ((hsign z hz).trans (sign_neg hx))).le
    have hle : f y ≤ 0 := closure_minimal hsub (isClosed_le hf continuous_const) hycl
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inr ((sign_neg hlt).trans (sign_neg hx).symm)
    · exact Or.inl (sign_eq_zero_iff.2 heq)
  · have hsub : AffineRootSystem.facet Ψ x ⊆ {z | f z = 0} := by
      intro z hz
      exact sign_eq_zero_iff.1 (by simpa only [hx, sign_zero] using hsign z hz)
    have heq : f y = 0 := closure_minimal hsub (isClosed_eq hf continuous_const) hycl
    exact Or.inl (sign_eq_zero_iff.2 heq)
  · have hsub : AffineRootSystem.facet Ψ x ⊆ {z | 0 ≤ f z} := by
      intro z hz
      exact (sign_eq_one_iff.1 ((hsign z hz).trans (sign_pos hx))).le
    have hle : 0 ≤ f y := closure_minimal hsub (isClosed_le continuous_const hf) hycl
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inr ((sign_pos hlt).trans (sign_pos hx).symm)
    · exact Or.inl (sign_eq_zero_iff.2 heq.symm)

set_option maxHeartbeats 2000000 in
/-- Positive radical subgroups grow along incidence of descended facets,
with all hypotheses and quantifiers of the published target. -/
theorem unramifiedFacetPositiveRadical :
    UnramifiedFacetPositiveRadicalStatement.{u} := by
  intro F _ _ _ _ G _ P R T hBuilding hOpen hAffine hReflections hApartments
    hCompatible hTits C A e a he hEquivariant hApartment hFixed hSurjective
    hSpecial hFacets hKernel E Fc Fc' hPrecedes D D' hSmooth hSmooth'
    hPoints hPoints' Q Q' hQ hQ'
  let B := P.toValuationBuildingData
  let := B.metricRootFintype
  let := RootTranslationMetric.normedAddCommGroup B.i
  let := RootTranslationMetric.normedSpace B.i
  let := B.apartmentMetricSpace
  let := B.apartmentNormedAddTorsor
  let := RootTranslationMetric.finiteDimensional B.i
  obtain ⟨H, _, hGen⟩ := unramifiedRadicalRootGeneration F G C E
  obtain ⟨g, Fa, Ca, hFace, hFc, hFc'⟩ := hPrecedes
  obtain ⟨w, hwFacet⟩ := hFace.1
  have hw : w ∈ Fa := hwFacet ▸ AffineRootSystem.mem_facet_self _ _
  obtain ⟨w', hwFacet', _⟩ := hFace.2
  have hw' : w' ∈ Ca := hwFacet' ▸ AffineRootSystem.mem_facet_self _ _
  have hImageFacet (x : B.Apartment) :
      a '' AffineRootSystem.facet B.affineRoots x ⊆
        AffineRootSystem.facet C.affineRoots (a x) := by
    rintro _ ⟨y, hy, rfl⟩
    change y ∈ a ⁻¹' AffineRootSystem.facet C.affineRoots (a x)
    rwa [hFacets x]
  have hFa : a '' Fa ⊆ AffineRootSystem.facet C.affineRoots (a w) := by
    rw [← hwFacet]
    exact hImageFacet w
  have hCa : a '' Ca ⊆ AffineRootSystem.facet C.affineRoots (a w') := by
    rw [← hwFacet']
    exact hImageFacet w'
  have hImage (Ω : Set B.Apartment) :
      e '' (B.translatedApartmentMap g '' Ω) =
        (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
          (a '' Ω) := by
    simp only [Set.image_image]
    apply Set.image_congr
    intro x _
    exact (hEquivariant g (B.apartmentMap x)).trans
      (congrArg (rationalExtend F (inertiaFixedField F) G g • ·) (hApartment x))
  have hSetFa : e '' Fc.val =
      (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
        (a '' Fa) :=
    (congrArg (Set.image e) hFc).trans (hImage Fa)
  have hSetCa : e '' Fc'.val =
      (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
        (a '' Ca) :=
    (congrArg (Set.image e) hFc').trans (hImage Ca)
  have hRad := hGen (a '' Fa) (Set.Nonempty.image a ⟨w, hw⟩)
    ⟨a w, hFa⟩ (rationalExtend F (inertiaFixedField F) G g) D hSmooth
    (hPoints.trans (congrArg (fun S => E.zeroPoints ⊓ C.pointwiseFixer S) hSetFa)) Q hQ
  have hRad' := hGen (a '' Ca) (Set.Nonempty.image a ⟨w', hw'⟩)
    ⟨a w', hCa⟩ (rationalExtend F (inertiaFixedField F) G g) D' hSmooth'
    (hPoints'.trans (congrArg (fun S => E.zeroPoints ⊓ C.pointwiseFixer S) hSetCa)) Q' hQ'
  have hRoots (α : relativeRoots C.i) :
      C.rootFixerPlus α (a '' Fa) ≤ C.rootFixerPlus α (a '' Ca) := by
    intro z hz
    have hz' := C.apartment.mem_rootFixerPlus_iff_forall_mem.1 hz
    refine C.apartment.mem_rootFixerPlus_iff_forall_mem.2 ⟨hz'.1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hClosure : a w ∈ AffineRootSystem.facetClosure C.affineRoots (a x) :=
      affine_mem_facetClosure a (hImageFacet x)
        (B.apartment.mem_facetClosure_of_isFaceOf hFace hx hw)
    exact (C.apartment.filtration_comparison_of_mem_facetClosure
      C.affineRoot_mem_or_two_smul_mem hClosure α.property).1
        (hz'.2 (a w) ⟨w, hw, rfl⟩)
  exact hRad.le.trans
    ((Subgroup.comap_mono (Subgroup.map_mono
      (sup_le_sup_left (iSup_mono hRoots) H))).trans hRad'.ge)

end Langlands.BruhatTits.IntegralModels
