import Langlands.AlgebraicGeometry.LinearSystem.RelativeMorphism
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof

/-! # Linear-system morphisms under line-bundle isomorphisms -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false

variable {X T : Scheme.{u}} {L M : LineBundle X} {n : ℕ}
  {s : Fin (n + 1) → GlobalSections L.obj}

/-- Transport the specified sections through an isomorphism of module sheaves. -/
def mapIsoSections (e : L.obj ≅ M.obj) (s : Fin (n + 1) → GlobalSections L.obj) :
    Fin (n + 1) → GlobalSections M.obj :=
  fun i ↦ e.hom.app ⊤ (s i)

/-- A line-bundle isomorphism preserves generation by the specified sections. -/
lemma mapIsoSections_generate (e : L.obj ≅ M.obj)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    ∀ x : X, ∃ i, x ∈ nonvanishingLocus M.obj (mapIsoSections e s i) := by
  intro x
  obtain ⟨i, hi⟩ := exists_mem_trivializationOpen hs x
  refine ⟨i, ?_⟩
  rw [lineBundleResidueOpenComparison, mapIsoSections, trivializationOpen_mapIso]
  exact hi

/-- Ratios of sections are unchanged under an isomorphism of the line bundle. -/
lemma sectionRatio_mapIso (e : L.obj ≅ M.obj) (g : T ⟶ X)
    (σ s₀ : GlobalSections L.obj)
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) :
    sectionRatio M g (e.hom.app ⊤ σ) (e.hom.app ⊤ s₀) =
      sectionRatio L g σ s₀ := by
  have hg' : ∀ t, g t ∈ trivializationOpen M.obj (e.hom.app ⊤ s₀) := by
    simpa only [trivializationOpen_mapIso] using hg
  apply (sectionRatio_eq_iff hg' _ _).mpr
  rw [pullbackSection_naturality, pullbackSection_naturality,
    ← Scheme.Modules.Hom.app_smul, sectionRatio_smul hg]

/-- The chart point map is unchanged after an isomorphism of line bundles. -/
lemma pointMap_mapIso {K : Type u} [CommRing K]
    (p : X ⟶ Spec (CommRingCat.of K)) (e : L.obj ≅ M.obj) (g : T ⟶ X)
    (i : Fin (n + 1)) (hg : ∀ t, g t ∈ trivializationOpen L.obj (s i)) :
    pointMap (L := M) p (mapIsoSections e s) g i
        (fun t ↦ by simpa only [mapIsoSections, trivializationOpen_mapIso] using hg t) =
      pointMap p s g i hg := by
  unfold pointMap
  apply chartMap_ringHom_congr
  apply MvPolynomial.ringHom_ext
  · intro k
    simp only [chartRingHom_C]
  · intro j
    simp only [chartRingHom_X]
    exact sectionRatio_mapIso e g (s j) (s i) hg

/-- The actual scheme map of a linear system is unchanged by a line-bundle
isomorphism carrying all its specified sections. -/
lemma linearSystemMap_mapIso {K : Type u} [CommRing K]
    (p : X ⟶ Spec (CommRingCat.of K)) (e : L.obj ≅ M.obj)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    linearSystemMap p (mapIsoSections_generate e hs) = linearSystemMap p hs := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨i, hi⟩ := exists_mem_trivializationOpen hs x
  refine ⟨trivializationOpen L.obj (s i), hi, ?_⟩
  rw [comp_linearSystemMap p (mapIsoSections_generate e hs) _ i
    (fun t ↦ by simpa only [mapIsoSections, trivializationOpen_mapIso] using
      (ι_mem (trivializationOpen L.obj (s i)) t)),
    pointMap_mapIso, comp_linearSystemMap p hs _ i (ι_mem _)]

/-- Relative linear-system maps are likewise invariant under a section-preserving
isomorphism of the defining line bundle. -/
lemma relativeLinearSystemMap_mapIso {S : Scheme.{u}} (p : X ⟶ S)
    (e : L.obj ≅ M.obj)
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    relativeLinearSystemMap p (mapIsoSections_generate e hs) =
      relativeLinearSystemMap p hs := by
  apply RelativeProjectiveSpace.hom_ext
  · simp
  · simp only [relativeLinearSystemMap_toIntegral, integralLinearSystemMap]
    exact linearSystemMap_mapIso _ e hs

end Langlands.AlgebraicGeometry.LinearSystem
