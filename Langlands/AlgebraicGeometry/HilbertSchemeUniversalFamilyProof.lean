import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement
import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily.ProjectivePieces
import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily.Globalization
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj

/-! # The Hilbert scheme of a projective flat family on all test schemes: proof

The Hilbert scheme is the disjoint union `∐ C θ` of the per-polynomial Hilbert schemes of the
ported FLT development, which are H-projective by
`exists_isHProjective_hilbertPolynomial_piece`. The FLT development supplies the classifier on
affine tests and the universal closed subscheme `𝒵`; `classification` turns the kernel of
`𝒵 ⟶ X ×_A H` into the universal ideal sheaf on all test schemes. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open P2MW.S_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj

noncomputable section

namespace Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily

set_option maxHeartbeats 1600000 in
/-- The Hilbert scheme of a flat, locally finitely presented family over a ring that is
embedded in projective space by the sections of an invertible module exists on all test
schemes, with its universal ideal sheaf and H-projective Hilbert-polynomial pieces. -/
theorem hilbertSchemeUniversalFamily : HilbertSchemeUniversalFamilyStatement.{u} := by
  intro A _ X f 𝓛X hfl hfp hX₁ hX₂
  have := hfl
  have := hfp
  choose C πC ptC hC using fun P : Polynomial ℚ =>
    exists_isHProjective_hilbertPolynomial_piece A f 𝓛X hX₁ hX₂ P
  obtain ⟨pt, hnat, hconst⟩ :=
    AlgebraicGeometry.exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq
      A f 𝓛X hX₁ hX₂ C πC ptC (fun P => (hC P).1)
  let F : H1SIC.Fam f 𝓛X := ⟨C, πC, ptC, fun P => (hC P).1, fun P => (hC P).2.1,
    fun P => (hC P).2.2.1, fun P => (hC P).2.2.2.1, fun P => (hC P).2.2.2.2.1, pt, hnat, hconst⟩
  have hsurj : ClassifierSurj f (Sigma.desc πC) pt := fun S' _ s x => F.surj s x
  obtain ⟨𝒵, ι, hι, hfl𝒵, hfp𝒵, huniv⟩ :=
    AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point
      A f (Sigma.desc πC) pt hnat hsurj
      (fun S' _ s Z Z' ι ι' hι hι' hfl hfl' hfp hfp' h =>
        F.inj hX₁ hX₂ s Z Z' ι ι' hι hι' hfl hfl' hfp hfp' h)
  have := hι
  have hcls := fun T s => classification hnat hsurj huniv hfl𝒵 hfp𝒵 T s
  have hproper : ∀ P, IsProper (πC P) := fun P => (hC P).2.2.2.1
  -- Instance search does not find this instance here, so it is supplied explicitly.
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  refine ⟨∐ C, Sigma.desc πC, ι.ker,
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation)
      (fun P => (hC P).2.2.2.2.1),
    AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated C πC (fun P => inferInstance),
    fun T s => hcls T s, fun θ => (Sigma.ι C θ).opensRange,
    fun P Q h => disjoint_opensRange_sigmaι C P Q h,
    (AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma C
      (𝟙 (∐ C))).2.2.1, fun θ => ⟨?_, ?_⟩⟩
  · have he : (Sigma.ι C θ).opensRange.ι ≫ Sigma.desc πC =
        (Sigma.ι C θ).isoOpensRange.inv ≫ πC θ := by
      rw [← Scheme.Hom.isoOpensRange_inv_comp_assoc, Sigma.ι_comp_desc]
    rw [he]
    obtain ⟨n, i, hi, hiπ⟩ := (hC θ).2.2.2.2.2
    have := hi
    exact ⟨n, (Sigma.ι C θ).isoOpensRange.inv ≫ i, inferInstance, by rw [Category.assoc, hiπ]⟩
  · intro B _ s g hg I hI
    obtain ⟨hflI, hfpI⟩ : Flat (I.subschemeι ≫ pullback.snd f s) ∧
        LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f s) := by
      rw [← hI]
      exact (hcls _ s).1 g hg
    rw [eq_pt hnat hsurj huniv s g hg I hflI hfpI hI]
    exact (F.pieces hX₁ hX₂ θ).2.2 B s I.subscheme I.subschemeι inferInstance hflI hfpI

end Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily
