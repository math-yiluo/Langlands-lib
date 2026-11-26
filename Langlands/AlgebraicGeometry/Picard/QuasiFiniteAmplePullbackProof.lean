import Langlands.AlgebraicGeometry.Picard.QuasiFiniteAmplePullbackStatement
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen
import Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisProof
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Proof that quasi-finite separated pullback preserves ampleness -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- Pullback along a quasi-compact open immersion preserves ampleness. -/
theorem LineBundle.IsAmple.pullback_of_isOpenImmersion
    {X Y : Scheme.{u}} {L : LineBundle X} (hL : L.IsAmple)
    (f : Y ⟶ X) [IsOpenImmersion f] [QuasiCompact f] :
    ((LineBundle.pullback f).obj L).IsAmple := by
  let : CompactSpace X := hL.compactSpace
  refine ⟨QuasiCompact.compactSpace_of_compactSpace f, fun y ↦ ?_⟩
  obtain ⟨m, hm, t, hyt, ht⟩ := hL.exists_section (f y)
  obtain ⟨n, hn, s, hys, hsW⟩ :=
    ampleSectionOpenBasis X L hL (f.opensRange ⊓ L.sectionOpen t) (f y) ⟨⟨y, rfl⟩, hyt⟩
  have haff : IsAffineOpen (L.sectionOpen s) := by
    have h := affineGenerationLocusIntersection X
      ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩ s (L.sectionOpen t) ht
    change IsAffineOpen (L.sectionOpen t ⊓ L.sectionOpen s) at h
    rwa [inf_eq_right.mpr (hsW.trans inf_le_right)] at h
  refine ⟨n, hn, L.pullbackPowSection f s, ?_, ?_⟩
  · rw [LineBundle.sectionOpen_pullbackPowSection]
    exact hys
  · rw [LineBundle.sectionOpen_pullbackPowSection, ← f.isAffineOpen_iff_of_isOpenImmersion,
      f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr (hsW.trans inf_le_left)]
    exact haff

/-- Pulling back an ample line bundle along a quasi-finite separated morphism gives an
ample line bundle: the morphism factors as a quasi-compact open immersion into its
normalization followed by an integral, hence affine, morphism. -/
theorem quasiFiniteAmplePullback : QuasiFiniteAmplePullbackStatement.{u} := by
  intro X Y f M hft hqf hqc hsep hM
  let := hft
  let := hqf
  let := hqc
  let := hsep
  have h₁ : ((LineBundle.pullback f.fromNormalization).obj M).IsAmple :=
    hM.pullback_of_isAffineHom f.fromNormalization
  have h₂ := h₁.pullback_of_isOpenImmersion f.toNormalization
  exact h₂.of_iso ((LineBundle.forget X).mapIso
    ((LineBundle.pullbackComp f.toNormalization f.fromNormalization).app M ≪≫
      eqToIso (congrArg (fun g ↦ (LineBundle.pullback g).obj M)
        (Scheme.Hom.toNormalization_fromNormalization f))))

end Langlands.AlgebraicGeometry.Picard
