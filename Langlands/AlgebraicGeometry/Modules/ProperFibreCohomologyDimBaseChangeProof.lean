import Langlands.AlgebraicGeometry.Modules.ProperFibreCohomologyDimBaseChangeStatement
import Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityProof

/-! # Invariance of fibre cohomology dimensions under base change: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.FibreDimension

namespace Langlands.AlgebraicGeometry.Modules

open DerivedSections FibreSemicontinuity

attribute [local instance] HasDerivedCategory.standard

/-- Fibre cohomology dimensions are invariant under base change. -/
theorem properFibreCohomologyDimBaseChange :
    ProperFibreCohomologyDimBaseChangeStatement.{u} := by
  intro T T' Y Y' g h g' h' hsq hg F hF t' p
  -- the fibre `Y_t` over `t = h t'` and a perfect model of `F_t` over `κ(t)`
  let f := pullback.snd g (T.fromSpecResidueField (h t'))
  let a := pullback.fst g (T.fromSpecResidueField (h t'))
  obtain ⟨K, hK, hmod⟩ := exists_perfectModel f ((Scheme.Modules.pullback a).obj F)
    (hF.pullback a)
  have : ∀ i, Module.Finite (T.residueField (h t')) (K.X i) := fun i => (hK.2 i).1
  -- the fibre over `t` itself: base change along the identity of `κ(t)`
  have hdim₀ : (fibreCohomologyDim g (h t') F p : ℤ) =
      homologyDim K p (kerPrime (𝟙 (T.residueField (h t'))).hom) := by
    obtain ⟨e₀⟩ := hmod _ (𝟙 _)
    have hsq₀ : IsPullback (𝟙 _) f f (Spec.map (𝟙 (T.residueField (h t')))) := by
      rw [Spec.map_id]
      exact IsPullback.id_horiz f
    obtain ⟨c₀⟩ := nonempty_relativeCohomology_iso_chosenPullback hsq₀
      ((Scheme.Modules.pullback a).obj F) p
    let E : fibreCohomology g (h t') F p ≅
        ((ModuleComplex.baseChange (𝟙 (T.residueField (h t'))).hom).obj K).homology p :=
      (relativeCohomology f p).mapIso
          ((Scheme.Modules.pullbackId _).app ((Scheme.Modules.pullback a).obj F)).symm ≪≫ c₀ ≪≫
        (DerivedPlus.homologyIsoOfIsoDerivedComplex _ e₀ p).symm
    rw [fibreCohomologyDim, E.toLinearEquiv.finrank_eq]
    exact finrank_homology_baseChange_eq K _ p
  -- the fibre over `t'`: base change along the residue field extension `κ(t) → κ(t')`
  have hdim₁ : (fibreCohomologyDim g' t' ((Scheme.Modules.pullback h').obj F) p : ℤ) =
      homologyDim K p (kerPrime (h.residueFieldMap t').hom) := by
    obtain ⟨e₁⟩ := hmod _ (h.residueFieldMap t')
    have hbig : IsPullback (pullback.fst f (Spec.map (h.residueFieldMap t')) ≫ a)
        (pullback.snd f (Spec.map (h.residueFieldMap t'))) g
        (T'.fromSpecResidueField t' ≫ h) := by
      have := (IsPullback.of_hasPullback f (Spec.map (h.residueFieldMap t'))).paste_horiz
        (IsPullback.of_hasPullback g (T.fromSpecResidueField (h t')))
      rwa [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at this
    have hsq₁ := IsPullback.of_right' hbig hsq
    obtain ⟨c₁⟩ := nonempty_relativeCohomology_iso_chosenPullback hsq₁
      ((Scheme.Modules.pullback h').obj F) p
    have hlift : hsq.lift (pullback.fst f (Spec.map (h.residueFieldMap t')) ≫ a)
        (pullback.snd f (Spec.map (h.residueFieldMap t')) ≫ T'.fromSpecResidueField t')
        (by rw [hbig.w, Category.assoc]) ≫ h' =
          pullback.fst f (Spec.map (h.residueFieldMap t')) ≫ a := hsq.lift_fst _ _ _
    let E : fibreCohomology g' t' ((Scheme.Modules.pullback h').obj F) p ≅
        ((ModuleComplex.baseChange (h.residueFieldMap t').hom).obj K).homology p :=
      c₁.symm ≪≫ (relativeCohomology _ p).mapIso
          ((Scheme.Modules.pullbackComp _ _).app F ≪≫
            (Scheme.Modules.pullbackCongr hlift).app F ≪≫
            ((Scheme.Modules.pullbackComp _ _).app F).symm) ≪≫
        (DerivedPlus.homologyIsoOfIsoDerivedComplex _ e₁ p).symm
    rw [fibreCohomologyDim, E.toLinearEquiv.finrank_eq]
    exact finrank_homology_baseChange_eq K _ p
  -- both kernels are zero
  have hker : kerPrime (h.residueFieldMap t').hom = kerPrime (𝟙 (T.residueField (h t'))).hom := by
    apply PrimeSpectrum.ext
    change RingHom.ker _ = RingHom.ker _
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (h.residueFieldMap t').hom.injective,
      (RingHom.injective_iff_ker_eq_bot _).1 (𝟙 (T.residueField (h t'))).hom.injective]
  have := hdim₀.trans (hker ▸ hdim₁.symm)
  exact_mod_cast this.symm

end Langlands.AlgebraicGeometry.Modules
