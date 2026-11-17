import Langlands.GroupScheme.Reductive.AffinePinnedConnectedAlignment
import Langlands.GroupScheme.Reductive.AffinePinnedFppfAutomorphismExtraction
import Langlands.GroupScheme.Reductive.AffinePinnedInnerUniqueness
import Langlands.GroupScheme.Reductive.RelativePinnedExistenceReduction
import Langlands.GroupScheme.Reductive.AffinePinnedAutomorphismAssembly
import Langlands.GroupScheme.Reductive.SemilinearPinningIdentity

/-! # Geometric splitting from local pinned representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- Preservation of the actual canonical cocharacter identifies the canonical
Borel representatives through their dynamic parabolic functors. -/
theorem PreservesCocharacter.preservesBorel {e : Comparison f g}
    (he : PreservesCocharacter e) : PreservesBorel e := by
  have hinv : N.cocharacterOver g ≫ e.inv = M.cocharacterOver f := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hpar := Dynamic.parabolic_eq_comap_of_iso (N.cocharacterOver g) e.symm
  rw [Iso.symm_hom, hinv] at hpar
  have hrep := (M.borelInclusionOver_represents f).comp_iso e
  rw [← hpar] at hrep
  exact ⟨hrep.isoOfIsRepresentedBy (N.borelInclusionOver_represents g),
    (hrep.isoOfIsRepresentedBy_hom_comp (N.borelInclusionOver_represents g)).symm⟩

variable (M : AffinePinnedModel.{u})

/-- On the connected affine original base, fppf-local concrete pinning of the
identity pullback admits a single exact global affine label. -/
theorem exists_pinnedAutomorphism_of_fppfLocallyPinned [ConnectedSpace M.base]
    (σ : CategoryTheory.Aut M.group)
    (hpin : IsFppfLocallyPinned ((baseChange (𝟙 M.base)).mapIso σ)) :
    ∃ θ, M.IsPinnedAutomorphism σ θ := by
  obtain ⟨τ, hτ⟩ := hpin.geometry.1
  obtain ⟨d, hd, _⟩ := exists_basedCoordinateIso_of_connected
    ((baseChange (𝟙 M.base)).mapIso σ) τ hτ hpin.geometry.2.preservesBorel
  exact ⟨d.rootEquiv⁻¹,
    M.isPinnedAutomorphism_of_identityCoordinateIso_of_fppfLocalPinning σ d hd hpin⟩

/-- Conjugating the actual identity pullback by its canonical comparison
recovers the given original automorphism. -/
theorem conjugate_identityBaseChange (σ : CategoryTheory.Aut M.group) :
    (baseChangeIdIso M.group).symm ≪≫ (baseChange (𝟙 M.base)).mapIso σ ≪≫
      baseChangeIdIso M.group = σ := by
  apply Iso.ext
  apply (cancel_epi (baseChangeIdIso M.group).hom).mp
  have hn := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫
    Functor.mapGrpIdIso).hom.naturality σ.hom
  change (baseChange (𝟙 M.base)).map σ.hom ≫ (baseChangeIdIso M.group).hom =
    (baseChangeIdIso M.group).hom ≫ σ.hom at hn
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc] using hn

/-- An arbitrary automorphism of the identity pullback is the actual pullback
of its transport to the original model. -/
theorem identityBaseChange_original (e : Comparison (M := M) (N := M)
    (𝟙 M.base) (𝟙 M.base)) :
    (baseChange (𝟙 M.base)).mapIso
      ((baseChangeIdIso M.group).symm ≪≫ e ≪≫ baseChangeIdIso M.group) = e := by
  let σ : CategoryTheory.Aut M.group :=
    (baseChangeIdIso M.group).symm ≪≫ e ≪≫ baseChangeIdIso M.group
  have hn := ((Functor.mapGrpNatIso Over.pullbackId) ≪≫
    Functor.mapGrpIdIso).hom.naturality σ.hom
  change (baseChange (𝟙 M.base)).map σ.hom ≫ (baseChangeIdIso M.group).hom =
    (baseChangeIdIso M.group).hom ≫ σ.hom at hn
  apply Iso.ext
  apply (cancel_mono (baseChangeIdIso M.group).hom).mp
  simpa only [σ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc] using hn

/-- Inner equivalence of actual identity pullbacks reflects to the original
automorphisms through the canonical comparison. -/
theorem innerEquivalent_of_identityBaseChange
    {σ τ : CategoryTheory.Aut M.group}
    (h : IsFppfInnerEquivalent ((baseChange (𝟙 M.base)).mapIso σ)
      ((baseChange (𝟙 M.base)).mapIso τ)) : IsFppfInnerEquivalent σ τ := by
  have hp := (h.precomp (baseChangeIdIso M.group).symm).postcomp (baseChangeIdIso M.group)
  simpa only [Iso.trans_assoc, M.conjugate_identityBaseChange] using hp

variable {Gad : GroupScheme M.base} (p : M.group ⟶ Gad)
  (hp : RelativeRoot.IsFppfQuotient (center M.group) p)
  (c : AutomorphicAction Gad M.group)
  (hc : c.restrict p = AutomorphicAction.conjugation (𝟙 M.group))

include p hp hc in
/-- An exact pinned automorphism in the adjoint action image has identity
label, by fppf-local pinned inner rigidity. -/
theorem IsPinnedAutomorphism.label_eq_one_of_inner [Nonempty M.base]
    {σ : CategoryTheory.Aut M.group} {θ : RootPairing.Aut M.rootDatum}
    (hpin : M.IsPinnedAutomorphism σ θ) (hinner : σ ∈ c.basePointHom.range) : θ = 1 := by
  obtain ⟨x, hx⟩ := hinner
  have hi : IsFppfLocallyInner σ :=
    IsFppfLocallyInner.of_adjointPoint p hp c hc x hx
  have he := eq_refl_of_fppfLocallyPinned_locallyInner
    (hpin.fppfLocallyPinned_baseChange M (𝟙 M.base)) (hi.baseChange (𝟙 M.base))
  have hσ : σ = 1 := by
    apply Iso.ext
    apply Descent.baseChangeEqIdentity_map_injective (𝟙 M.base) rfl
    change (baseChange (𝟙 M.base)).map σ.hom =
      (baseChange (𝟙 M.base)).map (𝟙 M.group)
    rw [CategoryTheory.Functor.map_id]
    simpa only [Functor.mapIso_hom, Iso.refl_hom] using
      congrArg Iso.hom he
  exact hpin.label_eq_one_of_eq_one M hσ

include p hp hc in
/-- Local pinned representatives imply both geometric inputs to the affine
automorphism-group splitting, over the connected original base. -/
theorem automorphismSplittingGeometry_of_localPinnedRepresentatives
    [ConnectedSpace M.base] (hlocal : HasFppfLocalPinnedRepresentatives.{u}) :
    M.AutomorphismSplittingGeometry c := by
  constructor
  · intro σ
    obtain ⟨d, ⟨hdpin, hi⟩, _⟩ :=
      hasUniquePinnedComparisons_of_localPinnedRepresentatives hlocal
        M M (𝟙 M.base) (𝟙 M.base) ((baseChange (𝟙 M.base)).mapIso σ)
    let τ : CategoryTheory.Aut M.group :=
      (baseChangeIdIso M.group).symm ≪≫ d ≪≫ baseChangeIdIso M.group
    have hτ : (baseChange (𝟙 M.base)).mapIso τ = d :=
      M.identityBaseChange_original d
    have hτpin : IsFppfLocallyPinned ((baseChange (𝟙 M.base)).mapIso τ) := by
      rwa [hτ]
    obtain ⟨θ, hθ⟩ := M.exists_pinnedAutomorphism_of_fppfLocallyPinned τ hτpin
    have hi' : IsFppfInnerEquivalent σ τ := by
      apply M.innerEquivalent_of_identityBaseChange
      rwa [hτ]
    obtain ⟨x, hx, _⟩ := hi'.inv.symm.existsUnique_adjointPoint p hp c hc
    refine ⟨θ, hθ.based M, τ, hθ, c.basePointHom x, ⟨x, rfl⟩, ?_⟩
    change c.basePointHom x = σ * τ⁻¹ at hx
    rw [hx]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  · intro σ θ hpin hi
    exact hpin.label_eq_one_of_inner M p hp c hc hi

include p hp c hc in
/-- The actual outer root-datum projection constructed from pinned full
faithfulness and local pinned-representative existence. -/
def automorphismProjectionOfLocalPinnedRepresentatives
    [ConnectedSpace M.base]
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (hlocal : HasFppfLocalPinnedRepresentatives.{u}) :
    CategoryTheory.Aut M.group →* RootPairing.Aut M.rootDatum :=
  M.automorphismProjection p hp hc hiso
    (M.automorphismSplittingGeometry_of_localPinnedRepresentatives p hp c hc hlocal)

include p hp c hc in
/-- The constructed projection has exactly the adjoint action image as kernel. -/
theorem automorphismProjectionOfLocalPinnedRepresentatives_ker
    [ConnectedSpace M.base]
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (hlocal : HasFppfLocalPinnedRepresentatives.{u}) :
    (M.automorphismProjectionOfLocalPinnedRepresentatives p hp c hc hiso hlocal).ker =
      c.basePointHom.range :=
  M.automorphismProjection_ker p hp hc hiso
    (M.automorphismSplittingGeometry_of_localPinnedRepresentatives p hp c hc hlocal)

end AffinePinnedModel

/-- The unchanged affine automorphism-group target follows from pinned full
faithfulness and the independent existence of local pinned representatives. -/
theorem affinePinnedAutomorphismGroup_of_localPinnedRepresentatives
    (hiso : AffinePinnedIsomorphismTheoremStatement.{u})
    (hlocal : AffinePinnedModel.HasFppfLocalPinnedRepresentatives.{u}) :
    AffinePinnedAutomorphismGroupStatement.{u} :=
  affinePinnedAutomorphismGroup_of_splitting hiso
    (fun M _ _Gad p hp c hc =>
      M.automorphismSplittingGeometry_of_localPinnedRepresentatives p hp c hc hlocal)

end Langlands.GroupScheme
