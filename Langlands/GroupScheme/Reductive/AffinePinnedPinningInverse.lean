import Langlands.GroupScheme.Reductive.AffinePinnedFppfPinning

/-! # Inverses of concrete pinned comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- The inverse torus square uses the inverse of the supplied torus isomorphism. -/
theorem PreservesTorus.symm {e : Comparison f g} (he : PreservesTorus e) :
    PreservesTorus e.symm := by
  obtain ⟨τ, hτ⟩ := he
  refine ⟨τ.symm, ?_⟩
  apply (cancel_mono e.hom).mp
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hτ, Iso.inv_hom_id_assoc]

/-- Cocharacter preservation is closed under inversion. -/
theorem PreservesCocharacter.symm {e : Comparison f g}
    (he : PreservesCocharacter e) : PreservesCocharacter e.symm := by
  change N.cocharacterOver g ≫ e.inv = M.cocharacterOver f
  rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The bijection on simple vectors can be inverted separately on each local test. -/
theorem PreservesLocalPinning.symm {e : Comparison f g}
    (he : PreservesLocalPinning e) : PreservesLocalPinning e.symm := by
  intro A _ _ _ _ a hb ha
  obtain ⟨σ, hσ⟩ := he A a ha hb
  refine ⟨σ.symm, fun s => ?_⟩
  have hv := congrArg (fun k => k ≫ e.inv.hom.hom.left) (hσ (σ.symm s))
  simpa only [Iso.symm_hom, Equiv.apply_symm_apply, Category.assoc, ← Grp.comp_hom_hom,
    ← Over.comp_left, Iso.hom_inv_id, Grp.id_hom_hom, Over.id_left,
    Category.comp_id] using hv.symm

/-- A concrete pinned comparison has a concrete pinned inverse. -/
theorem IsLocallyPinned.symm {e : Comparison f g}
    (he : IsLocallyPinned e) : IsLocallyPinned e.symm :=
  ⟨he.1.symm, he.2.1.symm, he.2.2.symm⟩

/-- The same fppf cover witnesses pinning preservation for the inverse. -/
theorem IsFppfLocallyPinned.symm {e : Comparison f g}
    (he : IsFppfLocallyPinned e) : IsFppfLocallyPinned e.symm := by
  obtain ⟨U, q, hf, hs, hl, hq⟩ := he
  refine ⟨U, q, hf, hs, hl, ?_⟩
  rw [pullComparison_symm]
  exact hq.symm

end Langlands.GroupScheme.AffinePinnedModel
