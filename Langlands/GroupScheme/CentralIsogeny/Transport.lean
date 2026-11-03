import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Isomorphism invariance of central isogenies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G G' H H' : GroupScheme S}

/-- Postcomposing a central isogeny with an isomorphism preserves its full kernel condition. -/
theorem IsCentralIsogeny.comp_iso {f : G ⟶ H} (hf : IsCentralIsogeny f) (e : H ≅ H') :
    IsCentralIsogeny (f ≫ e.hom) := by
  have he := isCentralIsogeny_of_isIso e.hom
  have : LocallyOfFinitePresentation f.hom.hom.left := hf.locallyOfFinitePresentation
  have : LocallyOfFinitePresentation e.hom.hom.hom.left := he.locallyOfFinitePresentation
  refine ⟨hf.isIsogeny.comp he.isIsogeny, ?_, ?_⟩
  · change LocallyOfFinitePresentation (f.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  apply hf.mem_center_of_comp_eq_one
  have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
  apply (cancel_mono e.hom.hom.hom).mp
  change x ≫ (f.hom.hom ≫ e.hom.hom.hom) = 1 at hx
  simpa only [Category.assoc, MonObj.one_comp] using hx

/-- Precomposing with an isomorphism transports central kernel points by the inverse map. -/
theorem IsCentralIsogeny.iso_comp {f : G ⟶ H} (hf : IsCentralIsogeny f) (e : G' ≅ G) :
    IsCentralIsogeny (e.hom ≫ f) := by
  have he := isCentralIsogeny_of_isIso e.hom
  have : LocallyOfFinitePresentation f.hom.hom.left := hf.locallyOfFinitePresentation
  have : LocallyOfFinitePresentation e.hom.hom.hom.left := he.locallyOfFinitePresentation
  refine ⟨he.isIsogeny.comp hf.isIsogeny, ?_, ?_⟩
  · change LocallyOfFinitePresentation (e.hom.hom.hom.left ≫ f.hom.hom.left)
    infer_instance
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  apply (mem_center_comp_iso_iff e x).mp
  apply hf.mem_center_of_comp_eq_one
  exact hx

/-- The converse target-transport comparison follows by composing with the inverse. -/
theorem isCentralIsogeny_comp_iso_iff (f : G ⟶ H) (e : H ≅ H') :
    IsCentralIsogeny (f ≫ e.hom) ↔ IsCentralIsogeny f := by
  constructor
  · intro hf
    simpa only [Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id] using
      hf.comp_iso e.symm
  · exact fun hf => hf.comp_iso e

/-- The converse source-transport comparison follows by composing with the inverse. -/
theorem isCentralIsogeny_iso_comp_iff (f : G ⟶ H) (e : G' ≅ G) :
    IsCentralIsogeny (e.hom ≫ f) ↔ IsCentralIsogeny f := by
  constructor
  · intro hf
    simpa only [Iso.symm_hom, ← Category.assoc, e.inv_hom_id, Category.id_comp] using
      hf.iso_comp e.symm
  · exact fun hf => hf.iso_comp e

end Langlands.GroupScheme
