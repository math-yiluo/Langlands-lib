import Langlands.AlgebraicGeometry.Modules.SectionResidue
import Mathlib.AlgebraicGeometry.Fiber

/-! # Restriction of neighbourhood sections to an actual fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

open Langlands.SchemeModule

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)

/-- The actual fibre is contained in the inverse image of every base
neighbourhood of its base point. -/
lemma fibre_preimage_neighbourhood {V : S.Opens} (hs : s ∈ V) :
    (⊤ : (f.fiber s).Opens) ≤ f.fiberι s ⁻¹ᵁ (f ⁻¹ᵁ V) := by
  intro x _
  have hx : f (f.fiberι s x) = s := by
    have h : f.fiberι s x ∈ Set.range (f.fiberι s) := Set.mem_range_self x
    rwa [f.range_fiberι] at h
  change f (f.fiberι s x) ∈ V
  rwa [hx]

/-- The canonical restriction of a section over the inverse image of a
base neighbourhood to the scheme-theoretic residue-field fibre. -/
def fibreNeighbourhoodSection (M : X.Modules) {V : S.Opens} (hs : s ∈ V)
    (t : Γ(M, f ⁻¹ᵁ V)) :
    GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj M) :=
  ((Scheme.Modules.pullback (f.fiberι s)).obj M).presheaf.map
    (homOfLE (fibre_preimage_neighbourhood f s hs)).op
      ((((Scheme.Modules.pullbackPushforwardAdjunction (f.fiberι s)).unit.app M).app
        (f ⁻¹ᵁ V)) t)

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting a neighbourhood section to a smaller neighbourhood does
not change its actual fibre restriction. -/
lemma fibreNeighbourhoodSection_restrict (M : X.Modules) {V W : S.Opens}
    (hsV : s ∈ V) (hsW : s ∈ W) (hWV : W ≤ V) (t : Γ(M, f ⁻¹ᵁ V)) :
    fibreNeighbourhoodSection f s M hsW
        (M.presheaf.map (homOfLE (f.preimage_mono hWV)).op t) =
      fibreNeighbourhoodSection f s M hsV t := by
  let η := (Scheme.Modules.pullbackPushforwardAdjunction (f.fiberι s)).unit.app M
  have hn := η.mapPresheaf.naturality
    (homOfLE (f.preimage_mono hWV)).op
  have he := ConcreteCategory.congr_hom hn t
  dsimp only [Functor.comp_obj, Functor.comp_map] at he
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at he
  let N := (Scheme.Modules.pullback (f.fiberι s)).obj M
  let a := homOfLE (fibre_preimage_neighbourhood f s hsW)
  let b := (TopologicalSpace.Opens.map (f.fiberι s).base).map
    (homOfLE (f.preimage_mono hWV))
  let v : Γ(N, f.fiberι s ⁻¹ᵁ (f ⁻¹ᵁ V)) := η.app (f ⁻¹ᵁ V) t
  have hc := ConcreteCategory.congr_hom (N.presheaf.map_comp b.op a.op) v
  exact (congrArg (fun q => N.presheaf.map a.op q) he).trans hc.symm

end Langlands.AlgebraicGeometry.Modules
