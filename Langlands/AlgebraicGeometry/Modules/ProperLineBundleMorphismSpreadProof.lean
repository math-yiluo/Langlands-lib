import Langlands.AlgebraicGeometry.Modules.ProperLineBundleMorphismSpreadStatement
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen

/-! # Proper spreading of an actual line-bundle frame -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules

/-- A frame of the fibre that comes from an actual section spreads under a
universally closed structure map. -/
theorem properLineBundleMorphismSpread :
    ProperLineBundleMorphismSpreadStatement.{u} := by
  intro X S f hf L φ s hs
  let : UniversallyClosed f := hf
  let : IsIso ((Scheme.Modules.pullback (f.fiberι s)).map φ) := hs
  let σ : GlobalSections L.obj := (sectionHomEquiv L.obj).symm φ
  have hσ : sectionHom L.obj σ = φ := (sectionHomEquiv L.obj).apply_symm_apply φ
  let W : Set X := {x | IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    ((Scheme.Modules.toPresheaf X).map φ))}
  have hW : IsOpen W := by
    simpa only [IsStalkFrame, hσ] using isOpen_lineBundle_stalkFrame L σ
  have hfibre : f ⁻¹' {s} ⊆ W := by
    intro x hx
    rw [← f.range_fiberι s] at hx
    obtain ⟨y, rfl⟩ := hx
    exact (pullback_stalk_isIso_iff (f.fiberι s) L.property φ y).mp (by infer_instance)
  let U : S.Opens := ⟨(f '' Wᶜ)ᶜ, (f.isClosedMap _ hW.isClosed_compl).isOpen_compl⟩
  have hsU : s ∈ U := by
    rintro ⟨x, hx, hxs⟩
    exact hx (hfibre hxs)
  refine ⟨U, hsU, (isIso_iff_stalk_isIso _).mpr ?_⟩
  intro y
  apply (pullback_stalk_isIso_iff (pullback.fst f U.ι) L.property φ y).mpr
  change (pullback.fst f U.ι) y ∈ W
  by_contra hy
  have hyU := ((pullback.snd f U.ι) y).property
  apply hyU
  refine ⟨(pullback.fst f U.ι) y, hy, ?_⟩
  exact congrArg (fun k : pullback f U.ι ⟶ S ↦ k y) pullback.condition

end Langlands.AlgebraicGeometry.Modules
