import Langlands.AlgebraicGeometry.FibralIsomorphismStatement
import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion

/-! # The fibral isomorphism criterion -/

universe u

open CategoryTheory Limits

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Conrad's fibral isomorphism criterion, over an arbitrary base scheme. -/
theorem fibralIsomorphism : FibralIsomorphismStatement.{u} := by
  intro S Y Y' h hY hY' hflat hf
  have := hY
  have := hY'
  have := hflat
  have hopen : IsOpenImmersion h.left :=
    isOpenImmersion_of_fiberwise h fun s => by
      have := hf s
      infer_instance
  have hsurj : Surjective h.left := by
    refine ⟨fun y => ?_⟩
    let s : S := Y'.hom y
    obtain ⟨y', hy', -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Y'.hom) (g := S.fromSpecResidueField s) y
      (IsLocalRing.closedPoint (S.residueField s)) (Scheme.fromSpecResidueField_apply _ _).symm
    have := hf s
    obtain ⟨x', hx'⟩ :=
      (((Over.pullback (S.fromSpecResidueField s)).map h).left).surjective y'
    have key : pullback.fst Y.hom (S.fromSpecResidueField s) ≫ h.left =
        ((Over.pullback (S.fromSpecResidueField s)).map h).left ≫
          pullback.fst Y'.hom (S.fromSpecResidueField s) := by
      exact (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst Y.hom (S.fromSpecResidueField s) x', ?_⟩
    rw [← hy', ← hx', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, key]
  exact (isIso_iff_isOpenImmersion_and_surjective h.left).mpr ⟨hopen, hsurj⟩

end Langlands.AlgebraicGeometry
