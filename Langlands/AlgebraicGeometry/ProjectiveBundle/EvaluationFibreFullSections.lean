import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationFibreBasis

/-! # Full fibre sections under the canonical comparison isomorphism -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.LinearSystem
open Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

private def specSectionBasis {R : CommRingCat.{u}} {N : (Spec R).Modules}
    {I : Type v} (b : Module.Basis I Γ(Spec R, ⊤) (GlobalSections N)) :
    Module.Basis I R (moduleSpecΓFunctor.obj N) :=
  b.mapCoeffs (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv (by
    intro c x
    change (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom c) • x = c • x
    rw [Iso.hom_inv_id_apply])

private lemma specSectionBasis_apply {R : CommRingCat.{u}} {N : (Spec R).Modules}
    {I : Type v} (b : Module.Basis I Γ(Spec R, ⊤) (GlobalSections N)) (i : I) :
    specSectionBasis b i = b i := by
  unfold specSectionBasis
  exact Module.Basis.mapCoeffs_apply (M := GlobalSections N) _ _ _ i

variable {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)
    {M : S.Modules} [M.IsQuasicoherent]
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj) {n : ℕ}

/-- Transport the actual coefficient basis through the canonical comparison,
retaining its invertibility as an explicit premise. -/
def fibreFullSectionBasis (U : FrameOpen M n) (hU : IsAffineOpen U.val)
    (s : S) (hs : s ∈ U.val)
    [IsIso (baseChangeEvaluation p L ev (S.fromSpecResidueField s)
      (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s))] :
    Module.Basis (Fin (n + 1)) (S.residueField s)
      ((relativeGlobalSections (p.fiberToSpecResidueField s)).obj
        ((LineBundle.pullback (p.fiberι s)).obj L).obj) :=
  specSectionBasis ((fibreFrameBasis U hU s hs).map
    ((globalSections (Spec (S.residueField s))).mapIso
      (asIso (baseChangeEvaluation p L ev (S.fromSpecResidueField s)
        (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s)))).toLinearEquiv)

/-- This full basis consists of the actual canonical changed evaluation sections. -/
@[simp]
lemma fibreFullSectionBasis_apply (U : FrameOpen M n) (hU : IsAffineOpen U.val)
    (s : S) (hs : s ∈ U.val)
    [IsIso (baseChangeEvaluation p L ev (S.fromSpecResidueField s)
      (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s))]
    (i : Fin (n + 1)) :
    fibreFullSectionBasis p L ev U hU s hs i = fibreFrameEvaluation p L ev U s hs i := by
  unfold fibreFullSectionBasis
  erw [specSectionBasis_apply, Module.Basis.map_apply, fibreFrameBasis_apply]
  rfl

variable (hgen : FrameEvaluationGenerates p L ev n)

include hgen in
/-- The full section basis generates whenever the original frame evaluation does. -/
lemma fibreFullSectionBasis_generate (U : FrameOpen M n) (hU : IsAffineOpen U.val)
    (s : S) (hs : s ∈ U.val)
    [IsIso (baseChangeEvaluation p L ev (S.fromSpecResidueField s)
      (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s))] :
    ∀ x : p.fiber s, ∃ i, x ∈ nonvanishingLocus
      ((LineBundle.pullback (p.fiberι s)).obj L).obj
      (fibreFullSectionBasis p L ev U hU s hs i) := by
  simpa only [fibreFullSectionBasis_apply] using
    fibreFrameEvaluation_generate p L ev hgen U s hs

/-- Under the retained canonical comparison hypothesis, global evaluation on a
fibre is the relative linear system of a basis of all fibre sections. -/
lemma fibreFullSectionBasis_coordinates (U : FrameOpen M n) (hU : IsAffineOpen U.val)
    (s : S) (hs : s ∈ U.val)
    [IsIso (baseChangeEvaluation p L ev (S.fromSpecResidueField s)
      (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s))] :
    relativeLinearSystemMap (p.fiberToSpecResidueField s)
        (fibreFullSectionBasis_generate p L ev hgen U hU s hs) =
      fibreEvaluationCoordinates p L ev hgen U s hs := by
  have he : (fun i => fibreFullSectionBasis p L ev U hU s hs i) =
      fibreFrameEvaluation p L ev U s hs := by
    funext i
    exact fibreFullSectionBasis_apply p L ev U hU s hs i
  simpa only [← he] using fibreFrameEvaluation_coordinates p L ev hgen U s hs

end Langlands.AlgebraicGeometry.ProjectiveBundle
