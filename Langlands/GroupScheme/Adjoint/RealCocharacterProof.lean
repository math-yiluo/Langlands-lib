import Langlands.GroupScheme.Adjoint.RealCocharacterStatement
import Langlands.GroupScheme.Adjoint.RealCocharacterKernel
import Langlands.GroupScheme.Rational.SplitTorusSurjection

/-! # The actual adjoint real cocharacter comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

/-- The actual adjoint torus map is real-surjective, has exactly the relative
root-annihilator kernel, and induces the required KP translation equivalence. -/
theorem adjointRealCocharacterComparison : AdjointRealCocharacterComparisonStatement.{u} := by
  intro k _ G A T T_ad q i j p h
  let := h.isAdjointQuotient.isConnectedReductive.isAffineHom
  let := h.flat
  let := h.surjective
  let := h.locallyOfFinitePresentation
  have hs := cocharacterMapReal_surjective_of_fppf
    h.sourceMaximal.1.1 h.targetMaximal.1.1 p
  have hk := h.ker_cocharacterMapReal_eq_relativeCentralDirections
  refine ⟨hs, hk, ?_⟩
  refine ⟨(Submodule.quotEquivOfEq _ _ hk.symm).trans
    (cocharacterQuotientEquivOfFppf h.sourceMaximal.1.1 h.targetMaximal.1.1 p), ?_⟩
  intro v
  simp only [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    cocharacterQuotientEquivOfFppf_mk]

end Langlands.GroupScheme
