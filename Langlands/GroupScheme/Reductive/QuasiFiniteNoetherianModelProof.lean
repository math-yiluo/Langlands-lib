import Langlands.GroupScheme.Reductive.QuasiFiniteNoetherianModelReduction
import Langlands.GroupScheme.Descent.FiniteCoefficientHomGeneral
import Langlands.GroupScheme.Reductive.DirectLimitAssembly

/-! # Noetherian models of reductive quasi-finite flat surjections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open Descent.FiniteCoefficient
open Langlands.AlgebraicGeometry.NoetherianApproximation
open P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC

/-- Every supplied reductive quasi-finite flat surjection has the required
noetherian subring model, uniformly in the universe. -/
theorem reductiveQuasiFiniteNoetherianModel :
    ReductiveQuasiFiniteNoetherianModelStatement.{u} := by
  intro A _ G H hG hH f hq hf hs
  let : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let := hG.isAffineHom
  let := hG.smooth
  let := hH.isAffineHom
  let := hH.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨D, -⟩ := exists_quasiFiniteSmoothAffineHomModel
    (R := ULift.{u} ℤ) homGeneral f ⟨⟨hq, hf⟩, hs⟩ ∅
  let S : FGIndex (ULift.{u} ℤ) A →o Subalgebra (ULift.{u} ℤ) A :=
    { toFun := fun i => i.1
      monotone' := fun _ _ h => h }
  let i₀ : FGIndex (ULift.{u} ℤ) A := ⟨D.coefficients, D.finite⟩
  have hcover : ∀ a : A, ∃ i : FGIndex (ULift.{u} ℤ) A, a ∈ S i := by
    intro a
    classical
    refine ⟨⟨Algebra.adjoin (ULift.{u} ℤ) ↑({a} : Finset A),
      Subalgebra.fg_adjoin_finset _⟩, ?_⟩
    exact Algebra.subset_adjoin (by simp)
  obtain ⟨hc⟩ := nonempty_isColimit_ringCocone S hcover
  let := D.sourceSmooth
  let := D.sourceAffine
  let := D.targetSmooth
  let := D.targetAffine
  have hG' : IsReductive
      ((baseChange (Spec.map ((ringCocone S).ι.app i₀))).obj D.source) :=
    IsReductive.of_iso D.sourceIso.symm hG
  have hH' : IsReductive
      ((baseChange (Spec.map ((ringCocone S).ι.app i₀))).obj D.target) :=
    IsReductive.of_iso D.targetIso.symm hH
  obtain ⟨i₁, hi₁, hredG⟩ :=
    (isReductive_baseChange_iff_eventually
      (ringDiagram S) (ringCocone S) hc i₀ D.source).mp hG'
  obtain ⟨i₂, hi₂, hredH⟩ :=
    (isReductive_baseChange_iff_eventually
      (ringDiagram S) (ringCocone S) hc i₀ D.target).mp hH'
  obtain ⟨i₃, h₁₃, h₂₃⟩ := exists_ge_ge i₁ i₂
  have h₀₃ : i₀ ≤ i₃ := hi₁.trans h₁₃
  let E := D.enlargeTo i₃.1 i₃.2 h₀₃
  exact ⟨E.toNoetherian (hredG i₃ h₀₃ h₁₃) (hredH i₃ h₀₃ h₂₃)⟩

end Langlands.GroupScheme
