import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Automorphic.GroupSchemePositiveMatrixEmbedding
import Langlands.Automorphic.GroupSchemeUniformGrowthEvaluation
import Langlands.Global.AdelicEisensteinContinuationStatement
import Langlands.Global.AdelicEisensteinPointwiseContinuationStatement
import Langlands.Global.EisensteinConstantTerm.Height

/-! # Finite-family pointwise Eisenstein continuation from Fréchet continuation -/

noncomputable section

universe u

open AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- A function-valued Eisenstein continuation gives the pointwise
continuation for any finite family, with one common domain. -/
def EisensteinPointwiseFromFrechetStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{u} → EisensteinPointwiseContinuationStatement.{u}

theorem eisensteinPointwiseFromFrechet : EisensteinPointwiseFromFrechetStatement.{u} := by
  classical
  intro hCont F _ _ G P M U A _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth hcalc
    hmax hrho Idx _ phi hphi
  obtain ⟨m, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  obtain ⟨N', rho', hN', hrho', htransfer⟩ :=
    exists_positiveMatrixEmbedding_of_isClosedSubgroup rho hrho hsmooth hcalc
  have hCont' (i : Idx) := hCont F G P M U A p iU l a r hA hT hG hU K hK
    rho' hN' hrho' hsmooth hcalc (phi i) hmax ((htransfer _ _ _).mp (hphi i))
  choose E hAgreement hLocal using hCont'
  have hMer (i : Idx) :
      ∃ S : Set (Fin m → ℂ), ∀ g : AdelicGroupPoints F G,
        IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun t => E i (e t) g) S := by
    apply exists_isMeromorphicOn_of_local
    intro t
    obtain ⟨W, hW, R, L, _, f, D, hf, hE⟩ := hLocal i m e t
    exact hasLocalMeromorphicData_of_isMeromorphicOn hf
      (UniformGrowthFrechetSpace.evaluation F G rho' hsmooth hcalc hN' hrho' R L)
      (φ := fun g s => E i (e s) g)
      (fun s hs g => by
        rw [UniformGrowthFrechetSpace.evaluation_apply, (hE s hs).1]) hW
  choose S hS using hMer
  let T := ⋂ i : Idx, S i
  have ho : IsOpen T := isOpen_iInter_of_finite fun i => (hS i 1).1
  have hd : Dense T := dense_iInter_of_isOpen (fun i => (hS i 1).1) (fun i => (hS i 1).2.1)
  refine ⟨E, e '' T, ?_, ?_⟩
  · intro i g
    apply isMeromorphicInCoordinatesOn_of_coordinates e
    rw [Set.preimage_image_eq _ e.injective]
    exact (hS i g).congr_mono ho hd (Set.iInter_subset _ i) fun _ _ => rfl
  · choose R hR using hAgreement
    obtain ⟨B, hB⟩ := (Set.finite_range R).bddAbove
    exact ⟨B, fun lam hreg i => hR i lam
      (fun alpha hAlpha => lt_of_le_of_lt (hB (Set.mem_range_self i)) (hreg alpha hAlpha))⟩

end Langlands.Global
