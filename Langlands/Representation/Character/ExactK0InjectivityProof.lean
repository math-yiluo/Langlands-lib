import Langlands.Representation.Character.FiniteFamilyProof
import Langlands.Representation.Smooth.IrreducibleGrothendieckProof
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Injectivity of actual characters on the exact finite-length Grothendieck group -/

noncomputable section

universe uG uV

namespace Langlands.Character

open MeasureTheory VirtualRepresentation

/-- Actual characters distinguish every class of the exact finite-length quotient
under the generic admissibility premise of the published target. -/
theorem exactK0CharacterInjectivity :
    ExactK0CharacterInjectivityStatement.{uG, uV} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ hAdm χ hχ
  classical
  let F : SmoothRep.IrreducibleLattice.{0, uG, uV} ℂ G →ₗ[ℤ]
      HarmonicAnalysis.Distribution G :=
    χ.comp (SmoothRep.realizeIrreducibles ℂ G)
  let f : SmoothRep.IrreducibleIsoClass.{0, uG, uV} ℂ G →
      HarmonicAnalysis.Distribution G := fun c => F (generator c)
  have hlin : LinearIndependent ℂ f := by
    apply linearIndependent_iff_finset_linearIndependent.mpr
    intro s
    let e := (Fintype.equivFin s).symm
    choose A hI hC using fun i : Fin (Fintype.card s) =>
      SmoothRep.IrreducibleIsoClass.exists_eq (e i).val
    have hne : Pairwise (fun i j =>
        ¬ Nonempty ((A i).representation.Equiv (A j).representation)) := by
      intro i j hij h
      have h := (SmoothRep.irreducibleIsoClass_eq_iff_nonempty_equiv
        (hI i) (hI j)).mpr h
      rw [hC i, hC j] at h
      exact hij (e.injective (Subtype.ext h))
    have h := finiteFamilyLinearIndependence G μ (Fintype.card s) A
      (fun i => hAdm (A i) (SmoothRep.hasFiniteLength_of_isIrreducible (hI i)))
      hI hne
    have hf : (f ∘ (Subtype.val : s → SmoothRep.IrreducibleIsoClass ℂ G)) ∘ e =
        fun i => distribution μ (A i).representation
          (hAdm (A i) (SmoothRep.hasFiniteLength_of_isIrreducible (hI i))) := by
      funext i
      change χ (SmoothRep.realizeIrreducibles ℂ G (generator (e i).val)) = _
      rw [← hC i, SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass
        (A i) (hI i) (SmoothRep.hasFiniteLength_of_isIrreducible (hI i))]
      exact hχ _ _
    exact (linearIndependent_equiv' e hf).mp h
  have hF : F = Finsupp.linearCombination ℤ f := by
    apply Finsupp.lhom_ext
    intro c n
    calc
      F (Finsupp.single c n) = n • f c := by
        rw [show Finsupp.single c n = n • generator c by simp [generator], map_zsmul]
      _ = Finsupp.linearCombination ℤ f (Finsupp.single c n) := by
        simp
  have hinj : Function.Injective F := by
    rw [hF]
    exact hlin.restrict_scalars' ℤ
  intro x y hxy
  obtain ⟨a, rfl⟩ := (SmoothRep.irreducibleGrothendieckStatement.{0, uG, uV} ℂ G).2 x
  obtain ⟨b, rfl⟩ := (SmoothRep.irreducibleGrothendieckStatement.{0, uG, uV} ℂ G).2 y
  exact congrArg (SmoothRep.realizeIrreducibles ℂ G) (hinj hxy)

end Langlands.Character
