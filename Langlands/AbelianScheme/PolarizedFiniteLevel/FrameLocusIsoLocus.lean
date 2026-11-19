import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus
import Langlands.AlgebraicGeometry.Modules.IsoLocusPullbackFree
import Langlands.AlgebraicGeometry.Picard.LineBundleFiniteProduct

/-! # The projective frame locus as an intersection of stalk-isomorphism loci -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- A point lies in the supremum of the opens on which a family of morphisms
restricts to isomorphisms exactly when it has an open neighbourhood inside all
their stalk-isomorphism loci. -/
theorem mem_sSup_isIso_restrict_iff {S : Scheme.{u}} {ι : Type*} {M N : ι → S.Modules}
    (φ : ∀ k, M k ⟶ N k) (x : S) :
    x ∈ sSup {W : S.Opens | ∀ k, IsIso ((Scheme.Modules.pullback W.ι).map (φ k))} ↔
      ∃ W : S.Opens, x ∈ W ∧ ∀ k, ∀ y ∈ W, y ∈ isoLocus (φ k) := by
  rw [TopologicalSpace.Opens.mem_sSup]
  have key : ∀ W : S.Opens, (∀ k, IsIso ((Scheme.Modules.pullback W.ι).map (φ k))) ↔
      ∀ k, ∀ y ∈ W, y ∈ isoLocus (φ k) := by
    intro W
    refine forall_congr' fun k => ?_
    rw [isIso_iff_forall_mem_isoLocus]
    constructor
    · intro h y hy
      exact (mem_isoLocus_pullback_iff W.ι (φ k) ⟨y, hy⟩).mp (h ⟨y, hy⟩)
    · intro h w
      exact (mem_isoLocus_pullback_iff W.ι (φ k) w).mpr (h _ w.2)
  constructor
  · rintro ⟨W, hW, hx⟩
    exact ⟨W, hx, (key W).mp hW⟩
  · rintro ⟨W, hx, hW⟩
    exact ⟨W, (key W).mpr hW, hx⟩

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}

/-- The target of a frame evaluation, a finite product of pulled-back cubic line
bundles, has finite local bases. -/
theorem Datum.hasFiniteLocalBasis_frameTarget (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (k : Fin (m + 2)) :
    Langlands.Scheme.Modules.HasFiniteLocalBasis
      (∏ᶜ fun j : {j : Fin (m + 2) // j ≠ k} =>
        (Scheme.Modules.pullback (a.torsionPoint (ρ j))).obj a.cubicBundle.obj) :=
  hasFiniteLocalBasis_of_isLocallyFreeOfRank
    (isLocallyFreeOfRank_pi fun j : {j : Fin (m + 2) // j ≠ k} =>
      (LineBundle.pullback (a.torsionPoint (ρ j))).obj a.cubicBundle)

/-- When the cubic direct image has finite local bases, the frame locus is the
intersection of the stalk-isomorphism loci of the frame evaluations. -/
theorem Datum.coe_frameLocus (a : Datum P S g d n)
    (hV : Langlands.Scheme.Modules.HasFiniteLocalBasis a.rigidificationModule)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) :
    (a.frameLocus ρ : Set S) = ⋂ k, isoLocus (a.frameEvaluation ρ k) := by
  have hopen : ∀ k, IsOpen (isoLocus (a.frameEvaluation ρ k)) := fun k => by
    have := isFinitePresentation_of_hasFiniteLocalBasis _ hV
    have := isFinitePresentation_of_hasFiniteLocalBasis _ (a.hasFiniteLocalBasis_frameTarget ρ k)
    exact isOpen_isoLocus _
  ext x
  change x ∈ a.frameLocus ρ ↔ _
  rw [Datum.frameLocus, mem_sSup_isIso_restrict_iff, Set.mem_iInter]
  constructor
  · rintro ⟨W, hxW, h⟩ k
    exact h k x hxW
  · intro h
    exact ⟨⟨⋂ k, isoLocus (a.frameEvaluation ρ k), isOpen_iInter_of_finite hopen⟩,
      Set.mem_iInter.mpr h, fun k y hy => Set.mem_iInter.mp hy k⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
