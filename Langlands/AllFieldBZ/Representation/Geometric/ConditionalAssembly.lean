import Langlands.AllFieldBZ.Representation.Geometric.ParabolicSupportFiltration
import Langlands.Representation.Geometric.ConditionalAssembly

/-!
# All-field port of `Langlands.Representation.Geometric.ConditionalAssembly`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ConditionalAssembly` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricLemma_of_orderedCosets geometricLemma_of_supportGraded geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration
open Langlands.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- A specified support filtration and its natural graded identifications
assemble the existential geometric-lemma conclusion, conditionally. -/
theorem geometricLemma_of_supportGraded {m : ℕ}
    (e : Fin m ≃ MinimalRepresentatives B C)
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m)
    (S : MinimalRepresentatives B C → BlockRefinement B)
    (R : MinimalRepresentatives B C → BlockRefinement C)
    (hS : ∀ w, IsIntersectionRefinement (F := F.Carrier) B C w.val (S w))
    (hR : ∀ w, IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ (R w))
    (hgraded : letI := T.topology
      (parabolicJacquetSupportFiltration.{uF, uV} T B C s).HasGradedPieces
        (fun i => geometricPieceFunctor T B C (e i).val (S (e i)) (R (e i))
          (hS (e i)).2.1 (hR (e i)).2.1)) :
    GeometricLemmaTheorem.{uF, uV} T B C := by
  let := T.topology
  refine ⟨S, R, hS, hR, m, e, Equiv.refl _, ?_⟩
  refine ⟨parabolicJacquetSupportFiltration.{uF, uV} T B C s, ?_⟩
  intro i
  simpa only [Function.comp_apply, Equiv.refl_apply] using hgraded i

/-- Conditional final assembly: classify a supplied ordered cover, apply the
supplied natural graded comparison, and retain its actual support filtration.
This does not establish any of its geometric hypotheses. -/
theorem geometricLemma_of_orderedCosets {m : ℕ}
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m)
    (hBruhat : Function.Bijective (parabolicDoubleCoset F.Carrier B C))
    (S : MinimalRepresentatives B C → BlockRefinement B)
    (R : MinimalRepresentatives B C → BlockRefinement C)
    (hS : ∀ w, IsIntersectionRefinement (F := F.Carrier) B C w.val (S w))
    (hR : ∀ w, IsIntersectionRefinement (F := F.Carrier) C B w.val⁻¹ (R w))
    (hgraded : letI := T.topology
      ∀ (e : Fin m ≃ MinimalRepresentatives B C)
        (t : OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m),
        (∀ i, t.representative i = permutation n F.Carrier (e i).val) →
        (parabolicJacquetSupportFiltration.{uF, uV} T B C t).HasGradedPieces
          (fun i => geometricPieceFunctor T B C (e i).val (S (e i)) (R (e i))
            (hS (e i)).2.1 (hR (e i)).2.1)) :
    GeometricLemmaTheorem.{uF, uV} T B C := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨e, t, ht⟩ := minimalPermutationOrdering B C s hBruhat
  exact geometricLemma_of_supportGraded.{uF, uV} T B C e t S R hS hR (hgraded e t ht)

end Langlands.AllFieldBZ.Geometric
