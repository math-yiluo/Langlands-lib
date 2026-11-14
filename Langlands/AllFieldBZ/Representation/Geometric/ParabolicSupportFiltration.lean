import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.Geometric.ParabolicSupportFiltration

/-!
# All-field port of `Langlands.Representation.Geometric.ParabolicSupportFiltration`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.ParabolicSupportFiltration` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped NNReal
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF uV

variable {F : Type uF} [CommRing F] {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)

variable [TopologicalSpace F] [IsTopologicalRing F]

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration
open Langlands.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- Support filtration of actual normalized parabolic induction restricted to P_C. -/
def parabolicInductionSupportFiltration {m : ℕ}
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m) :
    letI := T.topology
    RepFunctorFiltration
      (T.normalizedParabolicInductionFunctor B ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (C.parabolic F.Carrier).subtype) m := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact s.rawSmoothSupportFiltration.precomp (B.inducingFunctor (T.leviHalfCharacter B))

/-- Take actual images of the support subfunctor in the normalized Jacquet quotient. -/
def parabolicJacquetImageSubfunctor
    (S : letI := T.topology
      RepSubfunctor (T.normalizedParabolicInductionFunctor B ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (C.parabolic F.Carrier).subtype)) :
    letI := T.topology
    RepSubfunctor (jacquetInductionFunctor.{uF, uV} T B C) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact {
    obj A := C.normalizedJacquetImage (T.leviModulus C)
      ((T.normalizedParabolicInductionFunctor B).obj A).representation (S.obj A)
    map_mem := by
      intro A A' f q hq
      obtain ⟨v, hv, rfl⟩ := hq
      exact ⟨((T.normalizedParabolicInductionFunctor B).map f).hom.hom v,
        S.map_mem f hv, rfl⟩ }

set_option maxHeartbeats 800000 in
/-- The fixed support-image filtration of the exact functor in the geometric lemma. -/
def parabolicJacquetSupportFiltration {m : ℕ}
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m) :
    letI := T.topology
    RepFunctorFiltration (jacquetInductionFunctor.{uF, uV} T B C) m := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let t := parabolicInductionSupportFiltration.{uF, uV} T B C s
  exact {
    step k := parabolicJacquetImageSubfunctor T B C (t.step k)
    monotone A := by
      intro i j hij
      exact C.normalizedJacquetImage_mono _ _ (t.monotone A hij)
    zero A := by
      change C.normalizedJacquetImage _ _ ((t.step 0).obj A) = ⊥
      rw [t.zero A, C.normalizedJacquetImage_bot]
    top A := by
      change C.normalizedJacquetImage _ _ ((t.step (Fin.last m)).obj A) = ⊤
      rw [t.top A, C.normalizedJacquetImage_top] }

end Langlands.AllFieldBZ.Geometric
