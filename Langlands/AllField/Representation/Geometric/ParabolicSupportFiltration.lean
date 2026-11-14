import Langlands.Representation.Geometric.ParabolicSupportFiltration
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
/-! Support images in the actual normalized parabolic Jacquet quotient. -/

noncomputable section
open CategoryTheory
open scoped NNReal

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV



end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration
open Langlands.AllField.Geometric

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B C : BlockShape n)

/-- Support filtration of actual normalized parabolic induction restricted to P_C. -/
def parabolicInductionSupportFiltration {m : ℕ}
    (s : letI := T.topology
      OrderedDoubleCosets (B.parabolic F) (C.parabolic F) m) :
    letI := T.topology
    RepFunctorFiltration
      (T.normalizedParabolicInductionFunctor B ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (C.parabolic F).subtype) m := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact s.rawSmoothSupportFiltration.precomp (B.inducingFunctor (T.leviHalfCharacter B))

/-- Take actual images of the support subfunctor in the normalized Jacquet quotient. -/
def parabolicJacquetImageSubfunctor
    (S : letI := T.topology
      RepSubfunctor (T.normalizedParabolicInductionFunctor B ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (C.parabolic F).subtype)) :
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
      OrderedDoubleCosets (B.parabolic F) (C.parabolic F) m) :
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

end Langlands.AllField.Geometric
