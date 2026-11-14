import Langlands.AllFieldBZ.Group.GL.HeadTailBlocks
import Langlands.AllFieldBZ.Representation.Parabolic.RefinementCoordinatesNormalizationProof
import Langlands.AllFieldBZ.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.Representation.Parabolic.OrderedRefinementInduction

/-!
# All-field port of `Langlands.Representation.Parabolic.OrderedRefinementInduction`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.OrderedRefinementInduction` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedRefinementInductionTransitivityClause RefinementCoordinatesNormalizationTheorem normalizedRefinementInductionTransitivity orderedRefinementInductionEquiv orderedRefinementIteratedInduced refinementCoordinatesNormalization
open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) {n : ℕ} (B D : BlockShape n) (S : BlockRefinement D)
  (e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length)
  (hs : ∀ a, (S a.1).size a.2 = B.size (e a))
  (hc : ∀ i k x, D.index i ((S i).index k x) =
    B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual iterated action, with the original inducing representation
transported to the concrete refined Levi. -/
abbrev orderedRefinementIteratedInduced
    (σ : Representation ℂ (B.Levi F.Carrier) V) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.leviTopologicalGroup D
  T.normalizedParabolicInduced D
    (T.normalizedRefinedInduced D S
      (σ.comp (B.leviRefinementEquiv D S e hs F.Carrier).symm.toMonoidHom))

set_option maxHeartbeats 800000 in
include hc in
private theorem _root_.Langlands.Parabolic.exists_orderedRefinementInduction
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∃ E : Representation.Equiv
        (orderedRefinementIteratedInduced F T B D S e hs σ)
        (T.normalizedParabolicInduced B σ),
      (∀ f (g : GeneralLinear n F.Carrier),
        Induction.eval _ _ (E f) g =
          Induction.eval _ _ (Induction.eval _ _ f g) 1) ∧
      (∀ f (g : GeneralLinear n F.Carrier) (m : D.Levi F.Carrier),
        Induction.eval _ _ (Induction.eval _ _ (E.symm f) g) m =
          (T.leviHalfModulus D m : ℂ)⁻¹ •
            Induction.eval _ _ f (D.leviEmbedding F.Carrier m * g)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup D
  let σL := σ.comp (B.leviRefinementEquiv D S e hs F.Carrier).symm.toMonoidHom
  have hσL : IsSmooth σL :=
    isSmooth_comp _ (B.leviRefinementEquivContinuous D S e hs F.Carrier).symm.continuous hσ
  let A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier D S) :=
    SmoothRep.of σL hσL
  have hst := normalizedRefinementInductionTransitivity.{uF, uV} F T D S
  let stages := hst.choose
  have hstages := hst.choose_spec.1
  have hstages_inv := hst.choose_spec.2
  have hn := (refinementCoordinatesNormalization.{uF, uV} F T n B D S e hs hc).2.2 V σ
  let normalization := hn.choose
  have hnormalization := hn.choose_spec.1
  have hnormalization_inv := hn.choose_spec.2
  let stagesE : Representation.Equiv
      (orderedRefinementIteratedInduced F T B D S e hs σ)
      (T.normalizedComposedInduced D S σL) := by
    have E := SmoothRep.equivOfIso (stages.app A)
    dsimp only [CategoryTheory.Functor.comp_obj,
      LocalFieldPackage.TopologicalData.normalizedRefinedInductionFunctor,
      normalizedRefinedInductionFunctorOf,
      LocalFieldPackage.TopologicalData.normalizedParabolicInductionFunctor,
      BlockShape.normalizedInductionFunctorOf,
      LocalFieldPackage.TopologicalData.normalizedComposedInductionFunctor,
      orderedRefinementIteratedInduced,
      LocalFieldPackage.TopologicalData.normalizedRefinedInduced,
      LocalFieldPackage.TopologicalData.normalizedParabolicInduced,
      SmoothRep.representation, SmoothRep.of, Rep.of, A] at E ⊢
    exact E
  refine ⟨stagesE.trans normalization, ?_, ?_⟩
  · intro f g
    change Induction.eval _ _ (normalization (stagesE f)) g = _
    rw [hnormalization]
    exact hstages A f g
  · intro f g m
    change Induction.eval _ _
      (Induction.eval _ _ (SmoothRep.hom (stages.inv.app A) (normalization.symm f)) g) m = _
    exact (hstages_inv A (normalization.symm f) g m).trans
      (congrArg (fun v : V => (T.leviHalfModulus D m : ℂ)⁻¹ • v)
        (hnormalization_inv f (D.leviEmbedding F.Carrier m * g)))

/-- Ordered coordinates turn intrinsic induction in stages into an equivalence
with ordinary normalized induction. -/
def orderedRefinementInductionEquiv
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation.Equiv
      (orderedRefinementIteratedInduced F T B D S e hs σ)
      (T.normalizedParabolicInduced B σ) :=
  Classical.choose (exists_orderedRefinementInduction F T B D S e hs hc σ hσ)

end Langlands.AllFieldBZ.Parabolic
