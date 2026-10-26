import Langlands.Group.GL.HeadTailBlocks
import Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof
import Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! Ordinary normalized induction in stages under exact ordered coordinates. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
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
private theorem exists_orderedRefinementInduction
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
  have hn := (refinementCoordinatesNormalization.{uF, uV} p F T n B D S e hs hc).2.2 V σ
  let normalization := hn.choose
  have hnormalization := hn.choose_spec.1
  have hnormalization_inv := hn.choose_spec.2
  let stagesE : Representation.Equiv
      (orderedRefinementIteratedInduced F T B D S e hs σ)
      (T.normalizedComposedInduced D S σL) := by
    have E := SmoothRep.equivOfIso (stages.app A)
    dsimp only [CategoryTheory.Functor.comp_obj,
      PadicField.TopologicalData.normalizedRefinedInductionFunctor,
      normalizedRefinedInductionFunctorOf,
      PadicField.TopologicalData.normalizedParabolicInductionFunctor,
      BlockShape.normalizedInductionFunctorOf,
      PadicField.TopologicalData.normalizedComposedInductionFunctor,
      orderedRefinementIteratedInduced,
      PadicField.TopologicalData.normalizedRefinedInduced,
      PadicField.TopologicalData.normalizedParabolicInduced,
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

/-- Forward comparison evaluates the inner induced function at the identity. -/
theorem orderedRefinementInductionEquiv_eval
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ f (g : GeneralLinear n F.Carrier),
      Induction.eval _ _
          (orderedRefinementInductionEquiv F T B D S e hs hc σ hσ f) g =
        Induction.eval _ _ (Induction.eval _ _ f g) 1 :=
  (Classical.choose_spec (exists_orderedRefinementInduction F T B D S e hs hc σ hσ)).1

/-- The inverse retains the outer positive-half correction in its inner section. -/
theorem orderedRefinementInductionEquiv_symm_eval
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ f (g : GeneralLinear n F.Carrier) (m : D.Levi F.Carrier),
      Induction.eval _ _
          (Induction.eval _ _
            ((orderedRefinementInductionEquiv F T B D S e hs hc σ hσ).symm f) g) m =
        (T.leviHalfModulus D m : ℂ)⁻¹ •
          Induction.eval _ _ f (D.leviEmbedding F.Carrier m * g) :=
  (Classical.choose_spec (exists_orderedRefinementInduction F T B D S e hs hc σ hσ)).2

/-- The first/tail instance uses the published exact block coordinates. -/
abbrev headTailInductionEquiv {k : ℕ} (h : B.length = k + 2)
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσ : letI := T.topology; IsSmooth σ) :=
  orderedRefinementInductionEquiv F T B (B.headTailShape h)
    (B.headTailRefinement h) (B.headTailBlockEquiv h) (B.headTailBlock_size h)
    (B.headTail_index h) σ hσ

/-- The first/tail comparison has the same forward evaluation formula. -/
theorem headTailInductionEquiv_eval {k : ℕ} (h : B.length = k + 2)
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ f (g : GeneralLinear n F.Carrier),
      Induction.eval _ _ (headTailInductionEquiv F T B h σ hσ f) g =
        Induction.eval _ _ (Induction.eval _ _ f g) 1 :=
  orderedRefinementInductionEquiv_eval F T B (B.headTailShape h)
    (B.headTailRefinement h) (B.headTailBlockEquiv h) (B.headTailBlock_size h)
    (B.headTail_index h) σ hσ

/-- The first/tail inverse uses the actual two-block Levi and its positive half. -/
theorem headTailInductionEquiv_symm_eval {k : ℕ} (h : B.length = k + 2)
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ f (g : GeneralLinear n F.Carrier) (m : (B.headTailShape h).Levi F.Carrier),
      Induction.eval _ _
          (Induction.eval _ _ ((headTailInductionEquiv F T B h σ hσ).symm f) g) m =
        (T.leviHalfModulus (B.headTailShape h) m : ℂ)⁻¹ •
          Induction.eval _ _ f ((B.headTailShape h).leviEmbedding F.Carrier m * g) :=
  orderedRefinementInductionEquiv_symm_eval F T B (B.headTailShape h)
    (B.headTailRefinement h) (B.headTailBlockEquiv h) (B.headTailBlock_size h)
    (B.headTail_index h) σ hσ

end Langlands.Parabolic
