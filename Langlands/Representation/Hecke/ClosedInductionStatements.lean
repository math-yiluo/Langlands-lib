import Langlands.Representation.Hecke.HomomorphismLeft
import Langlands.Representation.Induction.Definitions
import Langlands.Topology.Nonarchimedean.Subgroup

/-! # The explicit Hecke Hom model of smooth induction

Renard III.2.5 Remark, (III.2.5.1)–(III.2.5.5), printed pp.74–75 / PDF pp.80–81.
-/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Hecke.Homomorphism

open Langlands.Algebra HarmonicAnalysis

universe uG v

section Composites

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure]
  (H : Subgroup G) [LocallyCompactSpace H]
  (μH : Measure H) [μH.IsHaarMeasure]

/-- Existing smooth function induction followed by the published Hecke functor. -/
abbrev inducedHeckeFunctor :
    Langlands.SmoothRep.{0, uG, v} ℂ H ⥤
      NondegenerateModuleCat.{uG, max uG v} (HeckeAlgebra μG) :=
  Langlands.SmoothRep.toRep ⋙ Induction.smoothInductionFunctor H ⋙
    heckeNondegenerateModuleFunctor μG

/-- Existing Hecke functor followed by the constructed Chapter I Hom induction. -/
abbrev homInductionHeckeFunctor :
    Langlands.SmoothRep.{0, uG, v} ℂ H ⥤
      NondegenerateModuleCat.{uG, max uG v} (HeckeAlgebra μG) :=
  heckeNondegenerateModuleFunctor μH ⋙ I μG μH H.subtype continuous_subtype_val

/-- Evaluation of the original module map underlying a vector of Hom induction. -/
def homInductionEvaluation (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (q : ((homInductionHeckeFunctor μG H μH).obj W).obj)
    (T : HeckeAlgebra μG) : W := by
  letI := leftModule μG μH H.subtype continuous_subtype_val
  letI := heckeNonUnitalModule μH W.representation W.isSmooth
  exact (show NonUnitalModuleHom (HeckeAlgebra μH) (HeckeAlgebra μG) W from q.val) T

end Composites

/-- Renard (III.2.5.1)–(III.2.5.5): natural identification of smooth induction
with the actual `H(G)`-nondegenerate part of `Hom_{H(H)}(H(G),W)`.
Both maps are specified, with normalized compact-open local units in the
inverse formula and the restricted left-action identity used in (III.2.5.4). -/
def ClosedInductionHomStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [μG.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G)),
    letI : LocallyCompactSpace H := hH.locallyCompactSpace
    ∀ (μH : Measure H) [μH.IsHaarMeasure],
    letI := leftModule μG μH H.subtype continuous_subtype_val
    ∃ α : inducedHeckeFunctor.{uG, v} μG H ≅
        homInductionHeckeFunctor.{uG, v} μG H μH,
      (∀ (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
          (f : Induction.SmoothFunctions H W.representation) (T : HeckeAlgebra μG),
        homInductionEvaluation μG H μH W ((α.hom.app W).hom.toAddMonoidHom f) T =
          Induction.eval H W.representation
            (heckeAction μG (Induction.smoothInduced H W.representation)
              (Induction.smoothInduced_smooth H W.representation) T f) 1) ∧
      (∀ (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
          (q : ((homInductionHeckeFunctor μG H μH).obj W).obj),
        ∃ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
          ∀ T : HeckeAlgebra μG,
            homInductionEvaluation μG H μH W q
              (T * HeckeAlgebra.normalizedIndicator μG K hK) =
                homInductionEvaluation μG H μH W q T) ∧
      (∀ (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
          (q : ((homInductionHeckeFunctor μG H μH).obj W).obj)
          (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
        (∀ T : HeckeAlgebra μG,
          homInductionEvaluation μG H μH W q
            (T * HeckeAlgebra.normalizedIndicator μG K hK) =
              homInductionEvaluation μG H μH W q T) →
        ∀ g : G,
          Induction.eval H W.representation ((α.inv.app W).hom.toAddMonoidHom q) g =
            homInductionEvaluation μG H μH W q (show HeckeAlgebra μG from
              GroupAction.leftTests g (HeckeAlgebra.normalizedIndicator μG K hK))) ∧
      (∀ (U : OpenSubgroup H) (hU : IsCompact (U : Set H))
          (h : H) (T : HeckeAlgebra μG),
        HeckeAlgebra.normalizedIndicator μH U hU • T = T →
          (show HeckeAlgebra μH from
            GroupAction.leftTests h (HeckeAlgebra.normalizedIndicator μH U hU)) • T =
              leftRepresentation μG H.subtype h T)

end Langlands.Hecke.Homomorphism
