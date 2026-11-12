import Langlands.Representation.Hecke.NormalQuotientModels
import Langlands.Representation.Hecke.HomomorphismSmooth
import Langlands.Representation.Induction.Definitions
import Langlands.Topology.Nonarchimedean.Subgroup

/-! # Normal quotients, Hecke tensor induction and adjunction

Renard III.2.10, (III.2.10.1)–(III.2.10.2), Proposition and Corollary,
printed pp.80–82 / PDF pp.86–88.
-/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open Langlands.Algebra HarmonicAnalysis

universe uP uG v

section Models

variable {P : Type uP} [Group P] [TopologicalSpace P] [T2Space P]
  [NonarchimedeanGroup P] [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P]
  (N : Subgroup P) [N.Normal] [IsClosed (N : Set P)]
  [MeasurableSpace (P ⧸ N)] [BorelSpace (P ⧸ N)]
  (μP : Measure P) [μP.IsHaarMeasure]
  (μM : Measure (P ⧸ N)) [μM.IsHaarMeasure]

/-- The actual `j_N`, followed by the integrated Hecke module functor. -/
abbrev coinvariantHeckeFunctor :=
  normalCoinvariantFunctor.{0, uP, max uP v} (R := ℂ) N ⋙ heckeNondegenerateModuleFunctor μM

/-- The actual Hecke tensor induction attached to the quotient projection. -/
abbrev quotientTensorHeckeFunctor :=
  heckeNondegenerateModuleFunctor.{uP, max uP v} μP ⋙
    Langlands.Hecke.Homomorphism.P μM μP (QuotientGroup.mk' N) QuotientGroup.continuous_mk

/-- An elementary tensor in the original balanced quotient for the quotient projection. -/
def quotientTensorTmul (W : SmoothRep.{0, uP, max uP v} ℂ P)
    (T : HeckeAlgebra μM) (w : W) :
    ((quotientTensorHeckeFunctor N μP μM).obj W).obj := by
  letI := rightModule μM μP (QuotientGroup.mk' N) QuotientGroup.continuous_mk
  letI := heckeNonUnitalModule μP W.representation W.isSmooth
  exact NonUnitalModuleTensor.tmul (HeckeAlgebra μP) (HeckeAlgebra μM) W T w

end Models

/-- III.2.10: pseudo-forgetting equals forgetting for a normal quotient;
`j_N` is naturally isomorphic to the actual Hecke tensor induction. The
right-action identity (III.2.10.1), forward map (III.2.10.2) and inverse
map on original elementary tensors are all specified conclusions. -/
def NormalQuotientHeckeStatement : Prop :=
  ∀ (P : Type uP) [Group P] [TopologicalSpace P] [T2Space P]
    [NonarchimedeanGroup P] [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P]
    (N : Subgroup P) [N.Normal] (hN : IsClosed (N : Set P)),
    letI : IsClosed (N : Set P) := hN
    ∀ [MeasurableSpace (P ⧸ N)] [BorelSpace (P ⧸ N)]
      (μP : Measure P) [μP.IsHaarMeasure]
      (μM : Measure (P ⧸ N)) [μM.IsHaarMeasure],
    let q := QuotientGroup.mk' N
    letI := rightModule μM μP q QuotientGroup.continuous_mk
    Nonempty (pseudoF.{uP, uP, v} μM μP q QuotientGroup.continuous_mk ≅
      F.{uP, uP, v} μM μP q QuotientGroup.continuous_mk) ∧
    (∀ (K : OpenSubgroup P) (hK : IsCompact (K : Set P)) (p : P) (T : HeckeAlgebra μM),
      let eP := HeckeAlgebra.normalizedIndicator μP K hK
      let eM := HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
        (isCompact_quotientOpenSubgroup N K hK)
      op (eP * (show HeckeAlgebra μP from GroupAction.leftTests p eP)) • T =
        T * (eM * (show HeckeAlgebra μM from GroupAction.leftTests (q p) eM))) ∧
    ∃ α : coinvariantHeckeFunctor.{uP, v} N μM ≅ quotientTensorHeckeFunctor N μP μM,
      (∀ (W : SmoothRep.{0, uP, max uP v} ℂ P) (w : W)
          (K : OpenSubgroup P) (hK : IsCompact (K : Set P)),
        w ∈ fixedVectors W.representation K.toSubgroup →
        (α.hom.app W).hom.toAddMonoidHom (Jacquet.mk W.representation N w) =
          quotientTensorTmul N μP μM W
            (HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
              (isCompact_quotientOpenSubgroup N K hK)) w) ∧
      (∀ (W : SmoothRep.{0, uP, max uP v} ℂ P) (T : HeckeAlgebra μM) (w : W),
        (α.inv.app W).hom.toAddMonoidHom (quotientTensorTmul N μP μM W T w) =
          heckeAction μM (normalQuotientAction N W.representation)
            (isSmooth_normalQuotientAction N W.representation W.isSmooth) T
            (Jacquet.mk W.representation N w))

/-- III.2.10 Proposition: actual normal-quotient coinvariants are left adjoint
to continuous pullback along the quotient projection. -/
def NormalQuotientAdjunctionStatement : Prop :=
  ∀ (P : Type uP) [Group P] [TopologicalSpace P] [T2Space P]
    [NonarchimedeanGroup P] [LocallyCompactSpace P]
    (N : Subgroup P) [N.Normal] (_hN : IsClosed (N : Set P)),
    Nonempty (normalCoinvariantFunctor.{0, uP, v} (R := ℂ) N ⊣
      restriction (QuotientGroup.mk' N) QuotientGroup.continuous_mk)

/-- III.2.10 Corollary: for a closed subgroup `P` of `G`, induction after
quotient pullback is right adjoint to restriction to `P` followed by `j_N`.
Both categories use the universe stable under function induction. -/
def NormalQuotientInductionAdjunctionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G]
    (P : Subgroup G) (_hP : IsClosed (P : Set G))
    (N : Subgroup P) [N.Normal] (_hN : IsClosed (N : Set P)),
    Nonempty ((restriction.{uG, uG, max uG v} P.subtype continuous_subtype_val ⋙
      normalCoinvariantFunctor (R := ℂ) N) ⊣
      (restriction (QuotientGroup.mk' N) QuotientGroup.continuous_mk ⋙
        SmoothRep.toRep ⋙ Induction.smoothInductionFunctor P))

/-- The complete III.2.10 comparison, formulas, Proposition and Corollary targets. -/
def NormalQuotientStatements : Prop :=
  NormalQuotientHeckeStatement.{uP, v} ∧ NormalQuotientAdjunctionStatement.{uP, v} ∧
    NormalQuotientInductionAdjunctionStatement.{uG, v}

end Langlands.Hecke.Homomorphism
