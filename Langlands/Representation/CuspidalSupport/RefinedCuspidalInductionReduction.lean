import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionRankZero
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
import Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
import Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.Padic
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof

/-! Reduction of refined cuspidal induction to standard cuspidal induction. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric CategoryTheory

universe uF uV

section Evaluation

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (B : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Evaluation at the identity of normalized parabolic induction is surjective
for smooth inducing data. -/
theorem normalizedParabolicInduced_eval_surjective
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth σ →
      Function.Surjective (fun f : Induction.SmoothFunctions (B.parabolic F.Carrier)
          (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) =>
        Induction.eval (B.parabolic F.Carrier)
          (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) f 1) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  intro hσ
  have hσP : IsSmooth (twist (T.parabolicHalfModulus B)
      (σ.comp (B.leviProjection F.Carrier))) :=
    (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus B)).mpr
      (isSmooth_comp _ (T.blockLeviProjection B).continuous hσ)
  intro v
  exact ⟨(Induction.compactLocalSection _ _ hσP 1 v Set.univ isOpen_univ
      (Set.mem_univ _)).val,
    Induction.compactLocalSection_apply _ _ hσP 1 v Set.univ isOpen_univ (Set.mem_univ _)⟩

/-- For smooth inducing data, evaluation at the identity descends to a
surjection from the normalized Jacquet module of the normalized parabolic
induction onto the inducing representation. -/
theorem jacquetEvaluation_id_surjective (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth σ →
      Function.Surjective (jacquetEvaluation T B
        (Representation.IntertwiningMap.id (T.normalizedParabolicInduced B σ))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hσ w
  obtain ⟨f, hf⟩ := normalizedParabolicInduced_eval_surjective T B σ hσ w
  exact ⟨B.jacquetMk (T.normalizedParabolicInduced B σ) f, hf⟩

end Evaluation

section Stages

/-- Normalized parabolic induction of the refined induction of irreducible
cuspidal data has finite length, given finite length of standard cuspidal
induction in the same rank. -/
theorem normalizedParabolicInduced_refined_finiteLength
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (hlen : CuspidalInductionLengthTheorem.{uF, uV} F T n)
    (B : BlockShape n) (S : BlockRefinement B)
    (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible ω.ρ → IsLeviCuspidal (B.flatten S) ω.ρ →
      letI := T.generalLinearTopologicalGroup n
      letI := T.leviTopologicalGroup B
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        (T.normalizedParabolicInduced B (T.normalizedRefinedInduced B S
          (ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom))).asModule := by
  let := T.topology
  intro hirr hcusp
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let e := flattenedLeviEquiv F.Carrier B S
  let σ := ω.ρ.comp e.symm.toMonoidHom
  have hσ : IsSmooth σ :=
    ((Parabolic.isAdmissible_flattenedLeviTransport_iff F T B S ω.ρ).mpr hcusp.1).1
  let := T.valuativeRel
  let := T.localField
  have hst := Parabolic.normalizedRefinementInductionTransitivity.{uF, uV} F T B S
  let E := hst.choose
  let A : SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) := SmoothRep.of σ hσ
  let E₁ : Representation.Equiv
      (T.normalizedParabolicInduced B (T.normalizedRefinedInduced B S σ))
      (T.normalizedComposedInduced B S σ) := by
    have E' := SmoothRep.equivOfIso (E.app A)
    dsimp only [CategoryTheory.Functor.comp_obj,
      PadicField.TopologicalData.normalizedRefinedInductionFunctor,
      normalizedRefinedInductionFunctorOf,
      PadicField.TopologicalData.normalizedParabolicInductionFunctor,
      BlockShape.normalizedInductionFunctorOf,
      PadicField.TopologicalData.normalizedComposedInductionFunctor,
      PadicField.TopologicalData.normalizedRefinedInduced,
      PadicField.TopologicalData.normalizedParabolicInduced,
      SmoothRep.representation, SmoothRep.of, Rep.of, A] at E' ⊢
    exact E'
  have hcf := Parabolic.composedFlattenedInduction.{uF, uV} p F T n B S _ σ
  let E₂ := hcf.choose
  have hcomp : σ.comp e.toMonoidHom = ω.ρ := by
    apply MonoidHom.ext
    intro m
    simp [σ]
  have hflat := (hlen (B.flatten S) (SmoothRep.of ω.ρ hcusp.1.1) hirr hcusp).1
  have hflat' : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (T.normalizedParabolicInduced (B.flatten S) (σ.comp e.toMonoidHom)).asModule := by
    rw [hcomp]
    exact hflat
  exact FiniteLengthAssembly.finiteLength_of_injective
    (E₂.toIntertwiningMap.comp E₁.toIntertwiningMap) (E₂.injective.comp E₁.injective) hflat'

end Stages

/-- The target conclusion for one rank, given finite length of standard
cuspidal induction in that rank. -/
theorem refinedCuspidalInductionFiniteLength_of_cuspidalInductionLength
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (hlen : CuspidalInductionLengthTheorem.{uF, uV} F T n)
    (B : BlockShape n) (S : BlockRefinement B)
    (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible ω.ρ →
    IsLeviCuspidal (B.flatten S) ω.ρ →
      letI := T.leviTopologicalGroup B
      let σ := ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom
      let I : Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
        Rep.of (T.normalizedRefinedInduced B S σ)
      IsAdmissible I.ρ ∧
        IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) I.ρ.asModule ∧
        ∃ m : ℕ, HasCompositionSeriesLength I m := by
  let := T.topology
  intro hirr hcusp
  let := T.leviTopologicalGroup B
  let := T.generalLinearTopologicalGroup n
  have hI := Parabolic.refinedCuspidalInduction_isAdmissible F T B S ω hcusp
  let σ := ω.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom
  let ρI := T.normalizedRefinedInduced B S σ
  have hJlen := normalizedParabolicInduced_refined_finiteLength F T hlen B S ω hirr hcusp
  have hJadm : IsAdmissible (T.normalizedParabolicInduced B ρI) :=
    Parabolic.normalizedInductionAdmissibility F T B _ ρI hI
  have hJfg : Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (T.normalizedParabolicInduced B ρI).asModule := by
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hJlen).1
    infer_instance
  have hJac := Parabolic.normalizedJacquetFiniteLength T B _ hJadm hJfg
  have hfin : IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) ρI.asModule :=
    FiniteLengthAssembly.finiteLength_of_surjective _
      (jacquetEvaluation_id_surjective T B ρI (T.isSmooth_normalizedRefinedInduced B S σ)) hJac
  exact ⟨hI, hfin, exists_hasCompositionSeriesLength_of_isFiniteLength _ hfin⟩

/-- The target proposition holds as soon as standard cuspidal induction has
finite length in every positive rank. -/
def RefinedCuspidalInductionReductionClause : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
      0 < n → CuspidalInductionLengthTheorem.{uF, uV} F T n) →
    RefinedCuspidalInductionFiniteLengthStatement.{uF, uV}

theorem refinedCuspidalInductionReductionClause_holds :
    RefinedCuspidalInductionReductionClause.{uF, uV} := by
  intro hlen p _ F T n B S ω hirr hcusp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact refinedCuspidalInductionFiniteLength_rankZero F T B S ω hcusp
  · exact refinedCuspidalInductionFiniteLength_of_cuspidalInductionLength F T
      (hlen p F T n hn) B S ω hirr hcusp

end Langlands.CuspidalSupport
