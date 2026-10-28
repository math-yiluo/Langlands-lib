import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetUnitStatement
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Parabolic.RefinedInductionAdmissibility
import Langlands.Representation.Parabolic.RefinedInductionNonvanishingProof
import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionReduction

/-! Irreducible opposite-Jacquet unit embeddings from second adjointness. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

private theorem embedding_of_endomorphism_equiv
    {G H V W U : Type*} [Monoid G] [Monoid H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U]
    (σ : Representation ℂ G V) (τ : Representation ℂ G U)
    (ρ : Representation ℂ H W) [σ.IsIrreducible] [Nontrivial W]
    (E : (ρ.IntertwiningMap ρ) ≃ₗ[ℂ] (σ.IntertwiningMap τ)) :
    ∃ j : σ.IntertwiningMap τ, Function.Injective j := by
  have hid : Representation.IntertwiningMap.id ρ ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    exact hv (by simpa using congrArg (fun f : ρ.IntertwiningMap ρ => f v) h)
  have hj : E (Representation.IntertwiningMap.id ρ) ≠ 0 :=
    fun h => hid (E.map_eq_zero_iff.mp h)
  exact ⟨_, (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right hj⟩

/-- Every irreducible admissible inducing representation embeds into the
opposite Jacquet module of its actual normalized induction. -/
theorem irreducibleOppositeJacquetUnit :
    IrreducibleOppositeJacquetUnitStatement.{uF, uV} := by
  constructor
  · intro p _ F T
    let := T.topology
    intro n hn B σ hσi hσa
    let := T.generalLinearTopologicalGroup n
    let := hσi
    let : Nontrivial σ := IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (B.Levi F.Carrier)) σ.ρ.asModule
    let I : Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier) :=
      Rep.of (T.normalizedParabolicInduced B σ.ρ)
    let : Nontrivial I :=
      (CuspidalSupport.normalizedParabolicInduced_eval_surjective T B σ.ρ hσa.1).nontrivial
    have hIa : IsAdmissible I.ρ :=
      normalizedInductionAdmissibility F T B σ σ.ρ hσa
    obtain ⟨E, _⟩ :=
      (normalizedSecondAdjointness.{uF, uV, max uF uV}).1 p F T n hn B
    exact embedding_of_endomorphism_equiv σ.ρ _ I.ρ (E σ I hσa hIa)
  · intro p _ F T
    let := T.topology
    intro n hn B S σ hσi hσa
    let := T.leviTopologicalGroup B
    let := hσi
    let : Nontrivial σ := IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (refinedLevi F.Carrier B S)) σ.ρ.asModule
    let I : Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
      Rep.of (T.normalizedRefinedInduced B S σ.ρ)
    let : Nontrivial I :=
      ((normalizedRefinedInductionNonvanishing.{uF, uV}
        p F T n B S σ σ.ρ hσa.1).2 inferInstance)
    have hIa : IsAdmissible I.ρ :=
      normalizedRefinedInductionAdmissibility F T B S σ.ρ hσa
    obtain ⟨E, _⟩ :=
      (normalizedSecondAdjointness.{uF, uV, max uF uV}).2 p F T n hn B S
    exact embedding_of_endomorphism_equiv σ.ρ _ I.ρ (E σ I hσa hIa)

end Langlands.Parabolic
