import Langlands.Representation.Geometric.OppositeRefinedFiltration
import Langlands.Representation.Parabolic.OppositeJacquetFiltrationGradedProof
import Langlands.Representation.Parabolic.RefinedOppositeJacquetTensor
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-! Actual refined opposite Jacquet descriptions of the transported grades. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear OppositeCuspidalJacquetFiltration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
  (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))

/-- Reversing the coarse block labels is continuous for the actual product
topologies induced by the supplied field topology. -/
theorem continuous_leviReverseEquiv :
    letI := T.topology
    Continuous (leviReverseEquiv (R := F.Carrier) B) := by
  let := T.topology
  exact continuous_pi (fun i => continuous_apply i.rev)

/-- The actual normalized opposite Jacquet module of a smooth representation
is smooth, by the actual reversed upper Jacquet equivalence. -/
theorem isSmooth_oppositeJacquet :
    letI := T.topology
    IsSmooth A.ρ →
      IsSmooth (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ := by
  let := T.topology
  intro hA
  exact isSmooth_of_surjective
    (oppositeJacquetReverseEquiv T B A).toIntertwiningMap
    (oppositeJacquetReverseEquiv T B A).surjective
    (isSmooth_comp (leviReverseEquiv B).toMonoidHom
      (continuous_leviReverseEquiv T B) (T.isSmooth_normalizedJacquet B.reverse hA))

variable (S : BlockRefinement B)

set_option maxHeartbeats 800000 in
/-- For smooth input, the grade of the transported composed filtration is
the actual normalized refined opposite Jacquet module of the pulled-back
original reversed upper grade, at the same index. -/
def composedOppositeFiltrationOfReverseGradeJacquetEquiv {l : ℕ}
    (s : ObjectRepFiltration (Rep.of (T.normalizedJacquet B.reverse A.ρ)) l)
    (i : Fin l) :
    letI := T.topology
    IsSmooth A.ρ →
      Representation.Equiv
        ((composedOppositeFiltrationOfReverse T B A S s).gradedRepresentation i).ρ
        (T.normalizedRefinedOppositeJacquet B S
          ((s.gradedRepresentation i).ρ.comp (leviReverseEquiv B).toMonoidHom)) := by
  letI := T.topology
  intro hA
  let g := Classical.choice
    ((Parabolic.normalizedOppositeJacquetFiltrationGraded p F T n B S).1
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A)
      (CuspidalJacquetMultiplicity.oppositeJacquet T B A).ρ
      (isSmooth_oppositeJacquet T B A hA) l
      (oppositeFiltrationOfReverse T B A s) i)
  exact (composedOppositeFiltrationOfReverseGradedEquiv T B A S s i).symm.trans
    (g.trans (RefinedOppositeJacquetTensor.normalizedRefinedOppositeJacquetCongr
      T B S (oppositeFiltrationOfReverseGradedEquiv T B A s i).symm))

set_option maxHeartbeats 800000 in
/-- A supplied actual identification of an original reversed upper grade
passes through block relabelling and the normalized refined opposite quotient.
The identified grade may have an independent carrier universe. -/
def composedOppositeFiltrationOfReverseGradeCongr {l : ℕ}
    (s : ObjectRepFiltration (Rep.of (T.normalizedJacquet B.reverse A.ρ)) l)
    (i : Fin l) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (B.reverse.Levi F.Carrier) W)
    (e : (s.gradedRepresentation i).ρ.Equiv ρ) :
    letI := T.topology
    IsSmooth A.ρ →
      Representation.Equiv
        ((composedOppositeFiltrationOfReverse T B A S s).gradedRepresentation i).ρ
        (T.normalizedRefinedOppositeJacquet B S
          (ρ.comp (leviReverseEquiv B).toMonoidHom)) := by
  letI := T.topology
  intro hA
  exact (composedOppositeFiltrationOfReverseGradeJacquetEquiv T B A S s i hA).trans
    (RefinedOppositeJacquetTensor.normalizedRefinedOppositeJacquetCongr T B S
      (FiniteTensorFiltration.compCongr e (leviReverseEquiv B).toMonoidHom))

end Langlands.Geometric
