import Langlands.GroupScheme.Rational.LeviTorusCentralizerConjugacy
import Langlands.GroupScheme.Rational.SolvableMaximalTorusStatement
import Langlands.GroupScheme.Rational.ParabolicRadicalTorusCentralizerLeviStatement

/-! # Reduction to one suitable maximal torus of the supplied radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For each supplied geometric solvable radical, one maximal torus has an
actual rational Levi representing its whole-torus centralizer in the ambient
connected reductive group. -/
def ParabolicRadicalTorusInitialCentralizerLeviStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
        IsGeometricSolvableRadical r →
        ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (sR : S.toGrp ⟶ R),
          IsMaximalTorus sR ∧
          ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P),
            IsRationalLeviSubgroup l ∧
              (torusCentralizer (sR ≫ r ≫ j)).IsRepresentedBy (l ≫ j)

/-- Rational maximal-torus conjugacy and the one-torus existence assertion
suffice for the unchanged supplied-torus target. -/
def ParabolicRadicalTorusCentralizerLeviReductionStatement : Prop :=
  SolvableMaximalTorusConjugacyStatement.{u} →
  ParabolicRadicalTorusInitialCentralizerLeviStatement.{u} →
  ParabolicRadicalTorusCentralizerLeviStatement.{u}

/-- The supplied radical is smooth, connected and affine, so maximal-torus
conjugacy transports the initial actual ambient-centralizer Levi to every
supplied maximal torus. -/
theorem parabolicRadicalTorusCentralizerLevi_of_initial_torus :
    ParabolicRadicalTorusCentralizerLeviReductionStatement.{u} := by
  intro hconj hinitial k _ G hG P j hj R r hr S sR hsR
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : IsAffineHom P.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  let : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth R.X.hom := hr.1.smooth
  let : ConnectedSpace R.X.left := hr.1.connectedSpace
  obtain ⟨A, a, ha, hlevi⟩ := hinitial k G hG P j hj R r hr
  have hconjugate := hconj k R hr.1.isSolvableGroupScheme A S a sR ha hsR
  exact hconjugate.exists_rationalLevi_torusCentralizer r j hlevi

end Langlands.GroupScheme
