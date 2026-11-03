import Langlands.GroupScheme.Rational.ParabolicTorusStatement
import Langlands.GroupScheme.Rational.MaximalSplitTorusStatement
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement

/-! # Conjugacy of ambient maximal split tori inside a parabolic subgroup

The three structural statements used here remain explicit hypotheses. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The three structural propositions used by the conditional parabolic conjugacy
reduction. This bundle is an input, not an assertion that these propositions hold. -/
def ParabolicSplitTorusConjugacyInputs : Prop :=
  SmoothMaximalSplitTorusConjugacyStatement.{u} ∧
    ParabolicDynamicStatement.{u} ∧ DynamicConnectedStatement.{u}

variable {k : Type u} [Field k]
  {G H P : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Conditional on conjugacy of maximal split tori of smooth connected affine groups,
two ambient maximal split tori factoring through such a closed subgroup are conjugate
by a rational point of that subgroup, with an equation into the subgroup itself. -/
theorem exists_innerIso_comp_eq_of_smooth_connected_closed_factorizations
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i')
    (f : T.toGrp ⟶ H) (f' : T'.toGrp ⟶ H)
    (hf : f ≫ j = i) (hf' : f' ≫ j = i') :
    ∃ (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (e : T.toGrp ≅ T'.toGrp),
      f ≫ (H.innerIso p).hom = e.hom ≫ f' := by
  exact hconj k H T T' f f'
    (IsMaximalSplitTorus.of_comp hj (hf.symm ▸ hi))
    (IsMaximalSplitTorus.of_comp hj (hf'.symm ▸ hi'))

/-- Parabolic subgroups of a connected reductive group are connected, conditional
on the parabolic-dynamic and dynamic-connectedness statements. -/
theorem IsParabolicSubgroup.connectedSpace_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hconn : DynamicConnectedStatement.{u})
    (hG : IsConnectedReductive G) {j : P ⟶ G} (hj : IsParabolicSubgroup j) :
    ConnectedSpace P.X.left := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  obtain ⟨χ, hχ⟩ := (hPD k G hG P j hj.isClosedSubgroup).mp hj
  exact ((hconn k G χ P j).2 hG.connectedSpace).1 ⟨Over.mono_of_mono_left _, hχ⟩

/-- The three structural statements imply conjugacy inside every rational parabolic
containing two ambient maximal split tori; minimality is unnecessary. -/
theorem exists_parabolic_innerIso_comp_eq_of_structuralStatements
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hPD : ParabolicDynamicStatement.{u}) (hconn : DynamicConnectedStatement.{u})
    (hG : IsConnectedReductive G) (j : P ⟶ G) (hj : IsParabolicSubgroup j)
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i')
    (f : T.toGrp ⟶ P) (f' : T'.toGrp ⟶ P)
    (hf : f ≫ j = i) (hf' : f' ≫ j = i') :
    ∃ (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) (e : T.toGrp ≅ T'.toGrp),
      f ≫ (P.innerIso p).hom = e.hom ≫ f' := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth P.X.hom := hj.smooth
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : IsAffineHom P.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : ConnectedSpace P.X.left :=
    hj.connectedSpace_of_parabolicDynamic hPD hconn hG
  exact exists_innerIso_comp_eq_of_smooth_connected_closed_factorizations
    hconj j hj.isClosedSubgroup hi hi' f f' hf hf'

/-- Conditional reduction to the unchanged published minimal-parabolic proposition. -/
theorem minimalParabolicSplitTorusConjugacy_of_structuralStatements
    (h : ParabolicSplitTorusConjugacyInputs.{u}) :
    MinimalParabolicSplitTorusConjugacyStatement.{u} := by
  obtain ⟨hconj, hPD, hconn⟩ := h
  intro k _ G hG P j hj T T' i i' hi hi' f f' hf hf'
  exact exists_parabolic_innerIso_comp_eq_of_structuralStatements
    hconj hPD hconn hG j hj.isParabolicSubgroup hi hi' f f' hf hf'

end Langlands.GroupScheme
