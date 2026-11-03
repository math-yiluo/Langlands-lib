import Langlands.GroupScheme.Rational.ParabolicTorusStatement
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SplitRankReduction

/-! # Maximal split-torus conjugacy through a common torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Two rational parabolics contain an ambient maximal split torus with actual
factorizations through both subgroup schemes. -/
def ParabolicIntersectionSplitTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P P' : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G) (j' : P' ⟶ G),
      IsParabolicSubgroup j → IsParabolicSubgroup j' →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsMaximalSplitTorus i ∧
        ∃ (f : T.toGrp ⟶ P) (f' : T.toGrp ⟶ P'), f ≫ j = i ∧ f' ≫ j' = i

/-- The stronger centralizer-containment interface supplies the actual common torus. -/
theorem parabolicIntersectionSplitTorusStatement_of_centralizer
    (hCentralizer : ParabolicIntersectionCentralizerStatement.{u}) :
    ParabolicIntersectionSplitTorusStatement.{u} := by
  intro k _ G hG P P' j j' hj hj'
  obtain ⟨T, i, hi, hP, hP'⟩ := hCentralizer k G hG P P' j j' hj hj'
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have : IsClosedImmersion j'.hom.hom.left := hj'.isClosedSubgroup
  have hrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hrep' : (SubgroupFunctor.range j').IsRepresentedBy j' :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hle := (range_le_torusCentralizer i).trans hP
  have hle' := (range_le_torusCentralizer i).trans hP'
  exact ⟨T, i, hi, hrep.factorHom i hle, hrep'.factorHom i hle',
    hrep.factorHom_comp i hle, hrep'.factorHom_comp i hle'⟩

/-- Conjugacy inside each containing minimal parabolic gives ambient conjugacy
through their common maximal split torus. -/
theorem maximalSplitTorus_subgroupConjugate_of_parabolicIntersection
    (hCommon : ParabolicIntersectionSplitTorusStatement.{u})
    (hInside : MinimalParabolicSplitTorusConjugacyStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (hContains : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
        ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
          IsMinimalParabolicSubgroup j ∧ ∃ f : T.toGrp ⟶ P, f ≫ j = i)
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (i' : T'.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i') :
    SubgroupConjugate i i' := by
  obtain ⟨P, j, hj, f, hf⟩ := hContains T i hi
  obtain ⟨P', j', hj', f', hf'⟩ := hContains T' i' hi'
  obtain ⟨M, m, hm, g, g', hg, hg'⟩ :=
    hCommon k G hG P P' j j' hj.1 hj'.1
  have hFirst : SubgroupConjugate i m := by
    have h : SubgroupConjugate f g := hInside k G hG P j hj T M i m hi hm f g hf hg
    simpa only [hf, hg] using h.postcomp j
  have hSecond : SubgroupConjugate i' m := by
    have h : SubgroupConjugate f' g' :=
      hInside k G hG P' j' hj' T' M i' m hi' hm f' g' hf' hg'
    simpa only [hf', hg'] using h.postcomp j'
  exact hFirst.trans hSecond.symm

/-- The common-torus route and explicit maximal extension give both clauses of
the unchanged ambient statement. All geometric inputs remain premises. -/
theorem maximalSplitTorusConjugacyStatement_of_parabolicIntersection_extension
    (hCommon : ParabolicIntersectionSplitTorusStatement.{u})
    (hInside : MinimalParabolicSplitTorusConjugacyStatement.{u})
    (hContains : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsMaximalSplitTorus i →
          ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
            IsMinimalParabolicSubgroup j ∧ ∃ f : T.toGrp ⟶ P, f ≫ j = i)
    (hExtension : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G →
      ∀ (J : Type u) [Finite J] (j : splitTorus (Spec (CommRingCat.of k)) J ⟶ G),
        IsClosedSubgroup j →
          ∃ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G),
            IsMaximalSplitTorus i' ∧
              ∃ f : splitTorus (Spec (CommRingCat.of k)) J ⟶ T'.toGrp, f ≫ i' = j) :
    MaximalSplitTorusConjugacyStatement.{u} := by
  apply maximalSplitTorusConjugacyStatement_of_extension_conjugacy hExtension
  intro k _ G hG
  exact maximalSplitTorus_subgroupConjugate_of_parabolicIntersection
    hCommon hInside hG (hContains k G hG)

end Langlands.GroupScheme
