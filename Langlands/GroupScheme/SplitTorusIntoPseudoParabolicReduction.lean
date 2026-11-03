import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicStatement
import Langlands.GroupScheme.SplitSolvableIntoPseudoParabolicStatement
import Langlands.GroupScheme.HomogeneousQuotientStatement
import Langlands.GroupScheme.SplitSolvableFixedPointStatement
import Langlands.GroupScheme.PseudoParabolicQuotientStatement
import Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingStatement
import Langlands.GroupScheme.PseudoParabolicStructureStatement
import Langlands.GroupScheme.SchemeActionQuotientIdentity
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.FixedCosetFactorization
import Langlands.GroupScheme.Torus.SplitSolvableProof

/-! # Assembly of rational containment in pseudo-parabolic subgroups

This module derives CGP Lemma C.2.2 from five explicit component
propositions, and then its split-torus specialization. The implications are
conditional: no component proposition is proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Quotient existence, structure of pseudo-parabolic subgroups,
pseudo-completeness of the quotient, the split-solvable fixed-point theorem
and rational lifting together imply rational containment of split subtori in
pseudo-parabolic subgroups. This is a conditional implication, with all five
prerequisite propositions explicit. -/
def SplitTorusIntoPseudoParabolicReductionStatement : Prop :=
  SmoothSubgroupQuotientExistenceStatement.{u} →
    PseudoParabolicSubgroupStructureStatement.{u} →
      PseudoParabolicQuotientPseudoCompleteStatement.{u} →
        SplitSolvablePseudoCompleteFixedPointStatement.{u} →
          PseudoParabolicQuotientRationalLiftingStatement.{u} →
            SplitTorusIntoPseudoParabolicStatement.{u}

/-- A rational point of a homogeneous quotient that is fixed by `H` on all
tests gives a fixed coset of any lift `g`, in the form used by
`factorOfFixedCoset`. -/
theorem fixedCoset_of_isFixed {S : Scheme.{u}} {G H : GroupScheme S}
    (A : SubgroupFunctor G) {Q : Over S} (q : G.X ⟶ Q)
    (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ A.carrier T)
    [QuasiCompact q.left] [Flat q.left] [Surjective q.left]
    (j : H ⟶ G) (g : Over.mk (𝟙 S) ⟶ G.X)
    (hx : ((Dynamic.flagQuotientSchemeAction G A q hfib).restrict j).IsFixed (g ≫ q))
    (T : Over S) (h : T ⟶ H.X) :
    ((h ≫ j.hom.hom) * G.constantPoint g T) ≫ q = G.constantPoint g T ≫ q := by
  have e := hx T (Over.homMk T.hom (by simp)) h
  rw [SchemeAction.restrict_act, ← Category.assoc] at e
  change (Dynamic.flagQuotientSchemeAction G A q hfib).act (h ≫ j.hom.hom)
      (G.constantPoint g T ≫ q) = G.constantPoint g T ≫ q at e
  rwa [Dynamic.flagQuotientSchemeAction_act_lift] at e

/-- CGP Lemma C.2.2 follows from quotient existence, smoothness of
pseudo-parabolic subgroups, pseudo-completeness of the quotient, the
split-solvable fixed-point theorem and rational lifting. The rational point
is the inverse of a lift of a fixed coset. -/
theorem splitSolvableIntoPseudoParabolic_of_components
    (hquot : SmoothSubgroupQuotientExistenceStatement.{u})
    (hstructure : PseudoParabolicSubgroupStructureStatement.{u})
    (hcomplete : PseudoParabolicQuotientPseudoCompleteStatement.{u})
    (hfixed : SplitSolvablePseudoCompleteFixedPointStatement.{u})
    (hlift : PseudoParabolicQuotientRationalLiftingStatement.{u}) :
    SplitSolvableIntoPseudoParabolicStatement.{u} := by
  intro k _ G P _ _ hconn i hi H j hj hH
  obtain ⟨hPsm, -, -⟩ := hstructure k G P i hi
  obtain ⟨Q, q, hQsep, hQlft, hQqc, hqsm, hqsurj, hqqc, hfib⟩ :=
    hquot k G P i hi.isClosedSubgroup hPsm
  have hQ : IsPseudoComplete Q :=
    hcomplete k G P i hi Q q hQsep hQlft hQqc hqsm hqsurj hqqc hfib
  have := hqsm
  have := hqsurj
  have := hqqc
  obtain ⟨x, hx⟩ := hfixed k H hH Q hQ ⟨quotientIdentityPoint q⟩
    ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range i) q hfib).restrict j)
  obtain ⟨g, rfl⟩ :=
    hlift k G hconn P i hi Q q hQsep hQlft hQqc hqsm hqsurj hqqc hfib x
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hcoset := fixedCoset_of_isFixed (SubgroupFunctor.range i) q hfib j g hx
  exact ⟨g⁻¹, factorOfFixedCoset j i q hfib g hcoset,
    factorOfFixedCoset_comp j i q hfib g hcoset⟩

/-- The split-torus target is the specialization of CGP Lemma C.2.2 to the
source of a split subtorus, which is split solvable. -/
theorem splitTorusIntoPseudoParabolic_of_splitSolvableIntoPseudoParabolic
    (h : SplitSolvableIntoPseudoParabolicStatement.{u}) :
    SplitTorusIntoPseudoParabolicStatement.{u} := by
  intro k _ G P _ _ _ i hi S j hj
  exact h k G P i hi S.toGrp j hj.2 hj.1.isSplitSolvableGroupScheme

/-- Conditional assembly of the split-torus target from the five component
propositions. -/
theorem splitTorusIntoPseudoParabolic_of_components
    (hquot : SmoothSubgroupQuotientExistenceStatement.{u})
    (hstructure : PseudoParabolicSubgroupStructureStatement.{u})
    (hcomplete : PseudoParabolicQuotientPseudoCompleteStatement.{u})
    (hfixed : SplitSolvablePseudoCompleteFixedPointStatement.{u})
    (hlift : PseudoParabolicQuotientRationalLiftingStatement.{u}) :
    SplitTorusIntoPseudoParabolicStatement.{u} :=
  splitTorusIntoPseudoParabolic_of_splitSolvableIntoPseudoParabolic
    (splitSolvableIntoPseudoParabolic_of_components hquot hstructure hcomplete
      hfixed hlift)

/-- The conditional reduction, as a proposition with its proof. -/
theorem splitTorusIntoPseudoParabolicReduction :
    SplitTorusIntoPseudoParabolicReductionStatement.{u} :=
  splitTorusIntoPseudoParabolic_of_components

end Langlands.GroupScheme
