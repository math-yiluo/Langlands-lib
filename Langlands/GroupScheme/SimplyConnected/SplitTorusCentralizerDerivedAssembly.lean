import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedGeometricReduction
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonStatement
import Langlands.GroupScheme.SimplyConnected.LeviCorootLattice
import Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement
import Langlands.GroupScheme.SimplyConnected.SplitCriterionStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Derived.SemisimpleStatement
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity
import Langlands.GroupScheme.Rational.SplitCentralEmbedding

/-! # Conditional assembly for derived split-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The six structural statements retained by the centralizer-derived assembly. -/
def SplitTorusCentralizerDerivedInputsStatement : Prop :=
  DynamicCentralizerReductiveStatement.{u} ∧
    DerivedSubgroupSemisimpleStatement.{u} ∧
    SplitSimplyConnectedCorootSpanStatement.{u} ∧
    SplitCorootSpanSimplyConnectedStatement.{u} ∧
    SplitTorusCentralizerDerivedCorootComparisonStatement.{u} ∧
    IsSimplyConnectedAlgebraicClosureAscentStatement.{u}

/-- The geometric coroot comparison and the two coroot criteria prove the
algebraically closed case, assuming reductivity and derived semisimplicity. -/
theorem splitTorusCentralizerDerivedSimplyConnectedAlgClosed_of_inputs
    (hred : DynamicCentralizerReductiveStatement.{u})
    (hderived : DerivedSubgroupSemisimpleStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u})
    (hcomp : SplitTorusCentralizerDerivedCorootComparisonStatement.{u}) :
    SplitTorusCentralizerDerivedSimplyConnectedAlgClosedStatement.{u} := by
  intro k _ _ G hG A a ha M j hj D d hd
  have hGred := hG.isSemisimple.isConnectedReductive
  have := hGred.isAffineHom
  have := hGred.smooth
  let χ := CommGroupScheme.groupHom (centralizingCocharacter ha.1 a) ≫ a
  have hjχ : (Dynamic.centralizer χ).IsRepresentedBy j := by
    change (Dynamic.centralizer
      (CommGroupScheme.groupHom (centralizingCocharacter ha.1 a) ≫ a)).IsRepresentedBy j
    rwa [centralizingCocharacter_spec ha.1 a]
  have hM : IsConnectedReductive M :=
    hred k G hGred χ M j (ha.1.isClosedSubgroup_torusCentralizer a hj) hjχ
  have hD := hderived k M D d hM hd
  have := hD.isConnectedReductive.isAffineHom
  obtain ⟨T, S, i, t, φ, hT, hi, hS, ht, hφ, _hsquare,
    J, K, hJ, hK, P, Q, hP, hPred, hQ, _hQred, b, s, hs, hmap⟩ :=
    hcomp k G hGred A a ha M j hj D d hd hD
  let : Finite J := hJ
  let : Finite K := hK
  have hPfull := hnec k G hG T hT i hi J P hP hPred
  have : Module.Finite ℤ (characterLattice S) := hS.finite_characterLattice
  have : Finite (cocharacterLattice S ⧸ Q.corootSpan ℤ) :=
    Q.finite_quotient_rootSpan_iff_corootSpan.mp
      (hD.finite_quotient_rootSpan hS ht.2.1 hQ)
  have : IsClosedImmersion (CommGroupScheme.groupHom φ).hom.hom.left := hφ
  have hQfull := Langlands.LinearAlgebra.corootSpan_eq_top_of_map_eq_span_simple_coroots
    b hPfull s hs Q (RealTorusSpace.cocharacterMapInt φ)
    (RealTorusSpace.cocharacterMapInt_injective φ) hmap
  exact hsuff k D hD S hS t ht K Q hQ hQfull

/-- The six displayed structural statements suffice for the exact public
centralizer-derived theorem over every field in the arbitrary universe `u`. -/
theorem splitTorusCentralizerDerivedSimplyConnected_of_inputs
    (hred : DynamicCentralizerReductiveStatement.{u})
    (hderived : DerivedSubgroupSemisimpleStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u})
    (hcomp : SplitTorusCentralizerDerivedCorootComparisonStatement.{u})
    (hascent : IsSimplyConnectedAlgebraicClosureAscentStatement.{u}) :
    SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} :=
  splitTorusCentralizerDerivedSimplyConnected_of_algebraicClosure hascent
    (splitTorusCentralizerDerivedSimplyConnectedAlgClosed_of_inputs
      hred hderived hnec hsuff hcomp)

/-- The bundled structural hypotheses imply the exact public target. -/
theorem splitTorusCentralizerDerivedSimplyConnected_of_input_bundle
    (h : SplitTorusCentralizerDerivedInputsStatement.{u}) :
    SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} := by
  obtain ⟨hred, hderived, hnec, hsuff, hcomp, hascent⟩ := h
  exact splitTorusCentralizerDerivedSimplyConnected_of_inputs
    hred hderived hnec hsuff hcomp hascent

end Langlands.GroupScheme
