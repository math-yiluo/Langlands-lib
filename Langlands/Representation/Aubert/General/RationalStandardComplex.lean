import Langlands.Representation.Aubert.General.RationalAlternatingOperator
import Langlands.Representation.Aubert.General.RationalWeylRootAction
import Langlands.Representation.Aubert.General.StandardComplex
import Langlands.GroupScheme.Rational.StandardParabolicOrderStatement
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsStatement

/-! # The normalized Aubert complex on the actual rational-point family -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The named all-test order statement gives order on the actual point groups. -/
theorem standardParabolic_monotone
    (hOrder : StandardParabolicOrderStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) : Monotone (parabolic i ν) := by
  intro I J hIJ
  exact ((hOrder k G hG T i hi ν hν).1
    (rootSet i ν I) (rootSet i ν J)
    (rootSet_subset i ν I) (rootSet_subset i ν J)).1.mp
      ((rootSet_subset_iff i ν I J).2 hIJ) (Over.mk (𝟙 _))

/-- The same order statement reverses the actual unipotent point groups. -/
theorem standardUnipotent_antitone
    (hOrder : StandardParabolicOrderStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) : Antitone (unipotent i ν) := by
  intro I J hIJ
  exact (((hOrder k G hG T i hi ν hν).1
    (rootSet i ν I) (rootSet i ν J)
    (rootSet_subset i ν I) (rootSet_subset i ν J)).2
      ((rootSet_subset_iff i ν I J).2 hIJ)).2 (Over.mk (𝟙 _))

/-- Evaluation of the named full-root endpoint at the identity test object. -/
theorem standardParabolic_univ [Fintype (SimpleRoot i ν)]
    (hEndpoints : StandardParabolicEndpointsStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) : parabolic i ν Finset.univ = ⊤ := by
  change (standardParabolic i ν (rootSet i ν Finset.univ)).carrier _ = _
  rw [rootSet_univ, (hEndpoints k G hG T i hi ν hν).2.2.1]
  rfl

/-- The actual full-root radical is trivial under the named endpoint statement. -/
theorem standardUnipotent_univ [Fintype (SimpleRoot i ν)]
    (hEndpoints : StandardParabolicEndpointsStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) : unipotent i ν Finset.univ = ⊥ := by
  change (standardUnipotent i ν (rootSet i ν Finset.univ)).carrier _ = _
  rw [rootSet_univ, (hEndpoints k G hG T i hi ν hν).2.2.2.2]
  rfl

/-- Association means the actual normalizer representative carries precisely
the indicated simple-root subset to the other one. Levi conjugation is checked
separately by the support-category predicate. -/
def rootAssociation [Mono i.hom.hom.left]
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (I J : Finset (SimpleRoot i ν)) (n : RationalPoint k G.X) : Prop :=
  ∃ hn : n ∈ Group.RelativeWeyl.normalizer (torusPoints i),
    weylCharacterAction i hN hZ (QuotientGroup.mk ⟨n, hn⟩) '' rootSet i ν I =
      rootSet i ν J

section Complex

variable [TopologicalSpace k]

local instance rationalStandardComplexPointTopology : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  [Fintype (SimpleRoot i ν)] [LinearOrder (SimpleRoot i ν)]
  (hStandard : StandardCocharacterStatement.{u})
  (hOrder : StandardParabolicOrderStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))

/-- The degree object consists of actual normalized induction--Jacquet terms. -/
abbrev rationalDegreeObject
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ) :=
  StandardComplex.degreeObject.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU E q

/-- Canonical quotient transitions with the chosen exterior orientation. -/
abbrev rationalDifferential
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ) :=
  StandardComplex.differential.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (standardUnipotent_antitone i ν hOrder hG hi hν) E q

/-- The actual incoming-image submodule. -/
abbrev rationalBoundary
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ) :=
  StandardComplex.boundary.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (standardUnipotent_antitone i ν hOrder hG hi hν) E q

/-- The canonical projection onto the retained quotient at degree `q`. -/
abbrev rationalTerminalProjection
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) (q : ℕ) :=
  StandardComplex.terminalProjection.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (standardUnipotent_antitone i ν hOrder hG hi hν) E q

/-- The retained cokernel at removed-root degree `|S| - |I|`. -/
abbrev rationalSharpObject
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (I : Finset (SimpleRoot i ν)) :=
  StandardComplex.sharpObject.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (standardUnipotent_antitone i ν hOrder hG hi hν) E I

/-- The same actual cokernel, functorial on all smooth modules. -/
abbrev rationalSharpFunctor (I : Finset (SimpleRoot i ν)) :=
  StandardComplex.sharpFunctor.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (standardUnipotent_antitone i ν hOrder hG hi hν) I

/-- The actual initial map into removed-root degree zero. -/
abbrev rationalInitialMap
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) :=
  StandardComplex.initialMap.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardUnipotent_isUnimodular i ν hU hUc) E

/-- The full-root endpoint identifies the initial object with `E`. -/
abbrev rationalInitialEquiv (hEndpoints : StandardParabolicEndpointsStatement.{u})
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) :=
  StandardComplex.initialEquiv.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_univ i ν hEndpoints hG hi hν)
    (standardUnipotent_univ i ν hEndpoints hG hi hν) E

/-- The canonical first differential from the actual input representation. -/
abbrev rationalInitialDifferential
    (E : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) :=
  StandardComplex.initialDifferential.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardUnipotent_isUnimodular i ν hU hUc)
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (standardUnipotent_antitone i ν hOrder hG hi hν) E

end Complex

end Langlands.Aubert.General.RationalPointFamily
