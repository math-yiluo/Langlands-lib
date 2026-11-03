import Langlands.Representation.Aubert.General.GeometricK0Target
import Langlands.Representation.Aubert.General.JacquetTarget
import Langlands.Group.RelativeWeylJacquetWeighted
import Langlands.Group.RelativeWeylAssociatedIndexing

/-! # Conditional longest-representative assembly on actual exact K0 -/

noncomputable section

open CategoryTheory Classical
open scoped BigOperators

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep Langlands.Group RelativeWeylIndexing

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
  (hM : ∀ I, IsClosed (M I : Set G))

section TransportedTerms

variable (J J' : Finset ι) (g : G)
  (hconj : ∀ x : G, x ∈ M J ↔ g⁻¹ * x * g ∈ M J')
  (hJ' : ∀ K : Finset J',
    IsSemidirectDecomposition ((P (leviIndex J' K)).subgroupOf (M J'))
      ((M (leviIndex J' K)).subgroupOf (M J'))
      ((U (leviIndex J' K)).subgroupOf (M J')))
  (hLfl : letI := (hM J').locallyCompactSpace
    ∀ K : Finset J', ParabolicFiniteLength.{uG, max uG uV} (hJ' K)
      ((hU (leviIndex J' K)).preimage continuous_subtype_val))

/-- One literal restricted-Levi alternating term, preceded by ambient Jacquet
restriction and followed by the specified actual conjugation transport. -/
def transportedLeviJacquetTerm (K : Finset J') :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) :=
  letI := (hM J').locallyCompactSpace
  (conjugationK0 g hconj).comp
    ((alternatingTerm
      (fun K : Finset J' => (P (leviIndex J' K)).subgroupOf (M J'))
      (fun K => (M (leviIndex J' K)).subgroupOf (M J'))
      (fun K => (U (leviIndex J' K)).subgroupOf (M J'))
      hJ' (fun K => (hU (leviIndex J' K)).preimage continuous_subtype_val) hLfl K).comp
      (jacquetK0 (h J') (hU J') (hfl J').2.2.1 (hfl J').2.2.2))

omit [Fintype ι] in
/-- The transported terms sum to conjugation after the literal Levi operator
after ambient Jacquet restriction, with the original unadjusted signs. -/
theorem sum_transportedLeviJacquetTerm :
    (∑ K : Finset J', ((-1 : ℤ) ^ K.card) •
      transportedLeviJacquetTerm P M U h hU hfl hM J J' g hconj hJ' hLfl K) =
      (conjugationK0 g hconj).comp
        ((leviAlternatingOperator P M U J' (hM J') hJ' hU hLfl).comp
          (jacquetK0 (h J') (hU J') (hfl J').2.2.1 (hfl J').2.2.2)) := by
  let _ := (hM J').locallyCompactSpace
  apply LinearMap.ext
  intro x
  simp only [transportedLeviJacquetTerm, leviAlternatingOperator, alternatingOperator,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_zsmul]

end TransportedTerms

section GeometricTerms

variable (T : Subgroup G) [Fintype (RelativeWeyl.Weyl T)]
  {CM : CoxeterMatrix ι} (actual : ActualCoxeterSystem T CM)
  (hInter : GeometricIntersectionDecompositions P M U T actual)
  (hTermFl : ∀ (I J : Finset ι) (w : RelativeWeyl.Weyl T)
    (hw : IsMinimal actual I J w)
    (n : RelativeWeyl.normalizer T) (hn : QuotientGroup.mk n = w),
    GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J (n : G)
      (hInter I J w hw n hn).1 (hInter I J w hw n hn).2)

/-- An actual geometric intersection term for `r_J i_I`, composed with `r_I`.
The left and right minimality indices are literally `J,I`. -/
def jacquetGeometricTerm (J I : Finset ι) (w : RelativeWeyl.Weyl T)
    (hw : IsMinimal actual J I w)
    (n : RelativeWeyl.normalizer T) (hn : QuotientGroup.mk n = w) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) :=
  (geometricTermK0 P M U hM hU J I (n : G)
    (hInter J I w hw n hn).1 (hInter J I w hw n hn).2
    (hTermFl J I w hw n hn)).comp
      (jacquetK0 (h I) (hU I) (hfl I).2.2.1 (hfl I).2.2.2)

/-- The signed sum of actual geometric terms after ambient Jacquet restriction,
for a specified section of the actual normalizer quotient. -/
def jacquetGeometricSum (J : Finset ι)
    (lift : RelativeWeyl.Weyl T → RelativeWeyl.normalizer T)
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) :=
  ∑ I : Finset ι, ((-1 : ℤ) ^ I.card) •
    ∑ w : {w : RelativeWeyl.Weyl T // w ∈ minimalReps actual J I},
      jacquetGeometricTerm P M U h hU hfl hM T actual hInter hTermFl J I w
        ((mem_minimalReps actual J I w).mp w.property) (lift w) (hlift w)

variable
  (hExpansion : GeometricK0ExpansionStatement.{uI, uG, uV}
    P M U h hU hfl hM T actual hInter hTermFl)
  (J : Finset ι)
  (lift : RelativeWeyl.Weyl T → RelativeWeyl.normalizer T)
  (hlift : ∀ w, QuotientGroup.mk (lift w) = w)

include hExpansion in
/-- The supplied actual geometric expansion expands `r_J D_G` into the
constructed signed sum. It does not prove the geometric-lemma input. -/
theorem jacquetK0_comp_alternatingOperator_eq_geometricSum :
    (jacquetK0 (h J) (hU J) (hfl J).2.2.1 (hfl J).2.2.2).comp
        (alternatingOperator P M U h hU hfl) =
      jacquetGeometricSum P M U h hU hfl hM T actual hInter hTermFl J lift hlift := by
  have hrow (I : Finset ι) :
      (jacquetK0 (h J) (hU J) (hfl J).2.2.1 (hfl J).2.2.2).comp
          (alternatingTerm P M U h hU hfl I) =
        ∑ w : {w : RelativeWeyl.Weyl T // w ∈ minimalReps actual J I},
          jacquetGeometricTerm P M U h hU hfl hM T actual hInter hTermFl J I w
            ((mem_minimalReps actual J I w).mp w.property) (lift w) (hlift w) := by
    unfold alternatingTerm
    rw [← LinearMap.comp_assoc, hExpansion J I lift hlift]
    apply LinearMap.ext
    intro x
    simp [jacquetGeometricTerm, LinearMap.comp_apply]
  apply LinearMap.ext
  intro x
  simp only [alternatingOperator, jacquetGeometricSum, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun I _ => ?_
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
    congrArg (fun f => ((-1 : ℤ) ^ I.card) • f x) (hrow I)

/-- The unproved common-term comparison: the actual geometric term after `r_I`
depends on `I` only through `simpleImage actual w I ∩ J`. This is a
representation-theoretic input to the conditional assembly. -/
def JacquetGeometricTermReduction
    (F : RelativeWeyl.Weyl T → Finset ι →
      (FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G →ₗ[ℤ]
        FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J))) : Prop :=
  ∀ (I : Finset ι)
    (w : {w : RelativeWeyl.Weyl T // w ∈ minimalReps actual J I}),
    jacquetGeometricTerm P M U h hU hfl hM T actual hInter hTermFl J I w
        ((mem_minimalReps actual J I w).mp w.property) (lift w) (hlift w) =
      F w (simpleImage actual w I ∩ J)

variable
  (F : RelativeWeyl.Weyl T → Finset ι →
    (FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J)))

/-- The explicit common-term comparison identifies the actual sum with the
finite weighted expansion, without proving that comparison. -/
theorem jacquetGeometricSum_eq_weightedExpansion
    (hReduction : JacquetGeometricTermReduction
      P M U h hU hfl hM T actual hInter hTermFl J lift hlift F) :
    jacquetGeometricSum P M U h hU hfl hM T actual hInter hTermFl J lift hlift =
      jacquetWeightedExpansion actual J F := by
  unfold jacquetGeometricSum jacquetWeightedExpansion
  apply Finset.sum_congr rfl
  intro I _
  apply congrArg (fun z => ((-1 : ℤ) ^ I.card) • z)
  calc
    _ = ∑ w : {w : RelativeWeyl.Weyl T // w ∈ minimalReps actual J I},
        F w (simpleImage actual w I ∩ J) :=
      Finset.sum_congr rfl fun w _ => hReduction I w
    _ = _ := Finset.sum_coe_sort (minimalReps actual J I)
      (fun w => F w (simpleImage actual w I ∩ J))

variable
  (hAssociated : actualAssociatedLeviConjugation T M actual)
  (n : RelativeWeyl.normalizer T) (hn : QuotientGroup.mk n = longestRep actual J)
  (hJ' : ∀ K : Finset (associatedSubset actual J),
    IsSemidirectDecomposition
      ((P (leviIndex (associatedSubset actual J) K)).subgroupOf (M (associatedSubset actual J)))
      ((M (leviIndex (associatedSubset actual J) K)).subgroupOf (M (associatedSubset actual J)))
      ((U (leviIndex (associatedSubset actual J) K)).subgroupOf (M (associatedSubset actual J))))
  (hLfl : letI := (hM (associatedSubset actual J)).locallyCompactSpace
    ∀ K : Finset (associatedSubset actual J),
      ParabolicFiniteLength.{uG, max uG uV} (hJ' K)
        ((hU (leviIndex (associatedSubset actual J) K)).preimage continuous_subtype_val))

/-- The unproved survivor comparison, at the specified longest representative
and actual lift, with the associated subset and literal restricted families. -/
def JacquetLongestTermReduction : Prop :=
  ∀ K : Finset (associatedSubset actual J),
    F (longestRep actual J)
        (simpleImage actual (longestRep actual J) (leviIndex (associatedSubset actual J) K)) =
      transportedLeviJacquetTerm P M U h hU hfl hM J (associatedSubset actual J)
        (n : G) (conjugationMembership_of_map_eq (n : G) (hAssociated J n hn)) hJ' hLfl K

include hExpansion in
/-- Conditional Jacquet assembly. The actual geometric expansion, common-term
comparison, and survivor comparison remain explicit unproved inputs. -/
theorem jacquetCompatibility_of_geometricExpansion
    (hReduction : JacquetGeometricTermReduction
      P M U h hU hfl hM T actual hInter hTermFl J lift hlift F)
    (hLongest : JacquetLongestTermReduction
      P M U h hU hfl hM T actual J F hAssociated n hn hJ' hLfl) :
    (jacquetK0 (h J) (hU J) (hfl J).2.2.1 (hfl J).2.2.2).comp
        (alternatingOperator P M U h hU hfl) =
      (conjugationK0 (n : G)
        (conjugationMembership_of_map_eq (n : G) (hAssociated J n hn))).comp
        ((leviAlternatingOperator P M U (associatedSubset actual J)
          (hM (associatedSubset actual J)) hJ' hU hLfl).comp
          (jacquetK0 (h (associatedSubset actual J)) (hU (associatedSubset actual J))
            (hfl (associatedSubset actual J)).2.2.1 (hfl (associatedSubset actual J)).2.2.2)) := by
  calc
    _ = jacquetGeometricSum P M U h hU hfl hM T actual hInter hTermFl J lift hlift :=
      jacquetK0_comp_alternatingOperator_eq_geometricSum
        P M U h hU hfl hM T actual hInter hTermFl hExpansion J lift hlift
    _ = jacquetWeightedExpansion actual J F :=
      jacquetGeometricSum_eq_weightedExpansion
        P M U h hU hfl hM T actual hInter hTermFl J lift hlift F hReduction
    _ = ∑ K ∈ J.powerset, ((-1 : ℤ) ^ K.card) • F (longestRep actual J) K :=
      jacquetWeightedExpansion_eq_longest actual J F
    _ = ∑ K : Finset (associatedSubset actual J), ((-1 : ℤ) ^ K.card) •
        F (longestRep actual J)
          (simpleImage actual (longestRep actual J)
            (leviIndex (associatedSubset actual J) K)) :=
      signed_sum_associatedFinsetEquiv actual J (F (longestRep actual J))
    _ = ∑ K : Finset (associatedSubset actual J), ((-1 : ℤ) ^ K.card) •
        transportedLeviJacquetTerm P M U h hU hfl hM J (associatedSubset actual J)
          (n : G) (conjugationMembership_of_map_eq (n : G) (hAssociated J n hn)) hJ' hLfl K :=
      Finset.sum_congr rfl fun K _ => congrArg (fun z => ((-1 : ℤ) ^ K.card) • z) (hLongest K)
    _ = _ := sum_transportedLeviJacquetTerm P M U h hU hfl hM J (associatedSubset actual J)
      (n : G) (conjugationMembership_of_map_eq (n : G) (hAssociated J n hn)) hJ' hLfl

end GeometricTerms

end Langlands.Aubert.General
