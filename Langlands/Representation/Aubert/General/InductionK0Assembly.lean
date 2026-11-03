import Langlands.Representation.Aubert.General.GeometricK0Target
import Langlands.Group.RelativeWeylSignedSum

/-! # Finite assembly on the actual exact Grothendieck groups -/

noncomputable section

open CategoryTheory
open Classical
open scoped BigOperators

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep
open Langlands.Group

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
  (hM : ∀ I, IsClosed (M I : Set G))

section LeviTerms

variable (J : Finset ι)
  (hJ : ∀ K : Finset J,
    IsSemidirectDecomposition ((P (leviIndex J K)).subgroupOf (M J))
      ((M (leviIndex J K)).subgroupOf (M J))
      ((U (leviIndex J K)).subgroupOf (M J)))
  (hLfl : letI := (hM J).locallyCompactSpace
    ∀ K : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hJ K)
      ((hU (leviIndex J K)).preimage continuous_subtype_val))

/-- The actual restricted-Levi alternating term followed by actual induction
from `M J` to `G`. -/
def inducedLeviAlternatingTerm (K : Finset J) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G :=
  letI := (hM J).locallyCompactSpace
  (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1).comp
    (alternatingTerm
      (fun K : Finset J => (P (leviIndex J K)).subgroupOf (M J))
      (fun K => (M (leviIndex J K)).subgroupOf (M J))
      (fun K => (U (leviIndex J K)).subgroupOf (M J))
      hJ (fun K => (hU (leviIndex J K)).preimage continuous_subtype_val) hLfl K)

omit [Fintype ι] in
/-- Summing the induced restricted terms is induction composed with the
literal restricted-Levi operator, with its original signs. -/
theorem sum_inducedLeviAlternatingTerm :
    (∑ K : Finset J, ((-1 : ℤ) ^ K.card) •
      inducedLeviAlternatingTerm P M U h hU hfl hM J hJ hLfl K) =
    (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1).comp
      (leviAlternatingOperator P M U J (hM J) hJ hU hLfl) := by
  let _ := (hM J).locallyCompactSpace
  apply LinearMap.ext
  intro x
  simp only [inducedLeviAlternatingTerm, leviAlternatingOperator, alternatingOperator,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_zsmul]

end LeviTerms

section GeometricTerms

variable (T : Subgroup G) [Fintype (RelativeWeyl.Weyl T)]
  {CM : CoxeterMatrix ι} (actual : RelativeWeylIndexing.ActualCoxeterSystem T CM)
  (hInter : GeometricIntersectionDecompositions P M U T actual)
  (hTermFl : ∀ (I J : Finset ι) (w : RelativeWeyl.Weyl T)
    (hw : RelativeWeylIndexing.IsMinimal actual I J w)
    (n : RelativeWeyl.normalizer T) (hn : QuotientGroup.mk n = w),
    GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J (n : G)
      (hInter I J w hw n hn).1 (hInter I J w hw n hn).2)

/-- The actual geometric intersection map followed by ambient induction
from its target Levi. No reduction to a standard source intersection is
asserted by this definition. -/
def inducedGeometricTerm (I J : Finset ι) (w : RelativeWeyl.Weyl T)
    (hw : RelativeWeylIndexing.IsMinimal actual I J w)
    (n : RelativeWeyl.normalizer T) (hn : QuotientGroup.mk n = w) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G :=
  (inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1).comp
    (geometricTermK0 P M U hM hU I J (n : G)
      (hInter I J w hw n hn).1 (hInter I J w hw n hn).2
      (hTermFl I J w hw n hn))

variable
  (hExpansion : GeometricK0ExpansionStatement.{uI, uG, uV}
    P M U h hU hfl hM T actual hInter hTermFl)
  (J : Finset ι)
  (lift : RelativeWeyl.Weyl T → RelativeWeyl.normalizer T)
  (hlift : ∀ w, QuotientGroup.mk (lift w) = w)

include hExpansion in
/-- Expanding Jacquet after induction by the actual geometric-lemma equation
expands `D_G` after induction into the signed induced intersection terms. -/
theorem alternatingOperator_comp_induction_eq_geometricSum :
    (alternatingOperator P M U h hU hfl).comp
        (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1) =
      ∑ I : Finset ι, ((-1 : ℤ) ^ I.card) •
        ∑ w : {w : RelativeWeyl.Weyl T //
            w ∈ RelativeWeylIndexing.minimalReps actual I J},
          inducedGeometricTerm P M U h hU hfl hM T actual hInter hTermFl I J w
            ((RelativeWeylIndexing.mem_minimalReps actual I J w).mp w.property)
            (lift w) (hlift w) := by
  have hrow (I : Finset ι) :
      (alternatingTerm P M U h hU hfl I).comp
          (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1) =
        ∑ w : {w : RelativeWeyl.Weyl T //
            w ∈ RelativeWeylIndexing.minimalReps actual I J},
          inducedGeometricTerm P M U h hU hfl hM T actual hInter hTermFl I J w
            ((RelativeWeylIndexing.mem_minimalReps actual I J w).mp w.property)
            (lift w) (hlift w) := by
    unfold alternatingTerm
    rw [LinearMap.comp_assoc, hExpansion I J lift hlift]
    apply LinearMap.ext
    intro x
    simp [inducedGeometricTerm, LinearMap.comp_apply, map_sum]
  apply LinearMap.ext
  intro x
  simp only [alternatingOperator, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun I _ => ?_
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
    congrArg (fun f => ((-1 : ℤ) ^ I.card) • f x) (hrow I)

variable
  (hJ : ∀ K : Finset J,
    IsSemidirectDecomposition ((P (leviIndex J K)).subgroupOf (M J))
      ((M (leviIndex J K)).subgroupOf (M J))
      ((U (leviIndex J K)).subgroupOf (M J)))
  (hLfl : letI := (hM J).locallyCompactSpace
    ∀ K : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hJ K)
      ((hU (leviIndex J K)).preimage continuous_subtype_val))

include hExpansion in
/-- Conditional finite assembly: the actual geometric expansion and an actual
termwise induction/transitivity/conjugacy reduction imply the operator equation.
The reduction is an explicit unproved input here, not a new premise of the
rational-point induction compatibility target. -/
theorem inductionCompatibility_of_geometricExpansion
    (hReduction : ∀ (I : Finset ι)
      (w : {w : RelativeWeyl.Weyl T //
        w ∈ RelativeWeylIndexing.minimalReps actual I J}),
      inducedGeometricTerm P M U h hU hfl hM T actual hInter hTermFl I J w
          ((RelativeWeylIndexing.mem_minimalReps actual I J w).mp w.property)
          (lift w) (hlift w) =
        inducedLeviAlternatingTerm P M U h hU hfl hM J hJ hLfl
          ((RelativeWeylIndexing.intersectionSubset actual I J w).subtype (· ∈ J))) :
    (alternatingOperator P M U h hU hfl).comp
        (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1) =
      (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1).comp
        (leviAlternatingOperator P M U J (hM J) hJ hU hLfl) := by
  classical
  rw [alternatingOperator_comp_induction_eq_geometricSum
    P M U h hU hfl hM T actual hInter hTermFl hExpansion J lift hlift]
  have hsum (I : Finset ι) :
      (∑ w : {w : RelativeWeyl.Weyl T //
          w ∈ RelativeWeylIndexing.minimalReps actual I J},
        inducedGeometricTerm P M U h hU hfl hM T actual hInter hTermFl I J w
          ((RelativeWeylIndexing.mem_minimalReps actual I J w).mp w.property)
          (lift w) (hlift w)) =
        ∑ w ∈ RelativeWeylIndexing.minimalReps actual I J,
          inducedLeviAlternatingTerm P M U h hU hfl hM J hJ hLfl
            ((RelativeWeylIndexing.intersectionSubset actual I J w).subtype (· ∈ J)) := by
    calc
      _ = ∑ w : {w : RelativeWeyl.Weyl T //
          w ∈ RelativeWeylIndexing.minimalReps actual I J},
        inducedLeviAlternatingTerm P M U h hU hfl hM J hJ hLfl
          ((RelativeWeylIndexing.intersectionSubset actual I J w).subtype (· ∈ J)) :=
        Finset.sum_congr rfl fun w _ => hReduction I w
      _ = _ := Finset.sum_coe_sort (RelativeWeylIndexing.minimalReps actual I J)
        (fun w => inducedLeviAlternatingTerm P M U h hU hfl hM J hJ hLfl
          ((RelativeWeylIndexing.intersectionSubset actual I J w).subtype (· ∈ J)))
  calc
    _ = ∑ I : Finset ι, ((-1 : ℤ) ^ I.card) •
        ∑ w ∈ RelativeWeylIndexing.minimalReps actual I J,
          inducedLeviAlternatingTerm P M U h hU hfl hM J hJ hLfl
            ((RelativeWeylIndexing.intersectionSubset actual I J w).subtype (· ∈ J)) :=
      Finset.sum_congr rfl fun I _ => congrArg (fun z => ((-1 : ℤ) ^ I.card) • z) (hsum I)
    _ = _ := ?_
  change RelativeWeylIndexing.signedIntersectionSum actual J
    (fun K => inducedLeviAlternatingTerm P M U h hU hfl hM J hJ hLfl
      (K.subtype (· ∈ J))) = _
  rw [RelativeWeylIndexing.signedIntersectionSum_eq_sum_subtype]
  have hindex (K : Finset J) :
      (leviIndex J K).subtype (· ∈ J) = K := by
    ext b
    simp [leviIndex]
  simp_rw [show ∀ K : Finset J,
    (K.map (Function.Embedding.subtype (· ∈ J))).subtype (· ∈ J) = K from hindex]
  exact sum_inducedLeviAlternatingTerm P M U h hU hfl hM J hJ hLfl

end GeometricTerms

end Langlands.Aubert.General
