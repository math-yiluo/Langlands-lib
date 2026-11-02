import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Group.RelativeWeylIndexing

/-!
# Actual normalized intersection terms and the general geometric-lemma K0 target
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep
open Langlands.Group

section Intersections

variable {G : Type uG} [Group G]

/-- Source-side actual intersection `B ∩ n⁻¹ A n`. -/
def geometricSourceIntersection (A B : Subgroup G) (n : G) : Subgroup G :=
  B ⊓ A.map (MulAut.conj n⁻¹ : G →* G)

/-- Target-side actual intersection `A ∩ n B n⁻¹`. -/
def geometricTargetIntersection (A B : Subgroup G) (n : G) : Subgroup G :=
  A ⊓ B.map (MulAut.conj n : G →* G)

/-- Actual inverse conjugation identifies the two intersection subgroups. -/
theorem geometricIntersectionMembership (A B : Subgroup G) (n : G) :
    ∀ x : G, x ∈ geometricTargetIntersection A B n ↔
      n⁻¹ * x * n ∈ geometricSourceIntersection A B n := by
  intro x
  change (x ∈ A ∧ x ∈ B.map (MulAut.conj n).toMonoidHom) ↔
    (n⁻¹ * x * n ∈ B ∧ n⁻¹ * x * n ∈ A.map (MulAut.conj n⁻¹).toMonoidHom)
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply, mul_assoc, and_comm]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation preserves closedness of an actual subgroup. -/
theorem isClosed_map_conj (A : Subgroup G) (hA : IsClosed (A : Set G)) (n : G) :
    IsClosed (A.map (MulAut.conj n : G →* G) : Set G) := by
  have heq : (A.map (MulAut.conj n : G →* G) : Set G) =
      (fun x : G => n⁻¹ * x * n) ⁻¹' (A : Set G) := by
    ext x
    exact Subgroup.mem_map_equiv
  rw [heq]
  exact hA.preimage (by fun_prop)

theorem isClosed_geometricSourceIntersection
    (A B : Subgroup G) (hA : IsClosed (A : Set G)) (hB : IsClosed (B : Set G))
    (n : G) : IsClosed (geometricSourceIntersection A B n : Set G) :=
  hB.inter (isClosed_map_conj A hA n⁻¹)

theorem isClosed_geometricTargetIntersection
    (A B : Subgroup G) (hA : IsClosed (A : Set G)) (hB : IsClosed (B : Set G))
    (n : G) : IsClosed (geometricTargetIntersection A B n : Set G) :=
  hA.inter (isClosed_map_conj B hB n)

end Intersections

section Terms

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)

/-- The actual source intersection parabolic has its actual intersection Levi
and radical, all read inside `M J`. This is a separately named prerequisite. -/
def GeometricSourceDecomposition (I J : Finset ι) (n : G) : Prop :=
  IsSemidirectDecomposition
    ((geometricSourceIntersection (P I) (M J) n).subgroupOf (M J))
    ((geometricSourceIntersection (M I) (M J) n).subgroupOf (M J))
    ((geometricSourceIntersection (U I) (M J) n).subgroupOf (M J))

/-- The actual target intersection parabolic has its actual intersection Levi
and radical, all read inside `M I`. This is a separately named prerequisite. -/
def GeometricTargetDecomposition (I J : Finset ι) (n : G) : Prop :=
  IsSemidirectDecomposition
    ((geometricTargetIntersection (M I) (P J) n).subgroupOf (M I))
    ((geometricTargetIntersection (M I) (M J) n).subgroupOf (M I))
    ((geometricTargetIntersection (M I) (U J) n).subgroupOf (M I))

variable (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))

/-- Actual normalized Jacquet restriction from `M J` to `M J ∩ n⁻¹(M I)n`,
for the actual source intersection parabolic. -/
def geometricSourceJacquetFunctor (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n) :
    SmoothRep.{0, uG, uV} ℂ (M J) ⥤
      SmoothRep.{0, uG, uV} ℂ (geometricSourceIntersection (M I) (M J) n) :=
  leviNormalizedJacquetFunctor (hM J) inf_le_left hs
    (isClosed_geometricSourceIntersection (U I) (M J) (hU I) (hM J) n)

/-- Actual normalized induction from `M I ∩ n(M J)n⁻¹` to `M I`,
for the actual target intersection parabolic. -/
def geometricTargetInductionFunctor (I J : Finset ι) (n : G)
    (ht : GeometricTargetDecomposition P M U I J n) :
    SmoothRep.{0, uG, uV} ℂ (geometricTargetIntersection (M I) (M J) n) ⥤
      SmoothRep.{0, uG, max uG uV} ℂ (M I) :=
  leviNormalizedInductionFunctor (hM I) inf_le_left ht
    (isClosed_geometricTargetIntersection (M I) (U J) (hM I) (hU J) n)

/-- The normalized actual intersection term of the geometric lemma:
source Jacquet restriction, forward conjugation transport by `n`, then target
induction, on the full smooth categories with saturated carrier universe. -/
def geometricTermFunctor (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n) :
    SmoothRep.{0, uG, max uG uV} ℂ (M J) ⥤
      SmoothRep.{0, uG, max uG uV} ℂ (M I) :=
  geometricSourceJacquetFunctor P M U hM hU I J n hs ⋙
    conjugationFunctor n (geometricIntersectionMembership (M I) (M J) n) ⋙
      geometricTargetInductionFunctor P M U hM hU I J n ht

/-- Named representation prerequisites for the actual source Jacquet and
target induction functors. Conjugation transport is an equivalence and needs
no additional finite-length or exactness premise. -/
def GeometricTermFiniteLength (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n) : Prop :=
  PreservesFiniteLength (geometricSourceJacquetFunctor.{uI, uG, max uG uV}
    P M U hM hU I J n hs) ∧
  PreservesFiniteLengthShortExact (geometricSourceJacquetFunctor.{uI, uG, max uG uV}
    P M U hM hU I J n hs) ∧
  PreservesFiniteLength (geometricTargetInductionFunctor.{uI, uG, max uG uV}
    P M U hM hU I J n ht) ∧
  PreservesFiniteLengthShortExact (geometricTargetInductionFunctor.{uI, uG, max uG uV}
    P M U hM hU I J n ht)

/-- The exact-K0 map of the actual normalized intersection term. -/
def geometricTermK0 (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M I) :=
  (FiniteLengthGrothendieckGroup.map
    (geometricTargetInductionFunctor P M U hM hU I J n ht) hfl.2.2.1 hfl.2.2.2).comp
    ((conjugationK0 n (geometricIntersectionMembership (M I) (M J) n)).comp
      (FiniteLengthGrothendieckGroup.map
        (geometricSourceJacquetFunctor P M U hM hU I J n hs) hfl.1 hfl.2.1))

theorem geometricTerm_hasFiniteLength (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (hA : A.HasFiniteLength) :
    ((geometricTermFunctor P M U hM hU I J n hs ht).obj A).HasFiniteLength :=
  hfl.2.2.1 _
    (pullbackFunctor_preservesFiniteLength
      (conjugationEquiv n (geometricIntersectionMembership (M I) (M J) n))
      _ (hfl.1 A hA))

set_option maxHeartbeats 800000 in
/-- The class of the actual normalized intersection functor, with its
finite-length witness derived from the displayed named premises. -/
theorem geometricTermK0_ofRepresentation (I J : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (ht : GeometricTargetDecomposition P M U I J n)
    (hfl : GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht)
    (A : SmoothRep.{0, uG, max uG uV} ℂ (M J)) (hA : A.HasFiniteLength) :
    geometricTermK0.{uI, uG, uV} P M U hM hU I J n hs ht hfl
        (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((geometricTermFunctor.{uI, uG, uV} P M U hM hU I J n hs ht).obj A)
        (geometricTerm_hasFiniteLength.{uI, uG, uV} P M U hM hU I J n hs ht hfl A hA) := by
  rw [geometricTermK0, LinearMap.comp_apply, LinearMap.comp_apply,
    FiniteLengthGrothendieckGroup.map_ofRepresentation]
  rw [conjugationK0_ofRepresentation n (geometricIntersectionMembership (M I) (M J) n)
    _ (hfl.1 A hA)
    (pullbackFunctor_preservesFiniteLength
      (conjugationEquiv n (geometricIntersectionMembership (M I) (M J) n))
      _ (hfl.1 A hA))]
  exact FiniteLengthGrothendieckGroup.map_ofRepresentation
    (geometricTargetInductionFunctor P M U hM hU I J n ht)
    hfl.2.2.1 hfl.2.2.2 _
    (pullbackFunctor_preservesFiniteLength
      (conjugationEquiv n (geometricIntersectionMembership (M I) (M J) n))
      _ (hfl.1 A hA))

end Terms

section Expansion

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]
variable (P M U : Finset ι → Subgroup G)

/-- The actual intersection decompositions required at every minimum
representative and every normalizer lift; no representation identity is
included in this structural realization target. -/
def GeometricIntersectionDecompositions
    (T : Subgroup G) {CM : CoxeterMatrix ι}
    (actual : RelativeWeylIndexing.ActualCoxeterSystem T CM) : Prop :=
  ∀ (I J : Finset ι) (w : RelativeWeyl.Weyl T),
    RelativeWeylIndexing.IsMinimal actual I J w →
    ∀ n : RelativeWeyl.normalizer T, QuotientGroup.mk n = w →
      GeometricSourceDecomposition P M U I J (n : G) ∧
        GeometricTargetDecomposition P M U I J (n : G)

/-- Aubert (1.3), as equality of actual normalized exact-K0 maps. Each
summand is built from the actual intersection parabolics, their actual
Jacquet/induction functors and actual normalizer conjugation. Every section
of the actual normalizer quotient is quantified. This declares a target,
not a consequence of the supplied decompositions or preservation hypotheses. -/
def GeometricK0ExpansionStatement
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
    (hM : ∀ I, IsClosed (M I : Set G))
    (T : Subgroup G) [Fintype (RelativeWeyl.Weyl T)]
    {CM : CoxeterMatrix ι} (actual : RelativeWeylIndexing.ActualCoxeterSystem T CM)
    (hInter : GeometricIntersectionDecompositions P M U T actual)
    (hTermFl : ∀ (I J : Finset ι) (w : RelativeWeyl.Weyl T)
      (hw : RelativeWeylIndexing.IsMinimal actual I J w)
      (n : RelativeWeyl.normalizer T) (hn : QuotientGroup.mk n = w),
      GeometricTermFiniteLength.{uI, uG, uV} P M U hM hU I J (n : G)
        (hInter I J w hw n hn).1 (hInter I J w hw n hn).2) : Prop := by
  classical
  exact ∀ (I J : Finset ι)
    (lift : RelativeWeyl.Weyl T → RelativeWeyl.normalizer T)
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w),
    (jacquetK0 (h I) (hU I) (hfl I).2.2.1 (hfl I).2.2.2).comp
        (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1) =
      ∑ w : {w : RelativeWeyl.Weyl T // w ∈ RelativeWeylIndexing.minimalReps actual I J},
        geometricTermK0 P M U hM hU I J (lift w : G)
          (hInter I J w ((RelativeWeylIndexing.mem_minimalReps actual I J w).mp w.property)
            (lift w) (hlift w)).1
          (hInter I J w ((RelativeWeylIndexing.mem_minimalReps actual I J w).mp w.property)
            (lift w) (hlift w)).2
          (hTermFl I J w ((RelativeWeylIndexing.mem_minimalReps actual I J w).mp w.property)
            (lift w) (hlift w))

end Expansion

end Langlands.Aubert.General
