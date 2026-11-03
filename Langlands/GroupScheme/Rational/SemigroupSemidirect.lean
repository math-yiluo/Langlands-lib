import Langlands.GroupScheme.Rational.TrivialAction
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.SemigroupComparisonStatement
import Langlands.GroupScheme.AutomorphicAction.SemidirectSubgroup
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # Exact semigroup factors in an actual semidirect product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} {K G : GroupScheme B} (a : AutomorphicAction K G)

/-- A subgroup of a semidirect product containing the acting factor restricts
to an inner-action stable subgroup of its normal factor. -/
theorem isStable_comap_inl_of_range_inr_le
    (V : SubgroupFunctor a.semidirectProduct)
    (hK : SubgroupFunctor.range a.semidirectInr ≤ V) :
    a.IsStable (V.comap a.semidirectInl) := by
  intro T k g hg
  change a.act k g ≫ a.semidirectInl.hom.hom ∈ V.carrier T
  rw [← a.semidirect_conjugation, conjugation_act]
  exact (V.carrier T).mul_mem
    ((V.carrier T).mul_mem (hK T ⟨k, rfl⟩) hg)
    ((V.carrier T).inv_mem (hK T ⟨k, rfl⟩))

/-- Containment of the acting factor recovers the whole subgroup from its
restriction to the normal factor on every test scheme. -/
theorem eq_semidirectSubgroup_comap_inl
    (V : SubgroupFunctor a.semidirectProduct)
    (hK : SubgroupFunctor.range a.semidirectInr ≤ V) :
    V = a.semidirectSubgroup (V.comap a.semidirectInl)
      (a.isStable_comap_inl_of_range_inr_le V hK) := by
  apply le_antisymm
  · intro T z hz
    change (a.semidirectPointsEquiv T z).left ≫ a.semidirectInl.hom.hom ∈ V.carrier T
    have hd := a.semidirect_point_decomposition z
    have hm := (V.carrier T).mul_mem hz
      ((V.carrier T).inv_mem (hK T ⟨(a.semidirectPointsEquiv T z).right, rfl⟩))
    change z * ((a.semidirectPointsEquiv T z).right ≫ a.semidirectInr.hom.hom)⁻¹ ∈
      V.carrier T at hm
    have hc : z * ((a.semidirectPointsEquiv T z).right ≫ a.semidirectInr.hom.hom)⁻¹ =
        (a.semidirectPointsEquiv T z).left ≫ a.semidirectInl.hom.hom := by
      calc
        _ = (((a.semidirectPointsEquiv T z).left ≫ a.semidirectInl.hom.hom) *
            ((a.semidirectPointsEquiv T z).right ≫ a.semidirectInr.hom.hom)) *
            ((a.semidirectPointsEquiv T z).right ≫ a.semidirectInr.hom.hom)⁻¹ :=
          congrArg (fun w => w *
            ((a.semidirectPointsEquiv T z).right ≫ a.semidirectInr.hom.hom)⁻¹) hd
        _ = _ := mul_inv_cancel_right _ _
    rw [hc] at hm
    exact hm
  · apply (a.semidirectSubgroup_le_iff _ _ V).2
    refine ⟨?_, hK⟩
    intro T z hz
    rcases SubgroupFunctor.mem_map.mp hz with ⟨g, hg, rfl⟩
    exact hg

end AutomorphicAction

namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {K G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] [IsAffineHom G.X.hom]
    [Smooth K.X.hom] [Smooth G.X.hom]
    (a : AutomorphicAction K G) (b : AutomorphicAction S.toGrp G)
    (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (q : T ⟶ K.X) (g : T ⟶ G.X), b.act s (a.act q g) = a.act q (b.act s g))
    (hS : IsSplitTorus S.toGrp)

include hS hcomm

/-- Equivariant functoriality through the actual projection removes the acting
coordinate from any semigroup that excludes zero. -/
theorem semigroupSubgroup_semidirect_le_range_inl
    (hfun : SemigroupFunctorialityStatement.{u})
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∉ A) :
    semigroupSubgroup (a.semidirectLift b hcomm) A ≤
      SubgroupFunctor.range a.semidirectInl := by
  have hp := hfun k a.semidirectProduct K inferInstance inferInstance
    inferInstance inferInstance S hS (a.semidirectLift b hcomm)
    (AutomorphicAction.trivial S.toGrp K) a.semidirectProjection
    (fun T s z => by
      rw [AutomorphicAction.trivial_act, AutomorphicAction.semidirectLift_projection]) A
  rw [semigroupSubgroup_eq_bot_of_act_eq (AutomorphicAction.trivial S.toGrp K)
    (fun _ s q => AutomorphicAction.trivial_act S.toGrp K s q) hS A hzero] at hp
  intro T z hz
  apply (a.mem_range_semidirectInl_iff z).2
  exact hp T ⟨z, hz, rfl⟩

/-- With zero excluded, the exact ambient semigroup functor is the image of
the normal-factor semigroup functor. No intersection comparison is used. -/
theorem semigroupSubgroup_semidirect_eq_map_of_zero_notMem
    (hfun : SemigroupFunctorialityStatement.{u})
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∉ A) :
    semigroupSubgroup (a.semidirectLift b hcomm) A =
      (semigroupSubgroup b A).map a.semidirectInl := by
  symm
  exact semigroupSubgroup_map_eq a.semidirectInl a.isClosedSubgroup_semidirectInl
    b (a.semidirectLift b hcomm)
    (fun _ s g => (a.semidirectLift_inl b hcomm s g).symm) A
    (semigroupSubgroup_semidirect_le_range_inl a b hcomm hS hfun A hzero)

/-- A semigroup containing zero contains every acting-factor point, because
the lifted external action on that factor is the actual trivial action. -/
theorem range_inr_le_semigroupSubgroup_semidirect
    [ConnectedSpace K.X.left]
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    SubgroupFunctor.range a.semidirectInr ≤
      semigroupSubgroup (a.semidirectLift b hcomm) A := by
  have ht := semigroupSubgroup_eq_top_of_act_eq (AutomorphicAction.trivial S.toGrp K)
    (fun _ s q => AutomorphicAction.trivial_act S.toGrp K s q) hS
    inferInstance inferInstance A hzero
  have hm := semigroupSubgroup_map_le a.semidirectInr a.isClosedSubgroup_semidirectInr
    (AutomorphicAction.trivial S.toGrp K) (a.semidirectLift b hcomm)
    (fun _ s q => by
      rw [AutomorphicAction.trivial_act, AutomorphicAction.semidirectLift_inr]) A
  intro T z hz
  rcases SubgroupFunctor.mem_range.mp hz with ⟨q, rfl⟩
  apply hm T
  refine ⟨q, ?_, rfl⟩
  rw [ht]
  exact Subgroup.mem_top _

omit hS hcomm [IsAffineHom K.X.hom] [IsAffineHom G.X.hom]
    [Smooth K.X.hom] [Smooth G.X.hom] in
/-- The normal inclusion is normal on all tests, since it is the kernel of
the actual projection to the acting factor. -/
theorem range_semidirectInl_isNormal :
    (SubgroupFunctor.range a.semidirectInl).IsNormal := by
  intro T z x _ hx
  apply (a.mem_range_semidirectInl_iff _).2
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    (a.mem_range_semidirectInl_iff x).1 hx, mul_one, mul_inv_cancel]

/-- The source intersection comparison identifies the exact restriction of
every semigroup functor to the normal factor. -/
theorem semigroupSubgroup_semidirect_comap_inl
    [ConnectedSpace G.X.left]
    (hinter : SemigroupIntersectionStatement.{u})
    (A : AddSubsemigroup (characterLattice S)) :
    (semigroupSubgroup (a.semidirectLift b hcomm) A).comap a.semidirectInl =
      semigroupSubgroup b A := by
  exact hinter k a.semidirectProduct G inferInstance inferInstance
    inferInstance inferInstance inferInstance S hS (a.semidirectLift b hcomm) b
    a.semidirectInl a.isClosedSubgroup_semidirectInl
    (fun _ s g => (a.semidirectLift_inl b hcomm s g).symm) A
    (Or.inr (Or.inr (range_semidirectInl_isNormal a)))

/-- When zero is selected, the normal-factor semigroup is stable under the
inner action. This is derived from the source intersection comparison. -/
theorem semigroupSubgroup_isStable_inner_of_zero_mem
    [ConnectedSpace G.X.left] [ConnectedSpace K.X.left]
    (hinter : SemigroupIntersectionStatement.{u})
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    a.IsStable (semigroupSubgroup b A) := by
  rw [← semigroupSubgroup_semidirect_comap_inl a b hcomm hS hinter A]
  exact a.isStable_comap_inl_of_range_inr_le _
    (range_inr_le_semigroupSubgroup_semidirect a b hcomm hS A hzero)

/-- The exact semigroup containing zero is the extension of its normal-factor
semigroup by the whole acting group, on every test scheme. -/
theorem semigroupSubgroup_semidirect_eq_of_zero_mem
    [ConnectedSpace G.X.left] [ConnectedSpace K.X.left]
    (hinter : SemigroupIntersectionStatement.{u})
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A) :
    semigroupSubgroup (a.semidirectLift b hcomm) A =
      a.semidirectSubgroup (semigroupSubgroup b A)
        (semigroupSubgroup_isStable_inner_of_zero_mem a b hcomm hS hinter A hzero) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro z
  have he := congrArg (fun F : SubgroupFunctor a.semidirectProduct => F.carrier T)
    (a.eq_semidirectSubgroup_comap_inl
      (semigroupSubgroup (a.semidirectLift b hcomm) A)
      (range_inr_le_semigroupSubgroup_semidirect a b hcomm hS A hzero))
  change z ∈ (semigroupSubgroup (a.semidirectLift b hcomm) A).carrier T ↔
    (a.semidirectPointsEquiv T z).left ∈ (semigroupSubgroup b A).carrier T
  rw [he]
  change (a.semidirectPointsEquiv T z).left ∈
      ((semigroupSubgroup (a.semidirectLift b hcomm) A).comap a.semidirectInl).carrier T ↔ _
  rw [semigroupSubgroup_semidirect_comap_inl a b hcomm hS hinter A]

section Representatives

variable [ConnectedSpace G.X.left] [ConnectedSpace K.X.left]
    (hinter : SemigroupIntersectionStatement.{u})
    (A : AddSubsemigroup (characterLattice S)) (hzero : 0 ∈ A)
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) (hj : (semigroupSubgroup b A).IsRepresentedBy j)

/-- The actual semidirect action on a representative of a zero-containing
normal-factor semigroup, with stability proved from intersection. -/
def semidirectSemigroupAction : AutomorphicAction K H :=
  a.onRepresentedSubgroup j hj
    (semigroupSubgroup_isStable_inner_of_zero_mem a b hcomm hS hinter A hzero)

/-- The actual inclusion representing the zero-containing semigroup in the
semidirect group scheme. -/
def semidirectSemigroupInclusion :
    (semidirectSemigroupAction a b hcomm hS hinter A hzero j hj).semidirectProduct ⟶
      a.semidirectProduct :=
  a.semidirectSubgroupInclusion (semigroupSubgroup b A)
    (semigroupSubgroup_isStable_inner_of_zero_mem a b hcomm hS hinter A hzero) j hj

/-- The inclusion represents the exact existing ambient semigroup functor. -/
theorem isRepresentedBy_semidirectSemigroupInclusion :
    (semigroupSubgroup (a.semidirectLift b hcomm) A).IsRepresentedBy
      (semidirectSemigroupInclusion a b hcomm hS hinter A hzero j hj) := by
  rw [semigroupSubgroup_semidirect_eq_of_zero_mem a b hcomm hS hinter A hzero]
  exact a.isRepresentedBy_semidirectSubgroupInclusion _ _ j hj

/-- The constructed semigroup inclusion is closed whenever the original
normal-factor inclusion is closed. -/
theorem isClosedSubgroup_semidirectSemigroupInclusion (hjc : IsClosedSubgroup j) :
    IsClosedSubgroup (semidirectSemigroupInclusion a b hcomm hS hinter A hzero j hj) :=
  a.isClosedSubgroup_semidirectSubgroupInclusion _ _ j hj hjc

end Representatives

end RelativeRoot

end Langlands.GroupScheme
