import Langlands.GroupScheme.Rational.SemigroupOrderedSemidirect
import Langlands.GroupScheme.Rational.SemigroupCommutatorProof

/-! # Semidirect reduction with actual ambient weight support -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The additive semigroup consisting of the zero character alone. -/
def zeroCharacterSemigroup (S : CommGroupScheme (Spec (CommRingCat.of k))) :
    AddSubsemigroup (characterLattice S) where
  carrier := {0}
  add_mem' := by
    intro α β hα hβ
    change α = 0 at hα
    change β = 0 at hβ
    simp only [hα, hβ, zero_add, Set.mem_singleton_iff]

@[simp]
theorem mem_zeroCharacterSemigroup (χ : characterLattice S) :
    χ ∈ zeroCharacterSemigroup S ↔ χ = 0 := Iff.rfl

/-- Adding one zero character changes no semigroup, even an empty one. -/
@[simp]
theorem semigroupSum_zeroCharacterSemigroup (A : AddSubsemigroup (characterLattice S)) :
    semigroupSum (zeroCharacterSemigroup S) A = A := by
  apply le_antisymm
  · rintro χ ⟨α, hα, β, hβ, h⟩
    change α = 0 at hα
    subst α
    rw [zero_add] at h
    exact h ▸ hβ
  · intro χ hχ
    exact ⟨0, rfl, χ, hχ, zero_add χ⟩

variable {K G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] [IsAffineHom G.X.hom]
    [Smooth K.X.hom] [Smooth G.X.hom]
    [ConnectedSpace K.X.left] [ConnectedSpace G.X.left]
    (a : AutomorphicAction K G) (b : AutomorphicAction S.toGrp G)
    (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (q : T ⟶ K.X) (g : T ⟶ G.X), b.act s (a.act q g) = a.act q (b.act s g))
    (hS : IsSplitTorus S.toGrp)

include hcomm hS

omit [ConnectedSpace G.X.left] in
/-- The published commutator bound and the local inverse-image
equalities give inner stability for every semigroup, including those
excluding zero. -/
theorem semigroupSubgroup_isStable_inner_of_comap
    (hcomap : ∀ A : AddSubsemigroup (characterLattice S),
      (semigroupSubgroup (a.semidirectLift b hcomm) A).comap a.semidirectInl =
        semigroupSubgroup b A)
    (A : AddSubsemigroup (characterLattice S)) :
    a.IsStable (semigroupSubgroup b A) := by
  intro T q x hx
  have hq :
      q ≫ a.semidirectInr.hom.hom ∈
        (semigroupSubgroup (a.semidirectLift b hcomm)
          (zeroCharacterSemigroup S)).carrier T :=
    range_inr_le_semigroupSubgroup_semidirect a b hcomm hS
      (zeroCharacterSemigroup S) rfl T ⟨q, rfl⟩
  have hx' :
      x ≫ a.semidirectInl.hom.hom ∈
        (semigroupSubgroup (a.semidirectLift b hcomm) A).carrier T :=
    semigroupSubgroup_map_le a.semidirectInl a.isClosedSubgroup_semidirectInl
      b (a.semidirectLift b hcomm)
      (fun _ s g => (a.semidirectLift_inl b hcomm s g).symm) A T ⟨x, hx, rfl⟩
  have hc := semigroupCommutator k a.semidirectProduct inferInstance inferInstance
    S hS (a.semidirectLift b hcomm) (zeroCharacterSemigroup S) A T
    (q ≫ a.semidirectInr.hom.hom) (x ≫ a.semidirectInl.hom.hom) hq hx'
  rw [semigroupSum_zeroCharacterSemigroup] at hc
  have hm := ((semigroupSubgroup (a.semidirectLift b hcomm) A).carrier T).mul_mem hc hx'
  have hg :
      a.act q x ≫ a.semidirectInl.hom.hom ∈
        (semigroupSubgroup (a.semidirectLift b hcomm) A).carrier T := by
    rw [← a.semidirect_conjugation, AutomorphicAction.conjugation_act]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
  have he := hcomap A
  rw [← he]
  exact hg

/-- The original full-intersection API supplies the local equalities to
inner stability. -/
theorem semigroupSubgroup_isStable_inner
    (hinter : SemigroupIntersectionStatement.{u})
    (A : AddSubsemigroup (characterLattice S)) :
    a.IsStable (semigroupSubgroup b A) := by
  exact semigroupSubgroup_isStable_inner_of_comap a b hcomm hS
    (semigroupSubgroup_semidirect_comap_inl a b hcomm hS hinter) A

omit [Smooth K.X.hom] [Smooth G.X.hom]
  [ConnectedSpace K.X.left] [ConnectedSpace G.X.left] hS in
/-- The weights of the normal factor occur among the actual ambient weights. -/
theorem actionWeightSupport_normal_subset_semidirect :
    actionWeightSupport b ⊤ ⊆ actionWeightSupport (a.semidirectLift b hcomm) ⊤ := by
  rw [← actionWeightSupport_map a.semidirectInl inferInstance b
    (a.semidirectLift b hcomm)
    (fun _ s g => (a.semidirectLift_inl b hcomm s g).symm) ⊤]
  exact actionWeightSupport_subset_top _ _

omit [Smooth K.X.hom] [Smooth G.X.hom]
  [ConnectedSpace K.X.left] [ConnectedSpace G.X.left] hS in
/-- The weights of the trivially acted-on acting factor also occur in the
actual ambient support. -/
theorem actionWeightSupport_acting_subset_semidirect :
    actionWeightSupport (AutomorphicAction.trivial S.toGrp K) ⊤ ⊆
      actionWeightSupport (a.semidirectLift b hcomm) ⊤ := by
  rw [← actionWeightSupport_map a.semidirectInr inferInstance
    (AutomorphicAction.trivial S.toGrp K) (a.semidirectLift b hcomm)
    (fun _ s q => by
      rw [AutomorphicAction.trivial_act, AutomorphicAction.semidirectLift_inr]) ⊤]
  exact actionWeightSupport_subset_top _ _

end Langlands.GroupScheme.RelativeRoot
