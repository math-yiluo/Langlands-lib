import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Mathlib.GroupTheory.Commutator.Basic

/-! # Reduction of the all-test semigroup bound to its geometric generators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme.RelativeRoot

section GroupClosure

variable {M : Type*} [Group M]

/-- A subgroup normalizes a generated subgroup if its commutators with the
generators lie in that generated subgroup. -/
theorem subgroup_le_normalizer_closure_of_commutators {H : Subgroup M} {Y : Set M}
    (hcomm : ∀ g ∈ H, ∀ z ∈ Y, ⁅g, z⁆ ∈ Subgroup.closure Y) :
    H ≤ Subgroup.normalizer (Subgroup.closure Y) := by
  have conjugates (g : M) (hg : g ∈ H) :
      Subgroup.closure Y ≤
        (Subgroup.closure Y).comap (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    have hc := (Subgroup.closure Y).mul_mem (hcomm g hg z hz)
      (Subgroup.subset_closure hz)
    change g * z * g⁻¹ ∈ Subgroup.closure Y
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hc
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro z
  constructor
  · intro hz
    exact conjugates g hg hz
  · intro hz
    have hc := conjugates g⁻¹ (H.inv_mem hg) hz
    change g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ ∈ Subgroup.closure Y at hc
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc

/-- Extend a commutator bound from two generating sets when both generated
subgroups normalize the target. -/
theorem commutator_closure_le_of_normalizes {X Y : Set M} {K : Subgroup M}
    (hX : Subgroup.closure X ≤ Subgroup.normalizer K)
    (hY : Subgroup.closure Y ≤ Subgroup.normalizer K)
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ K) :
    ⁅Subgroup.closure X, Subgroup.closure Y⁆ ≤ K := by
  have conjX (x : M) (hx : x ∈ Subgroup.closure X) (z : M) (hz : z ∈ K) :
      x * z * x⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hX hx) z).mp hz
  have conjY (y : M) (hy : y ∈ Subgroup.closure Y) (z : M) (hz : z ∈ K) :
      y * z * y⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hY hy) z).mp hz
  apply Subgroup.commutator_le.mpr
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy => exact hcomm x hx y hy
      | one => simp
      | mul y z hy hz ihy ihz =>
          rw [commutatorElement_mul_right_eq_mul_conj]
          simpa only [mul_assoc] using K.mul_mem ihy (conjY y hy _ ihz)
      | inv y hy ihy =>
          rw [commutatorElement_inv_right, ← commutatorElement_inv x y]
          simpa only [inv_inv] using
            conjY y⁻¹ ((Subgroup.closure Y).inv_mem hy) _ (K.inv_mem ihy)
  | one =>
      intro y _
      simp
  | mul x z hx hz ihx ihz =>
      intro y hy
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact K.mul_mem (conjX x hx _ (ihz y hy)) (ihx y hy)
  | inv x hx ihx =>
      intro y hy
      rw [commutatorElement_inv_left, ← commutatorElement_inv x y]
      simpa only [inv_inv] using
        conjX x⁻¹ ((Subgroup.closure X).inv_mem hx) _ (K.inv_mem (ihx y hy))

end GroupClosure

section Semigroups

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The geometric input restricted to individual admissible subgroup functors.
It retains every additive subsemigroup and every test scheme. -/
def SemigroupGeneratorCommutatorBound (b : AutomorphicAction S.toGrp G) : Prop :=
  ∀ (A A' : AddSubsemigroup (characterLattice S))
    (F F' : SubgroupFunctor G),
    IsSemigroupGenerator b A F → IsSemigroupGenerator b A' F' →
    ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X),
      x ∈ F.carrier T → y ∈ F'.carrier T →
      x * y * x⁻¹ * y⁻¹ ∈ (semigroupSubgroup b (semigroupSum A A')).carrier T

/-- Adding a further A-weight to A+A' stays in A+A'; no zero is inserted. -/
theorem semigroupSum_left_absorbs (A A' : AddSubsemigroup (characterLattice S)) :
    semigroupSum A (semigroupSum A A') ≤ semigroupSum A A' := by
  rintro χ ⟨α, hα, _, ⟨β, hβ, γ, hγ, rfl⟩, rfl⟩
  exact ⟨α + β, A.add_mem hα hβ, γ, hγ, add_assoc α β γ⟩

/-- Adding a further A'-weight to A+A' stays in A+A'. -/
theorem semigroupSum_right_absorbs (A A' : AddSubsemigroup (characterLattice S)) :
    semigroupSum A' (semigroupSum A A') ≤ semigroupSum A A' := by
  rintro χ ⟨α, hα, _, ⟨β, hβ, γ, hγ, rfl⟩, rfl⟩
  exact ⟨β, hβ, α + γ, A'.add_mem hα hγ, add_left_comm β α γ⟩

/-- The generator bound yields normalization whenever A+B is contained in B.
The proof first extends conjugation across the B-closure, then the A-closure. -/
theorem semigroupSubgroup_normalized_of_generatorBound
    (b : AutomorphicAction S.toGrp G) (hcomm : SemigroupGeneratorCommutatorBound b)
    {A B : AddSubsemigroup (characterLattice S)} (hAB : semigroupSum A B ≤ B) :
    (semigroupSubgroup b B).IsNormalizedBy (semigroupSubgroup b A) := by
  intro T x y hx hy
  have hnorm :
      (semigroupSubgroup b A).carrier T ≤
        Subgroup.normalizer ((semigroupSubgroup b B).carrier T) := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨F, hF, hz⟩
    apply subgroup_le_normalizer_closure_of_commutators (H := F.carrier T) ?_ hz
    rintro g hg z ⟨F', hF', hz⟩
    exact semigroupSubgroup_mono b hAB T (hcomm A B F F' hF hF' T g z hg hz)
  exact (Subgroup.mem_normalizer_iff.mp (hnorm hx) y).mp hy

/-- The full all-test commutator bound follows from the geometric generator
bound, with normalization supplied by absorption of literal semigroup sums. -/
theorem semigroupSubgroup_commutator_of_generatorBound
    (b : AutomorphicAction S.toGrp G) (hcomm : SemigroupGeneratorCommutatorBound b)
    (A A' : AddSubsemigroup (characterLattice S))
    (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X)
    (hx : x ∈ (semigroupSubgroup b A).carrier T)
    (hy : y ∈ (semigroupSubgroup b A').carrier T) :
    x * y * x⁻¹ * y⁻¹ ∈ (semigroupSubgroup b (semigroupSum A A')).carrier T := by
  have hnorm (B : AddSubsemigroup (characterLattice S))
      (hB : semigroupSum B (semigroupSum A A') ≤ semigroupSum A A') :
      (semigroupSubgroup b B).carrier T ≤
        Subgroup.normalizer ((semigroupSubgroup b (semigroupSum A A')).carrier T) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro g hg z hz
    exact semigroupSubgroup_normalized_of_generatorBound b hcomm hB T g z hg hz
  have hc := commutator_closure_le_of_normalizes
    (hnorm A (semigroupSum_left_absorbs A A'))
    (hnorm A' (semigroupSum_right_absorbs A A')) (by
      rintro g ⟨F, hF, hg⟩ z ⟨F', hF', hz⟩
      exact hcomm A A' F F' hF hF' T g z hg hz)
  exact hc (Subgroup.commutator_mem_commutator hx hy)

/-- Restricting the full bound to individual generators loses no information. -/
theorem generatorCommutatorBound_iff (b : AutomorphicAction S.toGrp G) :
    SemigroupGeneratorCommutatorBound b ↔
      ∀ (A A' : AddSubsemigroup (characterLattice S))
        (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X),
        x ∈ (semigroupSubgroup b A).carrier T →
        y ∈ (semigroupSubgroup b A').carrier T →
        x * y * x⁻¹ * y⁻¹ ∈ (semigroupSubgroup b (semigroupSum A A')).carrier T := by
  constructor
  · exact semigroupSubgroup_commutator_of_generatorBound b
  · intro h A A' F F' hF hF' T x y hx hy
    exact h A A' T x y (generator_le_semigroupSubgroup b A F hF T hx)
      (generator_le_semigroupSubgroup b A' F' hF' T hy)

end Semigroups

end Langlands.GroupScheme.RelativeRoot
