import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Langlands.GroupScheme.Rational.SemigroupClosure

/-! # Ambient weight support and cyclic-tail commutators -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Two semigroups agree on the weights that occur in the ambient action. -/
def AgreeOnAmbientWeights (b : AutomorphicAction S.toGrp G)
    (A A' : AddSubsemigroup (characterLattice S)) : Prop :=
  ∀ χ ∈ actionWeightSupport b ⊤, χ ∈ A ↔ χ ∈ A'

/-- Every subgroup's weights lie in the ambient weight support. -/
theorem actionWeightSupport_subset_top (b : AutomorphicAction S.toGrp G)
    (F : SubgroupFunctor G) :
    actionWeightSupport b F ⊆ actionWeightSupport b ⊤ :=
  actionWeightSupport_mono b (fun _ _ _ => Subgroup.mem_top _)

/-- An ambient action weight occurs precisely when its weight space is nonzero. -/
theorem mem_actionWeightSupport_top_iff (b : AutomorphicAction S.toGrp G)
    (χ : characterLattice S) :
    χ ∈ actionWeightSupport b ⊤ ↔ actionWeightSpace b χ ≠ ⊥ := by
  constructor
  · rintro ⟨X, hX, hW, _⟩
    exact (Submodule.ne_bot_iff _).mpr ⟨X, hW, hX⟩
  · intro h
    obtain ⟨X, hW, hX⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact ⟨X, hX, hW, Subgroup.mem_top _⟩

/-- Only semigroup membership on ambient weights affects the admissible generators. -/
theorem isSemigroupGenerator_iff_of_weightSupport (b : AutomorphicAction S.toGrp G)
    {A A' : AddSubsemigroup (characterLattice S)}
    (h : AgreeOnAmbientWeights b A A')
    (F : SubgroupFunctor G) :
    IsSemigroupGenerator b A F ↔ IsSemigroupGenerator b A' F := by
  constructor
  · rintro ⟨hF, hs, hw⟩
    refine ⟨hF, hs, fun χ hχ => ?_⟩
    exact (h χ (actionWeightSupport_subset_top b F hχ)).mp (hw hχ)
  · rintro ⟨hF, hs, hw⟩
    refine ⟨hF, hs, fun χ hχ => ?_⟩
    exact (h χ (actionWeightSupport_subset_top b F hχ)).mpr (hw hχ)

/-- Semigroups selecting the same ambient weights generate the same all-test subgroup. -/
theorem semigroupSubgroup_eq_of_weightSupport (b : AutomorphicAction S.toGrp G)
    {A A' : AddSubsemigroup (characterLattice S)}
    (h : AgreeOnAmbientWeights b A A') :
    semigroupSubgroup b A = semigroupSubgroup b A' := by
  apply SubgroupFunctor.ext
  intro T
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext x
  constructor
  · rintro ⟨F, hF, hx⟩
    exact ⟨F, (isSemigroupGenerator_iff_of_weightSupport b h F).mp hF, hx⟩
  · rintro ⟨F, hF, hx⟩
    exact ⟨F, (isSemigroupGenerator_iff_of_weightSupport b h F).mpr hF, hx⟩

/-- The weight span also depends only on the selected ambient weights. -/
theorem semigroupWeightSpan_eq_of_weightSupport (b : AutomorphicAction S.toGrp G)
    {A A' : AddSubsemigroup (characterLattice S)}
    (h : AgreeOnAmbientWeights b A A') :
    semigroupWeightSpan b A = semigroupWeightSpan b A' := by
  have hle : ∀ (C D : AddSubsemigroup (characterLattice S)),
      (∀ χ ∈ actionWeightSupport b ⊤, χ ∈ C → χ ∈ D) →
      semigroupWeightSpan b C ≤ semigroupWeightSpan b D := by
    intro C D hCD
    apply iSup_le
    intro χ
    by_cases hχ : actionWeightSpace b χ.val = ⊥
    · rw [hχ]
      exact bot_le
    · exact le_iSup_of_le
        (⟨χ.val, hCD χ.val ((mem_actionWeightSupport_top_iff b χ.val).mpr hχ) χ.property⟩ : D)
        le_rfl
  exact le_antisymm (hle A A' (fun χ hχ => (h χ hχ).mp))
    (hle A' A (fun χ hχ => (h χ hχ).mpr))

/-- Sums of two positive cyclic tails lie in the tail indexed by the sum. -/
theorem semigroupSum_cyclicTail_le (a : characterLattice S) (r s : ℕ) :
    semigroupSum (cyclicTail a r) (cyclicTail a s) ≤ cyclicTail a (r + s) := by
  rintro χ ⟨α, ⟨n, hn, hn0, rfl⟩, β, ⟨m, hm, hm0, rfl⟩, rfl⟩
  exact ⟨n + m, by omega, by omega, add_nsmul a n m⟩

/-- The cyclic semigroup of the doubled character lies in the second tail. -/
theorem cyclicTail_double_le (a : characterLattice S) :
    cyclicTail (2 • a) 1 ≤ cyclicTail a 2 := by
  rintro χ ⟨n, hn, hn0, rfl⟩
  exact ⟨n * 2, by omega, by omega, by rw [mul_comm, mul_nsmul]⟩

/-- If higher positive multiples have no ambient weight, the second tail
equals the first tail of the doubled character on every test. -/
theorem weightFiltration_two_eq_double (b : AutomorphicAction S.toGrp G)
    (a : characterLattice S)
    (h : ∀ n : ℕ, 3 ≤ n → n • a ∉ actionWeightSupport b ⊤) :
    weightFiltration b a 2 = weightFiltration b (2 • a) 1 := by
  apply semigroupSubgroup_eq_of_weightSupport
  intro χ hχ
  constructor
  · rintro ⟨n, hn, hn0, rfl⟩
    have hn2 : n = 2 := by
      by_contra hn2
      exact h n (by omega) hχ
    subst n
    exact ⟨1, le_rfl, by omega, one_nsmul _⟩
  · intro hm
    exact cyclicTail_double_le a hm

/-- The source semigroup commutator bound specializes to addition of tail indices. -/
theorem weightFiltration_commutator_mem
    (hcomm : SemigroupCommutatorStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (a : characterLattice S) (r s : ℕ)
    (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X)
    (hx : x ∈ (weightFiltration b a r).carrier T)
    (hy : y ∈ (weightFiltration b a s).carrier T) :
    x * y * x⁻¹ * y⁻¹ ∈ (weightFiltration b a (r + s)).carrier T :=
  semigroupSubgroup_mono b (semigroupSum_cyclicTail_le a r s) T
    (hcomm k G hG inferInstance S hS b (cyclicTail a r) (cyclicTail a s) T x y hx hy)

/-- Vanishing of the commutator tail gives commutation on every test scheme. -/
theorem commute_of_weightFiltration_eq_bot
    (hcomm : SemigroupCommutatorStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (a : characterLattice S) (r s : ℕ)
    (hbot : weightFiltration b a (r + s) = ⊥)
    (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X)
    (hx : x ∈ (weightFiltration b a r).carrier T)
    (hy : y ∈ (weightFiltration b a s).carrier T) : Commute x y := by
  have hm := weightFiltration_commutator_mem hcomm hG hS b a r s T x y hx hy
  rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hm
  change x * y = y * x
  exact (mul_inv_eq_iff_eq_mul).mp (mul_inv_eq_one.mp hm)

end Langlands.GroupScheme.RelativeRoot
