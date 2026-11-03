import Langlands.GroupScheme.Rational.WeightSemigroup

/-! # Closure properties of actual semigroup subgroup functors -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The generated subgroup is the least all-test subgroup containing every
admissible generator. No representability is needed for this universal property. -/
theorem semigroupSubgroup_le_iff (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) (F : SubgroupFunctor G) :
    semigroupSubgroup b A ≤ F ↔
      ∀ F' : SubgroupFunctor G, IsSemigroupGenerator b A F' → F' ≤ F := by
  constructor
  · intro h F' hF'
    exact (generator_le_semigroupSubgroup b A F' hF').trans h
  · intro h T x hx
    apply (Subgroup.closure_le (F.carrier T)).2 ?_ hx
    rintro y ⟨F', hF', hy⟩
    exact h F' hF' T hy

/-- Each actual point action preserves the closure of the admissible subgroups. -/
theorem semigroupSubgroup_isStable (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) :
    b.IsStable (semigroupSubgroup b A) := by
  intro T s g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨F, hF, hx⟩ := hx
    exact Subgroup.subset_closure ⟨F, hF, hF.2.1 T s x hx⟩
  | one =>
    rw [b.act_one]
    exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    rw [b.act_mul_right]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [b.act_inv]
    exact Subgroup.inv_mem _ hx

/-- Stability is an equivalence on membership, since every point action has an
inverse point action. This applies to every test scheme. -/
theorem act_mem_semigroupSubgroup_iff (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S))
    (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (g : T ⟶ G.X) :
    b.act s g ∈ (semigroupSubgroup b A).carrier T ↔
      g ∈ (semigroupSubgroup b A).carrier T := by
  constructor
  · intro h
    have h' := semigroupSubgroup_isStable b A T s⁻¹ (b.act s g) h
    simpa only [b.act_inv_act] using h'
  · exact semigroupSubgroup_isStable b A T s g

/-- Tangent weight support is monotone under actual subgroup inclusion. -/
theorem actionWeightSupport_mono (b : AutomorphicAction S.toGrp G)
    {F F' : SubgroupFunctor G} (h : F ≤ F') :
    actionWeightSupport b F ⊆ actionWeightSupport b F' := by
  rintro χ ⟨X, hX, hw, hF⟩
  exact ⟨X, hX, hw, h _ hF⟩

/-- Once the generated subgroup has the required support bound, its
maximality equivalence follows from its definition and support monotonicity. -/
theorem semigroupSubgroup_maximality_of_support (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S))
    (hA : actionWeightSupport b (semigroupSubgroup b A) ⊆ A)
    (F : SubgroupFunctor G) (hF : IsSmoothConnectedClosed F) (hstable : b.IsStable F) :
    actionWeightSupport b F ⊆ A ↔ F ≤ semigroupSubgroup b A := by
  constructor
  · intro hsupport
    exact generator_le_semigroupSubgroup b A F ⟨hF, hstable, hsupport⟩
  · intro h χ hχ
    exact hA (actionWeightSupport_mono b h hχ)

/-- Any admissible subgroup containing all the admissible subgroups is exactly
the generated functor, on all tests. -/
theorem semigroupSubgroup_eq_of_maximal_generator (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S))
    (F : SubgroupFunctor G) (hF : IsSemigroupGenerator b A F)
    (hmax : ∀ F' : SubgroupFunctor G, IsSemigroupGenerator b A F' → F' ≤ F) :
    semigroupSubgroup b A = F := by
  apply le_antisymm
  · exact (semigroupSubgroup_le_iff b A F).2 hmax
  · exact generator_le_semigroupSubgroup b A F hF

/-- The span of the selected action weight spaces is monotone in the semigroup. -/
theorem semigroupWeightSpan_mono (b : AutomorphicAction S.toGrp G)
    {A A' : AddSubsemigroup (characterLattice S)} (h : A ≤ A') :
    semigroupWeightSpan b A ≤ semigroupWeightSpan b A' := by
  apply iSup_le
  intro χ
  exact le_iSup_of_le (⟨χ.val, h χ.property⟩ : A') le_rfl

/-- The actual semigroup subgroup construction as an order homomorphism. -/
def semigroupSubgroupOrderHom (b : AutomorphicAction S.toGrp G) :
    AddSubsemigroup (characterLattice S) →o SubgroupFunctor G where
  toFun := semigroupSubgroup b
  monotone' := fun _ _ h => semigroupSubgroup_mono b h

@[simp] theorem semigroupSubgroupOrderHom_apply (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) :
    semigroupSubgroupOrderHom b A = semigroupSubgroup b A := rfl

end Langlands.GroupScheme.RelativeRoot
