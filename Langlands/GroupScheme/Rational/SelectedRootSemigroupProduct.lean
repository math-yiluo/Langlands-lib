import Langlands.GroupScheme.Rational.RootRayFromFactorPairs
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction

/-! # Ordered actual root products for selected character semigroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- The actual roots in a semigroup which are not higher positive integral
multiples of another actual root in the same semigroup. -/
def semigroupIndivisibleRoots (i : T.toGrp ⟶ G)
    (A : AddSubsemigroup (characterLattice T)) : Set (characterLattice T) :=
  {a | a ∈ relativeRoots i ∧ a ∈ A ∧
    ∀ b ∈ relativeRoots i, b ∈ A → ∀ m : ℕ, 1 < m → m • b ≠ a}

/-- A character in an additive semigroup brings its entire positive cyclic
tail into that semigroup. -/
theorem cyclicTail_one_le_of_mem
    {A : AddSubsemigroup (characterLattice T)}
    {a : characterLattice T} (ha : a ∈ A) : cyclicTail a 1 ≤ A := by
  have hmem : ∀ n : ℕ, 0 < n → n • a ∈ A := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        intro hn
        by_cases hn0 : n = 0
        · subst n
          simpa using ha
        · simpa only [succ_nsmul] using A.add_mem (ih (by omega)) ha
  rintro χ ⟨n, _, hn, rfl⟩
  exact hmem n hn

section Pairs

variable [Smooth G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    (A : AddSubsemigroup (characterLattice T))

include hT hE

/-- Every selected actual root is on the positive integral ray of a root
indivisible within the selected roots. Opposite pairs bound every division by two. -/
theorem exists_semigroupIndivisibleRoot_ray
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i) (hχA : χ ∈ A) :
    ∃ a ∈ semigroupIndivisibleRoots i A, χ ∈ cyclicTail a 1 := by
  classical
  by_cases hmin : χ ∈ semigroupIndivisibleRoots i A
  · exact ⟨χ, hmin, self_mem_cyclicTail_one χ⟩
  · obtain ⟨b, hb, hbA, m, hm, hmb⟩ :
        ∃ b ∈ relativeRoots i, b ∈ A ∧ ∃ m : ℕ, 1 < m ∧ m • b = χ := by
      simpa only [semigroupIndivisibleRoots, Set.mem_ofPred_eq, hχ, hχA,
        true_and, not_forall, not_not, exists_prop] using hmin
    have hm2 : m = 2 := by
      rcases hE.eq_one_or_two_of_nsmul_mem i hT (hmb.symm ▸ hχ) with h | h
      · omega
      · exact h
    subst m
    have hbmin : b ∈ semigroupIndivisibleRoots i A := by
      refine ⟨hb, hbA, ?_⟩
      intro c hc hcA n hn hnc
      have hmul : (2 * n) • c ∈ relativeRoots i := by
        rw [← smul_smul, hnc, hmb]
        exact hχ
      rcases hE.eq_one_or_two_of_nsmul_mem i hT hmul with h | h <;> omega
    exact ⟨b, hbmin, 2, by omega, by omega, hmb⟩

/-- Distinct roots indivisible within one selected semigroup have disjoint
positive integral rays. No full relative-root-system realization is needed. -/
theorem disjoint_cyclicTail_semigroupIndivisibleRoots
    {a b : characterLattice T} (ha : a ∈ semigroupIndivisibleRoots i A)
    (hb : b ∈ semigroupIndivisibleRoots i A) (hne : a ≠ b) :
    Disjoint (cyclicTail a 1 : Set (characterLattice T))
      (cyclicTail b 1 : Set (characterLattice T)) := by
  apply Set.disjoint_left.mpr
  rintro χ ⟨m, _, hm, hma⟩ ⟨n, _, hn, hnb⟩
  rcases hE.root_eq_or_twice_of_common_positive_multiple i hT
      ha.1 hb.1 hm hn (hma.trans hnb.symm) with heq | heq | heq
  · exact hne heq
  · exact ha.2.2 b hb.1 hb.2.1 2 (by omega) heq.symm
  · exact hb.2.2 a ha.1 ha.2.1 2 (by omega) heq.symm

/-- The actual root-ray blocks indexed by all selected indivisible roots
cover exactly the selected actual roots. -/
theorem iUnion_rootRayBlock_semigroup
    {n : ℕ} (a : Fin n → characterLattice T)
    (ha : Set.range a = semigroupIndivisibleRoots i A) :
    (⋃ r, rootRayBlock i (a r)) = relativeRoots i ∩ (A : Set _) := by
  ext χ
  constructor
  · intro hχ
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hχ
    have har : a r ∈ semigroupIndivisibleRoots i A := ha ▸ Set.mem_range_self r
    exact ⟨hr.1, cyclicTail_one_le_of_mem har.2.1 hr.2⟩
  · rintro ⟨hχ, hχA⟩
    obtain ⟨b, hb, hχb⟩ := exists_semigroupIndivisibleRoot_ray i hT hE A hχ hχA
    obtain ⟨r, rfl⟩ := ha.symm ▸ hb
    exact Set.mem_iUnion.mpr ⟨r, hχ, hχb⟩

/-- The selected ray blocks satisfy the exact disjointness and cross-exclusion
conditions of the ordered semigroup-product theorem. -/
theorem rootRayBlock_semigroup_pairwise
    {n : ℕ} (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (ha : Set.range a = semigroupIndivisibleRoots i A) :
    (∀ r q : Fin n, r ≠ q → Disjoint (rootRayBlock i (a r)) (rootRayBlock i (a q))) ∧
    (∀ r q : Fin n, r ≠ q → Disjoint (rootRayBlock i (a r))
      (AddSubsemigroup.closure (rootRayBlock i (a q)) : Set (characterLattice T))) := by
  have hmem (r : Fin n) : a r ∈ semigroupIndivisibleRoots i A :=
    ha ▸ Set.mem_range_self r
  have htail (r q : Fin n) (hrq : r ≠ q) :
      Disjoint (cyclicTail (a r) 1 : Set (characterLattice T))
        (cyclicTail (a q) 1 : Set (characterLattice T)) :=
    disjoint_cyclicTail_semigroupIndivisibleRoots i hT hE A
      (hmem r) (hmem q) (fun h => hrq (hinj h))
  constructor
  · intro r q hrq
    exact (htail r q hrq).mono (fun _ h => h.2) (fun _ h => h.2)
  · intro r q hrq
    rw [closure_rootRayBlock i (hmem q).1]
    exact (htail r q hrq).mono_left (fun _ h => h.2)

end Pairs

section Support

variable [Smooth G.X.hom]

/-- When zero is excluded, the selected subgroup has precisely the selected
actual roots as its full larger-torus action support. -/
theorem actionWeightSupport_semigroupSubgroup_eq_roots_inter
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (A : AddSubsemigroup (characterLattice T)) (hzero : 0 ∉ A) :
    actionWeightSupport (AutomorphicAction.conjugation i)
        (semigroupSubgroup (AutomorphicAction.conjugation i) A) =
      relativeRoots i ∩ (A : Set _) := by
  rw [actionWeightSupport_semigroupSubgroup semigroupRealization
    (inferInstance : Smooth G.X.hom) hT, actionWeightSupport_top]
  ext χ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, actionWeightSpace_conjugation]
  constructor
  · rintro ⟨hχ, hχA⟩
    exact ⟨⟨fun h => hzero (h ▸ hχA), hχ⟩, hχA⟩
  · rintro ⟨hχ, hχA⟩
    exact ⟨hχ.2, hχA⟩

end Support

section Product

variable [Smooth G.X.hom]

/-- An enumeration of the roots indivisible within the selected roots exists
using only finiteness of the split-torus Lie support. -/
theorem exists_semigroupIndivisibleRoots_enumeration
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (A : AddSubsemigroup (characterLattice T)) :
    ∃ (n : ℕ) (a : Fin n → characterLattice T), Function.Injective a ∧
      Set.range a = semigroupIndivisibleRoots i A :=
  ((hT.finite_relativeRoots i).subset (fun _ h => h.1)).fin_param

/-- The actual subgroup selected by a zero-excluding character semigroup is
an ordered scheme product of the actual root groups on its selected minimal
rays. The upper opposite-factor-pair premise is retained explicitly. -/
theorem semigroup_orderedRootProduct
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) (hE : HasOppositeFactorPairs i)
    (A : AddSubsemigroup (characterLattice T)) (hzero : 0 ∉ A)
    {n : ℕ} (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (ha : Set.range a = semigroupIndivisibleRoots i A) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (jU : U ⟶ G)
      (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ G)
      (e : (∏ᶜ H).X ≅ U.X),
      (semigroupSubgroup (AutomorphicAction.conjugation i) A).IsRepresentedBy jU ∧
      IsClosedSubgroup jU ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
      IsUnipotent U ∧ IsSplitUnipotent U ∧
      (∀ r, (subgroup i (a r)).IsRepresentedBy (j r) ∧
        IsClosedSubgroup (j r) ∧ Smooth (H r).X.hom ∧
        ConnectedSpace (H r).X.left ∧ IsUnipotent (H r) ∧ IsSplitUnipotent (H r)) ∧
      e.hom ≫ jU.hom.hom = orderedMultiplication j := by
  let b := AutomorphicAction.conjugation i
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k G inferInstance inferInstance T hT b A
  obtain ⟨hUu, hUsp⟩ := hUnip U jU hjU hzero
  let : IsAffineHom U.X.hom := hjUc.isAffineHom
  let : Smooth U.X.hom := hUs
  let : ConnectedSpace U.X.left := hUc
  let c := b.onRepresentedSubgroup jU hjU hStable
  have hequiv : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.X)
      (x : V ⟶ U.X), c.act t x ≫ jU.hom.hom = b.act t (x ≫ jU.hom.hom) :=
    fun _ t x => b.onRepresentedSubgroup_act_comp jU hjU hStable t x
  have htop : (⊤ : SubgroupFunctor U).map jU = semigroupSubgroup b A := by
    rw [SubgroupFunctor.map_top, hjU.2]
  have hsupport : actionWeightSupport c ⊤ = relativeRoots i ∩ (A : Set _) := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_semigroupSubgroup_eq_roots_inter hT i A hzero
  have hblocks := rootRayBlock_semigroup_pairwise i hT hE A a hinj ha
  have hcover : (⋃ r, rootRayBlock i (a r)) = actionWeightSupport c ⊤ :=
    (iUnion_rootRayBlock_semigroup i hT hE A a ha).trans hsupport.symm
  obtain ⟨H, jH, hH, hIso⟩ :=
    hasOrderedSemigroupProducts_of_unipotent c hT hUu n
      (fun r => rootRayBlock i (a r)) hcover hblocks.1 hblocks.2
  have hroot (r : Fin n) : a r ∈ semigroupIndivisibleRoots i A :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      (semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).map jU =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock i (hroot r).1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_of_mem (hroot r).2.1)
  have hfactor (r : Fin n) :
      (subgroup i (a r)).IsRepresentedBy (jH r ≫ jU) ∧
        IsClosedSubgroup (jH r ≫ jU) ∧ Smooth (H r).X.hom ∧
        ConnectedSpace (H r).X.left ∧ IsUnipotent (H r) ∧ IsSplitUnipotent (H r) := by
    have hrep : (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy
        (jH r ≫ jU) := by
      rw [← hsemigroup r]
      exact (hH r).1.comp hjU
    have hcyclic : semigroupSubgroup b (cyclicTail (a r) 1) = subgroup i (a r) :=
      weightFiltration_one_eq_subgroup hT i (a r) (hroot r).1.1
    obtain ⟨hHu, hHsp⟩ := (semigroupRealization k G inferInstance inferInstance T hT b
      (cyclicTail (a r) 1)).2.2.2.1 (H r) (jH r ≫ jU) hrep (fun hz =>
        hzero (cyclicTail_one_le_of_mem (hroot r).2.1 hz))
    exact ⟨hcyclic ▸ hrep, (hH r).2.1.comp hjUc, (hH r).2.2.1,
      (hH r).2.2.2, hHu, hHsp⟩
  let := hIso
  exact ⟨U, jU, H, (fun r => jH r ≫ jU), asIso (orderedMultiplication jH),
    hjU, hjUc, hUs, hUc, hUu, hUsp, hfactor, orderedMultiplication_comp jH jU⟩

end Product

end Langlands.GroupScheme.RelativeRoot
