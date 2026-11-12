import Langlands.Representation.Hecke.RenardTestDecompositionStatements

/-! # Proof of Renard II.3.5 finite test-function expansions -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe uG uX

namespace Langlands.Hecke.RenardTestDecomposition

open Langlands.HarmonicAnalysis

/-- A compactly supported function constant on the cells of an open partition
has a finite expansion using precisely its nonzero cells. -/
private theorem finitePartitionExpansion {X : Type uX} [TopologicalSpace X]
    (f : X → ℂ) (hf : IsCompact (Function.support f))
    (C : X → Set X) (hself : ∀ x, x ∈ C x)
    (hcell : ∀ x y, y ∈ C x → C y = C x)
    (hopen : ∀ x, IsOpen (C x))
    (hconst : ∀ x y, y ∈ C x → f y = f x) :
    ∃ (n : ℕ) (g : Fin n → X) (c : Fin n → ℂ),
      (∀ i, c i ≠ 0) ∧
      Pairwise (fun i j => Disjoint (C (g i)) (C (g j))) ∧
      Function.support f = ⋃ i, C (g i) ∧
      ∀ x, f x = ∑ i, c i * (C (g i)).indicator (fun _ => 1) x := by
  classical
  obtain ⟨t, ht⟩ := hf.elim_finite_subcover C hopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hself x⟩)
  have hfinite : (C '' Function.support f).Finite := by
    apply (t.finite_toSet.image C).subset
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact ⟨y, hy, (hcell y x hxy).symm⟩
  let I := C '' Function.support f
  let : Fintype I := hfinite.fintype
  choose r hr hCr using fun i : I => i.property
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let g : Fin (Fintype.card I) → X := fun i => r (e i)
  have hg (i) : C (g i) = (e i).val := hCr (e i)
  have hc (i) : f (g i) ≠ 0 := hr (e i)
  have hdis : Pairwise (fun i j => Disjoint (C (g i)) (C (g j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    apply hij
    apply e.injective
    apply Subtype.ext
    exact (hg i).symm.trans
      (((hcell (g i) x hxi).symm.trans (hcell (g j) x hxj)).trans (hg j))
  have hsupp : Function.support f = ⋃ i, C (g i) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      let a : I := ⟨C x, x, hx, rfl⟩
      refine ⟨e.symm a, ?_⟩
      rw [hg, e.apply_symm_apply]
      exact hself x
    · rintro ⟨i, hxi⟩
      change f x ≠ 0
      rw [hconst (g i) x hxi]
      exact hc i
  refine ⟨Fintype.card I, g, fun i => f (g i), hc, hdis, hsupp, ?_⟩
  intro x
  by_cases hx : x ∈ Function.support f
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hsupp ▸ hx)
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem hxi, mul_one, hconst (g i) x hxi]
    · intro j _ hji
      rw [Set.indicator_of_notMem, mul_zero]
      intro hxj
      exact Set.disjoint_left.mp (hdis hji) hxj hxi
    · simp
  · have hfx : f x = 0 := not_ne_iff.mp hx
    rw [hfx]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [Set.indicator_of_notMem, mul_zero]
    intro hxi
    exact hx (hsupp.symm ▸ Set.mem_iUnion.mpr ⟨i, hxi⟩)

/-- The double-coset expansion with the original unnormalized indicators. -/
theorem doubleCosetExpansion : DoubleCosetExpansionStatement.{uG} := by
  classical
  intro G _ _ _ _ _ _ f
  obtain ⟨K, _, hK, hf⟩ :=
    TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hbi := hf f (by simp)
  obtain ⟨n, g, c, _, hdis, _, hexp⟩ := finitePartitionExpansion
    (f : G → ℂ) (TestFunction.isCompact_support f)
    (TestFunction.doubleCosetSet K)
    (DoubleCoset.mem_doubleCoset_self K.toSubgroup K.toSubgroup)
    (fun _ _ h => TestFunction.doubleCosetSet_eq_of_mem K h)
    (TestFunction.isOpen_doubleCosetSet K) (by
      intro y x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (TestFunction.mem_doubleCosetSet K y x).mp hx
      rw [hbi.2 ⟨b, hb⟩, hbi.1 ⟨a, ha⟩])
  refine ⟨K, hK, n, g, c, hdis, ?_⟩
  apply TestFunction.ext
  intro x
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, TestFunction.doubleCosetIndicator_apply] using hexp x

/-- Fixedness for left translations gives the exact expansion by right cosets. -/
theorem leftInvariantExpansion : LeftInvariantExpansionStatement.{uG} := by
  classical
  intro G _ _ _ _ _ _ K _ f hf
  have hleft (k : K) (x : G) : f ((k : G) * x) = f x := by
    simpa using congrArg (fun h : SchwartzBruhat G => h x) (hf k⁻¹)
  have hC (g : G) :
      DoubleCoset.doubleCoset g K.toSubgroup (⊥ : Subgroup G) =
        {x | ∃ k : K, x = (k : G) * g} := by
    ext x
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe, Subgroup.mem_bot, exists_eq_left,
      mul_one, Set.mem_ofPred_eq]
    exact ⟨fun ⟨k, hk, hx⟩ => ⟨⟨k, hk⟩, hx⟩,
      fun ⟨k, hx⟩ => ⟨k, k.property, hx⟩⟩
  obtain ⟨n, g, c, hc, hdis, hsupp, hexp⟩ := finitePartitionExpansion
    (f : G → ℂ) (TestFunction.isCompact_support f)
    (fun g => DoubleCoset.doubleCoset g K.toSubgroup (⊥ : Subgroup G))
    (DoubleCoset.mem_doubleCoset_self K.toSubgroup ⊥)
    (fun _ _ h => DoubleCoset.doubleCoset_eq_of_mem h)
    (fun _ => K.isOpen.mul_right.mul_right) (by
      intro y x hx
      rw [hC] at hx
      obtain ⟨k, rfl⟩ := hx
      exact hleft k y)
  exact ⟨n, g, c, hc, by simpa only [hC] using hdis,
    by simpa only [hC] using hsupp, by simpa only [hC] using hexp⟩

/-- Fixedness for right translations gives the exact expansion by left cosets. -/
theorem rightInvariantExpansion : RightInvariantExpansionStatement.{uG} := by
  classical
  intro G _ _ _ _ _ _ K _ f hf
  have hright (k : K) (x : G) : f (x * (k : G)) = f x :=
    congrArg (fun h : SchwartzBruhat G => h x) (hf k)
  have hC (g : G) :
      DoubleCoset.doubleCoset g (⊥ : Subgroup G) K.toSubgroup =
        {x | ∃ k : K, x = g * (k : G)} := by
    ext x
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe, Subgroup.mem_bot, exists_eq_left,
      one_mul, Set.mem_ofPred_eq]
    exact ⟨fun ⟨k, hk, hx⟩ => ⟨⟨k, hk⟩, hx⟩,
      fun ⟨k, hx⟩ => ⟨k, k.property, hx⟩⟩
  obtain ⟨n, g, c, hc, hdis, hsupp, hexp⟩ := finitePartitionExpansion
    (f : G → ℂ) (TestFunction.isCompact_support f)
    (fun g => DoubleCoset.doubleCoset g (⊥ : Subgroup G) K.toSubgroup)
    (DoubleCoset.mem_doubleCoset_self ⊥ K.toSubgroup)
    (fun _ _ h => DoubleCoset.doubleCoset_eq_of_mem h)
    (fun _ => K.isOpen.mul_left) (by
      intro y x hx
      rw [hC] at hx
      obtain ⟨k, rfl⟩ := hx
      exact hright k y)
  exact ⟨n, g, c, hc, by simpa only [hC] using hdis,
    by simpa only [hC] using hsupp, by simpa only [hC] using hexp⟩

/-- Renard II.3.5, Lemma (i) and both alternatives of (ii), at the full group universe. -/
theorem statements : Statements.{uG} :=
  ⟨doubleCosetExpansion, leftInvariantExpansion, rightInvariantExpansion⟩

end Langlands.Hecke.RenardTestDecomposition
