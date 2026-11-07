import Langlands.Algebra.OrderedPrefix
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # Independence of roots transformed by ordered reflection prefixes -/

noncomputable section

namespace Langlands.LinearAlgebra

section Linear

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Transform each direction by the product of the preceding automorphisms. -/
def orderedReflectionWeights (r : ℕ) (a : Fin r → M) (f : Fin r → M ≃ₗ[R] M) :
    Fin r → M :=
  fun j => orderedPrefix r f j.castSucc (a j)

private theorem span_cons_shear {r : ℕ} (a : M) (v : Fin r → M)
    (f : M ≃ₗ[R] M) (l : M →ₗ[R] R) (hf : ∀ z, f z = z - l z • a) :
    Submodule.span R (Set.range (Fin.cons a (fun j => f (v j)))) =
      Submodule.span R (Set.range (Fin.cons a v)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · exact Submodule.subset_span ⟨0, rfl⟩
    · change f (v j) ∈ _
      rw [hf]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨j.succ, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · exact Submodule.subset_span ⟨0, rfl⟩
    · change v j ∈ _
      have hz : v j = f (v j) + l (v j) • a := by rw [hf]; abel
      rw [hz]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨j.succ, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))

/-- Prefix-reflected independent directions remain independent and span the same module.
The assertion is over a commutative ring, so it applies to integral root lattices. -/
theorem orderedReflectionWeights_independent_span (r : ℕ) (a : Fin r → M)
    (ha : LinearIndependent R a) (l : Fin r → M →ₗ[R] R)
    (f : Fin r → M ≃ₗ[R] M)
    (hf : ∀ j z, f j z = z - l j z • a j)
    (hself : ∀ j, f j (a j) = -a j) :
    LinearIndependent R (orderedReflectionWeights r a f) ∧
      Submodule.span R (Set.range (orderedReflectionWeights r a f)) =
        Submodule.span R (Set.range a) := by
  change LinearIndependent R (fun j => orderedPrefix r f j.castSucc (a j)) ∧
    Submodule.span R (Set.range fun j => orderedPrefix r f j.castSucc (a j)) =
      Submodule.span R (Set.range a)
  induction r with
  | zero =>
    constructor
    · exact linearIndependent_empty_type
    · simp
  | succ r ih =>
    obtain ⟨htail, hspan⟩ := ih (fun j => a j.succ)
      (ha.comp Fin.succ (Fin.succ_injective r)) (fun j => l j.succ)
      (fun j => f j.succ) (fun j => hf j.succ) (fun j => hself j.succ)
    let v : Fin r → M :=
      fun j => orderedPrefix r (fun i => f i.succ) j.castSucc (a j.succ)
    change LinearIndependent R v at htail
    change Submodule.span R (Set.range v) =
      Submodule.span R (Set.range fun j : Fin r => a j.succ) at hspan
    have hfamily :
        (fun j => orderedPrefix (r + 1) f j.castSucc (a j)) =
          Fin.cons (a 0) (fun j => f 0 (v j)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp only [← Fin.succ_castSucc, orderedPrefix_succ,
          LinearEquiv.mul_apply, Fin.cons_succ, v]
    rw [hfamily]
    constructor
    · have hcons : LinearIndependent R (Fin.cons (-a 0) v) := by
        refine LinearIndependent.finCons' _ _ htail ?_
        intro c y hy hcy
        have heq : c • a 0 = y := by
          have h := eq_neg_of_add_eq_zero_left hcy
          simpa using congrArg Neg.neg h
        apply ha.eq_zero_of_smul_mem_span 0 c
        rw [heq]
        apply Submodule.span_mono (s := Set.range fun j : Fin r => a j.succ) ?_
          (hspan ▸ hy)
        rintro _ ⟨j, rfl⟩
        exact ⟨j.succ, ⟨Set.mem_univ _, by simp⟩, rfl⟩
      have hm := hcons.map' (f 0).toLinearMap (LinearMap.ker_eq_bot.mpr (f 0).injective)
      convert hm using 1
      funext j
      refine Fin.cases ?_ (fun j => rfl) j
      simp [hself]
    · rw [span_cons_shear (a 0) v (f 0) (l 0) (hf 0)]
      rw [Fin.range_cons, Submodule.span_insert, hspan,
        ← Submodule.span_insert, ← Fin.range_cons]
      congr 2
      exact Fin.cons_self_tail a

/-- Independence alone for a finite ordered reflection family. -/
theorem orderedReflectionWeights_linearIndependent (r : ℕ) (a : Fin r → M)
    (ha : LinearIndependent R a) (l : Fin r → M →ₗ[R] R)
    (f : Fin r → M ≃ₗ[R] M)
    (hf : ∀ j z, f j z = z - l j z • a j)
    (hself : ∀ j, f j (a j) = -a j) :
    LinearIndependent R (orderedReflectionWeights r a f) :=
  (orderedReflectionWeights_independent_span r a ha l f hf hself).1

end Linear

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
    (b : P.Base) {r : ℕ} (e : Fin r ≃ b.support)

/-- The roots obtained from the simple roots by preceding simple reflections
are independent over the original coefficient ring. -/
theorem prefixSimpleRoots_linearIndependent :
    LinearIndependent R (fun j =>
      orderedPrefix r (fun i => P.reflection (e i)) j.castSucc (P.root (e j))) :=
  orderedReflectionWeights_linearIndependent r (fun j => P.root (e j))
    (b.linearIndepOn_root.comp e e.injective) (fun j => P.coroot' (e j))
    (fun j => P.reflection (e j)) (fun j z => P.reflection_apply (e j) z)
    (fun j => P.reflection_apply_self (e j))

end RootPairing

end Langlands.LinearAlgebra
