import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Langlands.Representation.Exponents.DualEigenfunctionalExistence
import Langlands.LinearAlgebra.CommutingNilpotentStrictUpperBasisStatement

/-! # Proof of the common strictly upper triangular basis for commuting nilpotents -/

namespace Langlands

namespace CommutingNilpotentStrictUpperBasis

universe uK uV uI

open Module

variable {K : Type uK} [Field K] {I : Type uI}

/-- A commuting nilpotent family on a nonzero finite-dimensional space has a
common nonzero functional vanishing on every range. -/
theorem exists_dual_ne_zero_forall_apply_eq_zero {V : Type uV} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] (N : I → Module.End K V)
    (hc : ∀ s t, Commute (N s) (N t)) (hn : ∀ t, IsNilpotent (N t)) :
    ∃ φ : Module.Dual K V, φ ≠ 0 ∧ ∀ t v, φ (N t v) = 0 := by
  have hc' : ∀ s t, Commute (N s).dualMap (N t).dualMap := by
    intro s t
    change (N s).dualMap ∘ₗ (N t).dualMap = (N t).dualMap ∘ₗ (N s).dualMap
    rw [LinearMap.dualMap_comp_dualMap, LinearMap.dualMap_comp_dualMap]
    exact congrArg LinearMap.dualMap (hc t s).eq
  have hn' : ∀ t, IsNilpotent (N t).dualMap := by
    intro t
    obtain ⟨k, hk⟩ := hn t
    refine ⟨k, ?_⟩
    ext φ v
    rw [DualEigenfunctional.dualMap_pow_apply, hk]
    simp
  have : Nontrivial (Module.Dual K V) :=
    Module.nontrivial_of_finrank_pos (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_pos)
  obtain ⟨φ, hφ, h⟩ := DualEigenfunctional.exists_ne_zero_forall_apply_eq_zero
    (fun t => (N t).dualMap) hc' hn'
  refine ⟨φ, hφ, fun t v => ?_⟩
  have := congrArg (fun ψ : Module.Dual K V => ψ v) (h t)
  simpa using this

/-- Dimension induction in span form: `N t (b j)` lies in the span of the
earlier basis vectors. -/
theorem exists_basis_mem_span_aux (d : ℕ) :
    ∀ (V : Type uV) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (N : I → Module.End K V), (∀ s t, Commute (N s) (N t)) → (∀ t, IsNilpotent (N t)) →
      finrank K V = d →
      ∃ b : Basis (Fin d) K V, ∀ t j, N t (b j) ∈ Submodule.span K (b '' {i | i < j}) := by
  induction d with
  | zero =>
    intro V _ _ _ N _ _ hd
    exact ⟨Module.finBasisOfFinrankEq K V hd, fun _ j => j.elim0⟩
  | succ d ih =>
    intro V _ _ _ N hc hn hd
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hd
    obtain ⟨φ, hφ, hφN⟩ := exists_dual_ne_zero_forall_apply_eq_zero N hc hn
    have hH : ∀ t, ∀ x ∈ LinearMap.ker φ, N t x ∈ LinearMap.ker φ :=
      fun t x _ => LinearMap.mem_ker.mpr (hφN t x)
    have hHd : finrank K (LinearMap.ker φ) = d := by
      have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
      omega
    have hnil : ∀ t, IsNilpotent ((N t).restrict (hH t)) := by
      intro t
      obtain ⟨k, hk⟩ := hn t
      refine ⟨k, ?_⟩
      ext x
      rw [Module.End.pow_restrict, LinearMap.restrict_apply]
      simp [hk]
    obtain ⟨b', hb'⟩ := ih (LinearMap.ker φ) (fun t => (N t).restrict (hH t))
      (fun s t => LinearMap.restrict_commute (hc s t) (hH s) (hH t)) hnil hHd
    obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    have hli : ∀ (c : K), ∀ x ∈ LinearMap.ker φ, c • y + x = 0 → c = 0 := by
      intro c x hx hcx
      have := congrArg φ hcx
      rw [map_add, map_smul, LinearMap.mem_ker.mp hx, smul_eq_mul, add_zero, map_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hy
    have hsp : ∀ z : V, ∃ c : K, z + c • y ∈ LinearMap.ker φ := by
      intro z
      refine ⟨-(φ z / φ y), ?_⟩
      rw [LinearMap.mem_ker, map_add, map_smul, smul_eq_mul]
      field_simp
      ring
    set b := Basis.mkFinSnoc b' y hli hsp with hbdef
    have hb : ⇑b = Fin.snoc (((↑) : LinearMap.ker φ → V) ∘ b') y := Basis.coe_mkFinSnoc _ _ _ _
    refine ⟨b, fun t j => ?_⟩
    induction j using Fin.lastCases with
    | last =>
      have hle : LinearMap.ker φ ≤ Submodule.span K (b '' {i | i < Fin.last d}) := by
        intro x hx
        have hmem : (⟨x, hx⟩ : LinearMap.ker φ) ∈ Submodule.span K (Set.range b') := by
          rw [b'.span_eq]
          exact Submodule.mem_top
        have := Submodule.apply_mem_span_image_of_mem_span (LinearMap.ker φ).subtype hmem
        refine Submodule.span_mono ?_ this
        rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k.castSucc, Fin.castSucc_lt_last k, by simp [hb]⟩
      apply hle
      rw [hb, Fin.snoc_last]
      exact LinearMap.mem_ker.mpr (hφN t y)
    | cast k =>
      have hmem := Submodule.apply_mem_span_image_of_mem_span (LinearMap.ker φ).subtype (hb' t k)
      have heq : N t (b k.castSucc) =
          (LinearMap.ker φ).subtype ((N t).restrict (hH t) (b' k)) := by
        rw [hb, Fin.snoc_castSucc]
        rfl
      rw [heq]
      refine Submodule.span_mono ?_ hmem
      rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i.castSucc, Fin.castSucc_lt_castSucc_iff.mpr hi, by simp [hb]⟩

/-- Every commuting family of nilpotent endomorphisms of a finite-dimensional
vector space has a common strictly upper triangular basis. -/
theorem commutingNilpotentStrictUpperBasis :
    CommutingNilpotentStrictUpperBasisStatement.{uK, uV, uI} := by
  intro K _ V _ _ _ I N hc hn
  obtain ⟨b, hb⟩ := exists_basis_mem_span_aux (K := K) (I := I) (finrank K V) V N hc hn rfl
  refine ⟨b, fun t i j hij => ?_⟩
  have hsupp := b.mem_span_image.mp (hb t j)
  by_contra h
  exact (not_lt.mpr hij) (hsupp (Finsupp.mem_support_iff.mpr h))

end CommutingNilpotentStrictUpperBasis

end Langlands
