/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationTerms

/-!
# Exhaustiveness of the alternating column submodules

Source: Stacks Project, Tag 09KP, filtration construction.
(blueprint: lem-pc-derived-total-filtration-exhaustive)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))
variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

private lemma full_mem (j : ℕ) (k : ℤ) (x : (K.X (-(j : ℤ))).X (k + j)) :
    full K j k x ∈ term K S e (2 * j + 2) k := by
  apply (le_iSup (fun j' : ℕ ↦
    (if 2 * j' + 2 ≤ 2 * j + 2 then LinearMap.range (full K j' k).hom else ⊥) ⊔
    (if 2 * j' + 1 ≤ 2 * j + 2 then LinearMap.range (lower K S e j' k).hom else ⊥)) j)
  apply Submodule.mem_sup_left
  simp only [le_refl, ite_true]
  exact ⟨x, rfl⟩

private lemma generator_mem (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (k p q : ℤ) (hi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = k) (x : (K.X p).X q) :
    K.ιTotal (ComplexShape.up ℤ) p q k hi x ∈ ⨆ n, term K S e n k := by
  by_cases hp : p ≤ 0
  · obtain ⟨j, hpj⟩ : ∃ j : ℕ, p = -(j : ℤ) :=
      ⟨(-p).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
    subst p
    change -(j : ℤ) + q = k at hi
    have hq : q = k + j := by omega
    subst q
    exact (le_iSup (fun n ↦ term K S e n k) (2 * j + 2)) (full_mem K S e j k x)
  · have hz : IsZero ((K.X p).X q) := by
      rw [IsZero.iff_id_eq_zero]
      exact HomologicalComplex.congr_hom ((h_positive p (by omega)).eq_zero_of_src
        (𝟙 (K.X p))) q
    rw [hz.eq_zero_of_src (K.ιTotal (ComplexShape.up ℤ) p q k hi)]
    simp

private lemma total_mem (k : ℤ)
    (M : Submodule A ((K.total (ComplexShape.up ℤ)).X k))
    (hm : ∀ p q (hi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = k) (x : (K.X p).X q),
      K.ιTotal (ComplexShape.up ℤ) p q k hi x ∈ M)
    (x : (K.total (ComplexShape.up ℤ)).X k) : x ∈ M := by
  let f : ∀ p q (hi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = k), (K.X p).X q ⟶ ModuleCat.of A M :=
    fun p q hi ↦ ModuleCat.ofHom ((K.ιTotal (ComplexShape.up ℤ) p q k hi).hom.codRestrict M
      (hm p q hi))
  have hfac : K.totalDesc f ≫ ModuleCat.ofHom M.subtype = 𝟙 _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hi
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc, Category.comp_id]
    rfl
  have heq := congrArg (fun g ↦ g x) hfac
  change (K.totalDesc f x).val = x at heq
  rw [← heq]
  exact (K.totalDesc f x).property

private lemma directed_mem (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ℕ → ∀ k : ℤ, Submodule A (T.X k))
    (hm : ∀ n m, n ≤ m → ∀ k, M n k ≤ M m k)
    (k : ℤ) (x : T.X k) (hx : x ∈ ⨆ n, M n k) : ∃ n, x ∈ M n k := by
  exact (Submodule.mem_iSup_of_directed _
    (fun n m ↦ ⟨max n m, hm n _ (Nat.le_max_left _ _) k,
      hm m _ (Nat.le_max_right _ _) k⟩)).mp hx

/-- Every total-degree element belongs to an alternating column stage.
Source: Stacks Project, Tag 09KP, proof, finite support argument.
(blueprint: lem-pc-derived-total-filtration-exhaustive)

Proof. The full column inclusions generate each total-degree coproduct. Positive
columns contribute zero; every nonpositive column is `-j` and its full image lies
in stage `2*j+2`. Thus the supremum of the stage submodules is the whole module.
Their monotonicity makes them a directed family, so membership in the supremum
is membership in some stage. This is the finite-support argument for direct sums.
-/
theorem exhaustive (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (k : ℤ) (x : (K.total (ComplexShape.up ℤ)).X k) :
    ∃ n : ℕ, x ∈ term K S e n k := by
  have hx : x ∈ ⨆ n, term K S e n k :=
    total_mem K k _ (generator_mem K S e h_positive k) x
  exact directed_mem _ (term K S e)
    (fun _ _ h k ↦ term_mono K S e h k) k x hx

end CochainComplex.TotalFreeFiltration
