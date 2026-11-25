/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Preadditive.TraceSplitting
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!

# Averaging idempotents through a functor

Let `u = uₙ ≫ c` factor a unit through a finite level `Tₙ`, with a retraction `r` of `uₙ` whose
idempotent is an average: `n • (r ≫ uₙ) = ∑ a, ρ a` (the normalized Galois trace,
`CategoryTheory.nsmul_normalizedTrace_comp_eq_sum`). If an additive functor `Φ` inverts `c`, the
retraction `(Φ c)⁻¹ ≫ Φ r` of `Φ u` has idempotent `1/n` times the sum of the transported
actions `(Φ c)⁻¹ ≫ Φ (ρ a) ≫ Φ c`, which are the actions `σ a` on `Φ T` whenever `c` is
equivariant (`CategoryTheory.nsmul_inv_map_comp_map_comp_eq_sum`). This is the form in which
the finite-level splitting of Galois covers is applied to nearby cycles.

-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] (Φ : C ⥤ D)
  [Φ.Additive] {G Tₙ T : C}

/-- **Averaging idempotent through a functor.** If `n • (r ≫ uₙ) = ∑ a, ρ a`, `Φ` inverts `c`
and `Φ c` intertwines the actions, `Φ (ρ a) ≫ Φ c = Φ c ≫ σ a`, then the retraction
`(Φ c)⁻¹ ≫ Φ r` of `Φ (uₙ ≫ c)` satisfies `n • ((Φ c)⁻¹ ≫ Φ r ≫ Φ (uₙ ≫ c)) = ∑ a, σ a`:
```
Φ Tₙ --Φ c--> Φ T
 |Φ(ρ a)       |σ a
 v             v
Φ Tₙ --Φ c--> Φ T
```
-/
lemma nsmul_inv_map_comp_map_comp_eq_sum (uₙ : G ⟶ Tₙ) (c : Tₙ ⟶ T) (r : Tₙ ⟶ G) (n : ℕ)
    {ι : Type*} [Fintype ι] (ρ : ι → (Tₙ ⟶ Tₙ)) (σ : ι → (Φ.obj T ⟶ Φ.obj T))
    (havg : n • (r ≫ uₙ) = ∑ a, ρ a) (hσ : ∀ a, Φ.map (ρ a) ≫ Φ.map c = Φ.map c ≫ σ a)
    [IsIso (Φ.map c)] :
    n • ((inv (Φ.map c) ≫ Φ.map r) ≫ Φ.map (uₙ ≫ c)) = ∑ a, σ a := by
  have h : (inv (Φ.map c) ≫ Φ.map r) ≫ Φ.map (uₙ ≫ c) =
      inv (Φ.map c) ≫ Φ.map (r ≫ uₙ) ≫ Φ.map c := by
    simp only [Φ.map_comp, assoc]
  rw [h, ← Preadditive.comp_nsmul, ← Preadditive.nsmul_comp, ← Φ.map_nsmul, havg,
    Φ.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hσ, IsIso.inv_hom_id_assoc]

end CategoryTheory
