/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationExhaustive
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationQuotients

/-!
# A free filtration on a direct-sum total complex

Source: Stacks Project, Tag 09KP, construction of the filtration of the total complex.
(blueprint: lem-pc-derived-total-free-filtration)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The total complex of nonpositive columns with split free two-step filtrations
has an exhaustive, degreewise split filtration with free zero-differential quotients.
Source: Stacks Project, Differential Graded Algebra, Tag 09KP, proof, filtration
construction, specialized to a ring in degree zero.
(blueprint: lem-pc-derived-total-free-filtration)

Proof. Choose the split short exact sequence for column `-i` and transport its
left term to a subcomplex `Uᵢ` of that column using the middle-object isomorphism.
Both `Uᵢ` and the quotient have zero differential: each is isomorphic to a coproduct
of single-degree copies of `A`. In total degree `k`, set `F₀ = 0`, let `F₂ᵢ₊₁`
contain every full column `-j` with `j < i`, together with `Uᵢ` in column `-i`,
and let `F₂ᵢ₊₂` contain every full column `-j` with `j ≤ i`. Use the vertical
degree `k+j` in column `-j`.

The total differential preserves these submodules. Horizontal differentials
move column `-j` to `-(j-1)`, already included when `j > 0`; for `j = 0`
the target is a zero positive column. On `Uᵢ` the vertical differential vanishes;
on a full column the vertical differential stays in that column.
Thus they define subcomplexes with their inclusion morphisms and compatible
successive inclusion maps. Each inclusion is injective in every degree, hence
monic. Every element of a direct sum has finite support; positive columns vanish,
so it lies in `F₂ᵢ₊₂` for `i` at least every index in its support. This proves
exhaustiveness, including zero (which already lies in `F₀`).

The successive quotients are `Uᵢ` shifted in total degree by `-i`, and the
quotient of column `-i` by `Uᵢ` shifted by `-i`. Horizontal differentials vanish
in these quotients because their target columns occur earlier; their vertical
differentials vanish by the chosen single-degree decompositions. A summand in
vertical degree `d` therefore becomes a single summand in total degree `d-i`.
The given degreewise splittings yield retractions for each successive inclusion:
project away the new column part, using the splitting of `Uᵢ` inside its column
for the second inclusion. The inclusion out of zero has the zero retraction.
These descriptions identify the categorical cokernels with the stated coproducts.
-/
theorem exists_totalFreeFiltration {A : Type u} [CommRing A]
    (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (h_columns : ∀ p : ℤ, p ≤ 0 →
      ∃ S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ),
        Nonempty (S.X₂ ≅ K.X p) ∧ S.ShortExact ∧
        (∀ k : ℤ,
          Nonempty
            (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)).Splitting) ∧
        ∃ (I₁ I₃ : Type u) (d₁ : I₁ → ℤ) (d₃ : I₃ → ℤ),
          Nonempty (S.X₁ ≅ ∐ (fun i : I₁ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₁ i)).obj
              (ModuleCat.of A A))) ∧
          Nonempty (S.X₃ ≅ ∐ (fun i : I₃ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₃ i)).obj
              (ModuleCat.of A A)))) :
      ∃ (F : ℕ → CochainComplex (ModuleCat.{u} A) ℤ)
        (ι : ∀ n, F n ⟶ K.total (ComplexShape.up ℤ)) (step : ∀ n, F n ⟶ F (n + 1)),
        IsZero (F 0) ∧
        (∀ n, Mono (ι n)) ∧
        (∀ n, step n ≫ ι (n + 1) = ι n) ∧
        (∀ (k : ℤ) (x : (K.total (ComplexShape.up ℤ)).X k),
          ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x) ∧
        (∀ (n : ℕ) (k : ℤ),
          ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
            (step n).f k ≫ r = 𝟙 ((F n).X k)) ∧
      (∀ n, ∃ (I : Type u) (degree : I → ℤ),
          Nonempty (cokernel (step n) ≅
            ∐ (fun i : I ↦
              (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (degree i)).obj
                (ModuleCat.of A A)))) := by
  classical
  have hc (j : ℕ) := h_columns (-(j : ℤ)) (by omega)
  choose S he h_exact h_split h_free using hc
  let e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)) := fun j ↦ (he j).some
  let F := TotalFreeFiltration.complex K S e h_positive
  let ι := TotalFreeFiltration.inclusion K S e h_positive
  let step := TotalFreeFiltration.step K S e h_positive
  obtain ⟨hretract, hcoker⟩ :=
    TotalFreeFiltration.quotients K S e h_positive h_exact h_split h_free
  refine ⟨F, ι, step, ?_, ?_, ?_, ?_, hretract, hcoker⟩
  · exact TotalFreeFiltration.restrict_zero _ _ _
      (TotalFreeFiltration.term_zero K S e)
  · intro n
    exact TotalFreeFiltration.restrict_mono _ _ _
  · intro n
    exact TotalFreeFiltration.restrict_comp _ _ _ _ _ _
  · exact TotalFreeFiltration.restrict_surjective _ _ _
      (TotalFreeFiltration.exhaustive K S e h_positive)

end CochainComplex
