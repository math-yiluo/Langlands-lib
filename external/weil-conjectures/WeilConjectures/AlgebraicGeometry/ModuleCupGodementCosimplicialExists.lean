/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
import WeilConjectures.CategoryTheory.SimplexPresentationFaithful
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementRelations

/-! # Realization of the concrete Godement cosimplicial operators -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem presentation_surjective (n m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) :
    ∃ g : SimplexCategoryGenRel.mk n ⟶ SimplexCategoryGenRel.mk m,
      SimplexCategoryGenRel.toSimplexCategory.map g = f := by
  have key : ∀ k n m : ℕ, n + m = k → ∀ f : ⦋n⦌ ⟶ ⦋m⦌,
      ∃ g : SimplexCategoryGenRel.mk n ⟶ SimplexCategoryGenRel.mk m,
        SimplexCategoryGenRel.toSimplexCategory.map g = f := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n m hk f
      by_cases hinj : Function.Injective f.toOrderHom
      · by_cases hsurj : Function.Surjective f.toOrderHom
        · have hcard := Fintype.card_congr (Equiv.ofBijective f.toOrderHom ⟨hinj, hsurj⟩)
          simp only [Fintype.card_fin, SimplexCategory.len_mk] at hcard
          have hnm : n = m := by omega
          subst m
          have : Mono f := SimplexCategory.mono_iff_injective.mpr hinj
          exact ⟨𝟙 _, by simpa using (SimplexCategory.eq_id_of_mono f).symm⟩
        · cases m with
          | zero =>
            exfalso
            apply hsurj
            intro x
            refine ⟨0, ?_⟩
            apply Fin.ext
            have hx := x.isLt
            have hf := (f.toOrderHom 0).isLt
            simp only [SimplexCategory.len_mk] at hx hf
            omega
          | succ m =>
            obtain ⟨i, f', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f hsurj
            obtain ⟨g, hg⟩ := ih (n + m) (by omega) n m rfl f'
            exact ⟨g ≫ SimplexCategoryGenRel.δ i, by simp [hg]⟩
      · cases n with
        | zero =>
          exfalso
          apply hinj
          intro a b hab
          apply Fin.ext
          have ha := a.isLt
          have hb := b.isLt
          simp only [SimplexCategory.len_mk] at ha hb
          omega
        | succ n =>
          obtain ⟨i, f', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hinj
          obtain ⟨g, hg⟩ := ih (n + m) (by omega) n m rfl f'
          exact ⟨SimplexCategoryGenRel.σ i ≫ g, by simp [hg]⟩
  exact key (n + m) n m rfl f

private theorem presentation_full : SimplexCategoryGenRel.toSimplexCategory.Full := by
  constructor
  intro a b f
  rcases a with ⟨n⟩
  rcases b with ⟨m⟩
  exact presentation_surjective n m f

/-- The unit insertions and multiplication collapses form a cosimplicial object.
Source: Stacks Project, Tag 0FKR; Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16.
(blueprint: lem-sc-module-cup-godement-cosimplicial-exists)
Proof: take the stalk functor to families of stalk modules and its right adjoint,
the product of stalk skyscrapers. The product of skyscraperHomEquiv gives the
adjunction. Its endofunctor and unit are the concrete Godement object, map and
unit; its multiplication is moduleCup_godementMultiply, as seen by projecting
to each point and evaluating the stalk there. The triangle identities give the
two unit laws, and the counit naturality gives associativity. In degree n use
T^(n+1)(F), insert the unit for cofaces and multiplication for codegeneracies.
The monad laws and naturality prove the coface, codegeneracy and mixed
identities. Extend to every simplex map by its unique surjection/injection
factorization; the identities prove independence and preservation of
composition. The recursive insert and collapse definitions are exactly these
operators, and the term equalities are reflexivity. Empty products and zero
modules require no exceptions. This statement constructs no augmentation. -/
theorem moduleCup_godement_cosimplicial_exists (X : Scheme.{u}) (F : X.Modules) :
    ∃ (A : CosimplicialObject X.Modules)
      (h : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1)),
      (∀ (n : ℕ) (i : Fin (n + 2)),
        eqToHom (h n) ≫ moduleCup_godementInsert X F (n + 1) i =
          A.map (SimplexCategory.δ i) ≫ eqToHom (h (n + 1))) ∧
      (∀ (n : ℕ) (i : Fin (n + 1)),
        eqToHom (h (n + 1)) ≫ moduleCup_godementCollapse X F n i =
          A.map (SimplexCategory.σ i) ≫ eqToHom (h n)) := by
  have hfull := presentation_full
  have hfaithful := simplexPresentation_faithful
  let Q : SimplexCategoryGenRel ⥤ X.Modules :=
    CategoryTheory.Quotient.lift FreeSimplexQuiver.homRel
      (Paths.lift (moduleCup_godementQuiver X F))
      (moduleCup_godement_relations X F)
  let A : CosimplicialObject X.Modules :=
    { obj n := Q.obj (SimplexCategoryGenRel.mk n.len)
      map f := Q.map (SimplexCategoryGenRel.toSimplexCategory.preimage f)
      map_id n := by
        cases n
        exact (congrArg Q.map (Functor.preimage_id
          (F := SimplexCategoryGenRel.toSimplexCategory)
          (X := SimplexCategoryGenRel.mk _))).trans (Q.map_id _)
      map_comp {a b c} f g := by
        cases a
        cases b
        cases c
        rw [Functor.preimage_comp, Functor.map_comp] }
  refine ⟨A, fun _ ↦ rfl, ?_, ?_⟩
  · intro n i
    change moduleCup_godementInsert X F (n + 1) i =
      Q.map (SimplexCategoryGenRel.toSimplexCategory.preimage (SimplexCategory.δ i))
    rw [← SimplexCategoryGenRel.toSimplexCategory_map_δ, Functor.preimage_map]
    simp [Q, SimplexCategoryGenRel.δ, CategoryTheory.Quotient.lift_map_functor_map,
      Paths.lift_toPath, moduleCup_godementQuiver, Paths.of_map,
      FreeSimplexQuiver.len, FreeSimplexQuiver.mk]
  · intro n i
    change moduleCup_godementCollapse X F n i =
      Q.map (SimplexCategoryGenRel.toSimplexCategory.preimage (SimplexCategory.σ i))
    rw [← SimplexCategoryGenRel.toSimplexCategory_map_σ, Functor.preimage_map]
    simp [Q, SimplexCategoryGenRel.σ, CategoryTheory.Quotient.lift_map_functor_map,
      Paths.lift_toPath, moduleCup_godementQuiver, Paths.of_map,
      FreeSimplexQuiver.len, FreeSimplexQuiver.mk]

end
end AlgebraicGeometry.Scheme.Modules
