/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Full faithfulness does not identify ambient right adjoints

Let `D` be a preadditive category with binary biproducts, for instance the derived category
`D(k)` of vector spaces over a field. Consider the square of functors

```
      D ──── v_X = (-, 0) ───→ D × D
      │                          │
  F_et = 𝟭                F_proet = ⊞
      ↓                          ↓
      D ─────── v_Y = 𝟭 ───────→ D
```

Both comparison functors `v_X` and `v_Y` are fully faithful and `F_proet ∘ v_X ≅ v_Y ∘ F_et`.
The right adjoint of `F_proet` sends `K` to `(K, K)`, so the comparison
`v_X ∘ G_et ⟶ G_proet ∘ v_Y` of right adjoints has components `(K, 0) ⟶ (K, K)`, and no such
morphism is an isomorphism unless `K = 0`. So full faithfulness of the comparison functors and
agreement of the left adjoints do not formally make the comparison of right adjoints invertible.

## Main definitions

- `CategoryTheory.Limits.biprodFunctor`: the biproduct as a functor `D × D ⥤ D`.
- `CategoryTheory.Limits.biprodDiagAdjunction`: the adjunction `⊞ ⊣ diag`.

## Main statements

- `CategoryTheory.Limits.not_isIso_of_biprodFunctor_adjunction`: for every right adjoint `G`
  of `⊞` and every nonzero `K`, no morphism `(K, 0) ⟶ G K` is an isomorphism.
-/

@[expose] public section

universe w v u

open ZeroObject

namespace CategoryTheory.Limits

variable (D : Type u) [Category.{v} D] [Preadditive D] [HasBinaryBiproducts D]

/-- The biproduct `(M, N) ↦ M ⊞ N` as a functor `D × D ⥤ D`. -/
@[simps]
noncomputable def biprodFunctor : D × D ⥤ D where
  obj X := X.1 ⊞ X.2
  map f := biprod.map f.1 f.2

/-- The biproduct is left adjoint to the diagonal `K ↦ (K, K)`: morphisms `M ⊞ N ⟶ K`
correspond to pairs of morphisms `M ⟶ K`, `N ⟶ K`. -/
noncomputable def biprodDiagAdjunction : biprodFunctor D ⊣ Functor.diag D :=
  Adjunction.mkOfHomEquiv
    { homEquiv X K :=
        { toFun f := ((biprod.inl : X.1 ⟶ X.1 ⊞ X.2) ≫ f, (biprod.inr : X.2 ⟶ X.1 ⊞ X.2) ≫ f)
          invFun g := (biprod.desc g.1 g.2 : X.1 ⊞ X.2 ⟶ K)
          left_inv f := biprod.hom_ext' _ _ (by simp) (by simp)
          right_inv g := by ext <;> simp }
      homEquiv_naturality_left_symm f g :=
        biprod.hom_ext' _ _ (by simp) (by simp)
      homEquiv_naturality_right f g := by
        ext <;> simp }

/-- The functor `M ↦ (M, 0)` is fully faithful. -/
noncomputable def fullyFaithfulSectLZero [Limits.HasZeroObject D] :
    (Prod.sectL D (0 : D)).FullyFaithful where
  preimage f := f.1
  map_preimage f := by
    ext
    · rfl
    · exact (Limits.isZero_zero D).eq_of_src _ _

/-- The composite of `M ↦ (M, 0)` with the biproduct is isomorphic to the identity. -/
noncomputable def sectLZeroCompBiprodFunctorIso [Limits.HasZeroObject D] :
    Prod.sectL D (0 : D) ⋙ biprodFunctor D ≅ 𝟭 D :=
  NatIso.ofComponents (fun M ↦ (isoBiprodZero (Limits.isZero_zero D)).symm) (fun f ↦ by
    dsimp [isoBiprodZero]; exact biprod.map_fst _ _)

variable {D}

/-- Blueprint `ex-exc-comparison-not-formal`: **full faithfulness does not identify ambient
right adjoints.** Let `D` be a preadditive category with binary biproducts (for instance the
derived category of vector spaces over a field), `G` any right adjoint of the biproduct functor
`⊞ : D × D ⥤ D`, and `K` a nonzero object. Then no morphism `(K, 0) ⟶ G K` is an isomorphism;
in particular the comparison `v_X ∘ G_et ⟶ G_proet ∘ v_Y` of the right adjoints in the square
with `v_X = (-, 0)` (fully faithful, `CategoryTheory.Limits.fullyFaithfulSectLZero`),
`v_Y = F_et = 𝟭` and `F_proet = ⊞` (which satisfies `F_proet ∘ v_X ≅ 𝟭`,
`CategoryTheory.Limits.sectLZeroCompBiprodFunctorIso`) is not an isomorphism at `K`: indeed
`G K ≅ (K, K)` by uniqueness of adjoints and `CategoryTheory.Limits.biprodDiagAdjunction`.
(blueprint: `ex-exc-comparison-not-formal`) -/
theorem not_isIso_of_biprodFunctor_adjunction [Limits.HasZeroObject D] {G : D ⥤ D × D}
    (adj : biprodFunctor D ⊣ G) (K : D) (hK : ¬ IsZero K)
    (f : (Prod.sectL D (0 : D)).obj K ⟶ G.obj K) : ¬ IsIso f := by
  intro hf
  let e : (Prod.sectL D (0 : D)).obj K ≅ (Functor.diag D).obj K :=
    asIso f ≪≫ (adj.rightAdjointUniq (biprodDiagAdjunction D)).app K
  exact hK ((Limits.isZero_zero D).of_iso ((Prod.snd D D).mapIso e).symm)

/-- **The counterexample in the derived category of a field.** For a field `k` and a nonzero
object `K` of the derived category `D(k)` of `k`-vector spaces, and any right adjoint `G` of
the biproduct functor `D(k) × D(k) ⥤ D(k)`, no morphism `(K, 0) ⟶ G K` is an isomorphism.
(blueprint: `ex-exc-comparison-not-formal`) -/
theorem _root_.DerivedCategory.not_isIso_of_biprodFunctor_adjunction (k : Type u) [Field k]
    [HasDerivedCategory.{w} (ModuleCat.{v} k)]
    {G : DerivedCategory (ModuleCat.{v} k) ⥤ DerivedCategory (ModuleCat.{v} k) ×
      DerivedCategory (ModuleCat.{v} k)}
    (adj : biprodFunctor _ ⊣ G) (K : DerivedCategory (ModuleCat.{v} k)) (hK : ¬ IsZero K)
    (f : (Prod.sectL _ (0 : DerivedCategory (ModuleCat.{v} k))).obj K ⟶ G.obj K) :
    ¬ IsIso f :=
  Limits.not_isIso_of_biprodFunctor_adjunction adj K hK f

end CategoryTheory.Limits
