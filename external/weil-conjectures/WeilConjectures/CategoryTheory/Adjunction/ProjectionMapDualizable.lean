/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# The projection map at a dualizable object

Let `adj : F ⊣ G` be an adjunction between monoidal categories, with `F : D ⥤ C` a monoidal
functor. The right adjoint projection map `G M ⊗ L ⟶ G (M ⊗ F L)` built from the comonoidal
structure `δ` of `F` (`CategoryTheory.Adjunction.rightAdjointProjectionMap`) is an isomorphism
as soon as `L` is dualizable. This is formal: if `Z` is a left dual of `L`, both sides are right
adjoints of `T ↦ F (T ⊗ Z) ≅ F T ⊗ F Z`, and the projection map is the conjugate of the monoidal
structure `μ` of `F`.

## Main statements

- `CategoryTheory.Adjunction.rightAdjointProjectionMap_app_app_eq_conjugateEquiv`: if `L` has a
  left dual `Z`, the projection map at `L` is the conjugate of `μ (-) Z`.
- `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_of_exactPairing`: the
  projection map is an isomorphism at `L` if `L` has a left dual.
- `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isDualizable`: in a
  braided category, the projection map is an isomorphism at a dualizable `L`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : D ⥤ C)

/-- The monoidal structure `F T ⊗ F Z ⟶ F (T ⊗ Z)` of a lax monoidal functor `F`, as a natural
transformation in `T`. -/
@[simps]
def μTensorRight [F.LaxMonoidal] (Z : D) : F ⋙ tensorRight (F.obj Z) ⟶ tensorRight Z ⋙ F where
  app T := μ F T Z
  naturality _ _ f := by simp [μ_natural_left]

instance [F.Monoidal] (Z : D) : IsIso (F.μTensorRight Z) :=
  have (T : D) : IsIso ((F.μTensorRight Z).app T) :=
    (Functor.Monoidal.μIso F T Z).isIso_hom
  NatIso.isIso_of_isIso_app _

end Functor

namespace Adjunction

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))

/-- **The projection map as a conjugate.** Let `adj : F ⊣ G` be an adjunction with `F` monoidal,
let `φ` be the comonoidal structure `δ` of `F`, and let `Z` be a left dual of `L`. Composing
`adj` with `(- ⊗ Z) ⊣ (- ⊗ L)` and `(- ⊗ F Z) ⊣ (- ⊗ F L)` exhibits `M ↦ G M ⊗ L` and
`M ↦ G (M ⊗ F L)` as right adjoints of `T ↦ F (T ⊗ Z)` and `T ↦ F T ⊗ F Z`. The projection map
`π : G M ⊗ L ⟶ G (M ⊗ F L)` is the conjugate of `μ (-) Z : F T ⊗ F Z ⟶ F (T ⊗ Z)`, that is,
the unique map making the square of counits
```
  F (G M ⊗ L) ⊗ F Z --F π ▷ F Z--> F (G (M ⊗ F L)) ⊗ F Z
         |                                   |
     μ (G M ⊗ L) Z                           ε₂
         v                                   v
  F ((G M ⊗ L) ⊗ Z) -----------ε₁----------> M
```
commute. -/
theorem rightAdjointProjectionMap_app_app_eq_conjugateEquiv
    (hφ : ∀ a b, (φ.app a).app b = δ F a b) (M : C) (Z L : D) [ExactPairing Z L] :
    letI := ExactPairing.map F Z L
    ((adj.rightAdjointProjectionMap φ).app M).app L =
      (conjugateEquiv ((tensorRightAdjunction Z L).comp adj)
        (adj.comp (tensorRightAdjunction (F.obj Z) (F.obj L))) (F.μTensorRight Z)).app M := by
  let := ExactPairing.map F Z L
  let adj₁ := (tensorRightAdjunction Z L).comp adj
  let adj₂ := adj.comp (tensorRightAdjunction (F.obj Z) (F.obj L))
  apply (adj₂.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit]
  refine Eq.trans ?_ (conjugateEquiv_counit adj₁ adj₂ (F.μTensorRight Z) M).symm
  have h := adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M L
  rw [hφ] at h
  simp only [adj₁, adj₂, comp_counit_app, tensorRightAdjunction_counit_app] at h ⊢
  dsimp at h ⊢
  rw [← comp_whiskerRight_assoc, h]
  have hε : ε_ (F.obj Z) (F.obj L) = μ F L Z ≫ F.map (ε_ Z L) ≫ η F := rfl
  rw [hε]
  rw [comp_whiskerRight, Category.assoc, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]
  simp only [← Category.assoc]
  congr 1
  simp only [Functor.map_comp, Functor.Monoidal.map_associator, Functor.Monoidal.map_whiskerLeft,
    Functor.Monoidal.map_rightUnitor, Category.assoc, Functor.Monoidal.μ_δ_assoc,
    MonoidalCategory.whiskerLeft_comp, μTensorRight_app]

/-- **The projection map at an object with a left dual.** Let `adj : F ⊣ G` be an adjunction
with `F` monoidal, and let `φ` be the comonoidal structure `δ` of `F`. If `L` has a left dual
`Z`, the projection map `G M ⊗ L ⟶ G (M ⊗ F L)` is an isomorphism. -/
theorem isIso_rightAdjointProjectionMap_app_app_of_exactPairing
    (hφ : ∀ a b, (φ.app a).app b = δ F a b) (M : C) (Z L : D) [ExactPairing Z L] :
    IsIso (((adj.rightAdjointProjectionMap φ).app M).app L) := by
  let := ExactPairing.map F Z L
  rw [adj.rightAdjointProjectionMap_app_app_eq_conjugateEquiv φ hφ M Z L]
  infer_instance

/-- **The projection map at a dualizable object.** Let `adj : F ⊣ G` be an adjunction with `F`
monoidal, and let `φ` be the comonoidal structure `δ` of `F`. If `D` is braided and `L` is
dualizable, the projection map `G M ⊗ L ⟶ G (M ⊗ F L)` is an isomorphism. -/
theorem isIso_rightAdjointProjectionMap_app_app_of_isDualizable [BraidedCategory D]
    (hφ : ∀ a b, (φ.app a).app b = δ F a b) (M : C) {L : D} (hL : IsDualizable L) :
    IsIso (((adj.rightAdjointProjectionMap φ).app M).app L) := by
  obtain ⟨_⟩ := hL
  let := BraidedCategory.exactPairing_swap L Lᘁ
  exact adj.isIso_rightAdjointProjectionMap_app_app_of_exactPairing φ hφ M Lᘁ L

end Adjunction

end CategoryTheory
