/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Tensor maps of adjunctions with invertible unit, and base change of tensor maps

Let `adj : L ⊣ R` be an adjunction with a projection map `π M N : L M ⊗ N ⟶ L (M ⊗ F N)`, and
let `τ M N : R M ⊗ F N ⟶ R (M ⊗ N)` be its tensor map
(`CategoryTheory.Adjunction.projectionTensorMap`).

* If the right adjoint is `F` itself, with a tensor comparison `F (A ⊗ B) ≅ F A ⊗ F B` natural
  in `A`, and the unit of `L ⊣ F` is an isomorphism (an open immersion), then every tensor map is
  an isomorphism (`CategoryTheory.Adjunction.isIso_projectionTensorMap_of_isIso_unit`).
* If a base change map `β` is an isomorphism, then the tensor maps before and after base change
  determine each other (`CategoryTheory.Adjunction.isIso_map_map_projectionTensorMap_of_isIso`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory

section Unit

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {L : C ⥤ D}
  (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]
  (adj : L ⊣ F) (μ : ∀ A B : D, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)

/-- **The tensor map of an adjunction `L ⊣ F` with invertible unit is an isomorphism**, if `F`
has a tensor comparison `μ : F (A ⊗ B) ≅ F A ⊗ F B` natural in `A`. The tensor map is
`η ≫ F π⁻¹ ≫ F (ε_M ▷ N)`, and `F ε_M` is invertible by a triangle identity. -/
theorem isIso_projectionTensorMap_of_isIso_unit [IsIso adj.unit]
    (hμ : ∀ {A A' : D} (φ : A ⟶ A') (B : D),
      F.map (φ ▷ B) ≫ (μ A' B).hom = (μ A B).hom ≫ F.map φ ▷ F.obj B)
    (M N : D) :
    IsIso (adj.projectionTensorMap π M N) := by
  have := adj.isIso_map_counit_app_of_isIso_unit M
  have : IsIso (F.map (adj.counit.app M ▷ N)) := by
    have h := hμ (adj.counit.app M) N
    rw [← Iso.eq_comp_inv] at h
    rw [h]
    infer_instance
  rw [projectionTensorMap, homEquiv_unit, Functor.map_comp]
  infer_instance

end Unit

section BaseChange

/-- **Base change reflects the invertibility of tensor maps.** In the situation of
`CategoryTheory.Adjunction.projectionTensorMap_mateEquiv`, if the base change map `β` is an
isomorphism at `M` and at `M ⊗ N`, and the comparisons are isomorphisms, then for every functor
`H`, `H (Ga (τ M N))` is an isomorphism as soon as `H (τ' (Gb M) (Gb N))` is one. -/
theorem isIso_map_map_projectionTensorMap_of_isIso
    {Cx Cy Cx' Cy' E : Type*} [Category* Cx] [Category* Cy] [Category* Cx'] [Category* Cy']
    [Category* E]
    [MonoidalCategory Cx] [MonoidalCategory Cy] [MonoidalCategory Cx'] [MonoidalCategory Cy']
    {F : Cy ⥤ Cx} {L : Cx ⥤ Cy} {R : Cy ⥤ Cx} (adj : L ⊣ R)
    {F' : Cy' ⥤ Cx'} {L' : Cx' ⥤ Cy'} {R' : Cy' ⥤ Cx'} (adj' : L' ⊣ R')
    (π : ∀ (M : Cx) (N : Cy), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]
    (π' : ∀ (M : Cx') (N : Cy'), L'.obj M ⊗ N ⟶ L'.obj (M ⊗ F'.obj N)) [∀ M N, IsIso (π' M N)]
    (hπ' : ∀ {M M' : Cx'} (φ : M ⟶ M') (N : Cy'),
      L'.map φ ▷ N ≫ π' M' N = π' M N ≫ L'.map (φ ▷ F'.obj N))
    {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'}
    (δa : ∀ M M' : Cx, Ga.obj (M ⊗ M') ⟶ Ga.obj M ⊗ Ga.obj M') [∀ M M', IsIso (δa M M')]
    (δb : ∀ N N' : Cy, Gb.obj (N ⊗ N') ⟶ Gb.obj N ⊗ Gb.obj N') [∀ N N', IsIso (δb N N')]
    (hδb : ∀ {N N' : Cy} (φ : N ⟶ N') (N'' : Cy),
      Gb.map (φ ▷ N'') ≫ δb N' N'' = δb N N'' ≫ Gb.map φ ▷ Gb.obj N'')
    (κ : ∀ N : Cy, Ga.obj (F.obj N) ⟶ F'.obj (Gb.obj N)) [∀ N, IsIso (κ N)]
    (Ex : L ⋙ Gb ⟶ Ga ⋙ L') [IsIso Ex] (ξ : TwoSquare Ga L L' Gb)
    (hExξ : ∀ M : Cx, Ex.app M ≫ ξ.app M = 𝟙 _)
    (hEx : ∀ (M : Cx) (N : Cy), Gb.map (π M N) ≫ Ex.app (M ⊗ F.obj N) ≫
      L'.map (δa M (F.obj N)) ≫ L'.map (Ga.obj M ◁ κ N) =
        δb (L.obj M) N ≫ Ex.app M ▷ Gb.obj N ≫ π' (Ga.obj M) (Gb.obj N))
    (M N : Cy) [IsIso ((mateEquiv adj adj' ξ).app M)]
    [IsIso ((mateEquiv adj adj' ξ).app (M ⊗ N))] (H : Cx' ⥤ E)
    (h : IsIso (H.map (adj'.projectionTensorMap π' (Gb.obj M) (Gb.obj N)))) :
    IsIso (H.map (Ga.map (adj.projectionTensorMap π M N))) := by
  have key := projectionTensorMap_mateEquiv adj adj' π π' hπ' δa δb hδb κ Ex ξ hExξ hEx M N
  have : IsIso (H.map (Ga.map (adj.projectionTensorMap π M N) ≫
      (mateEquiv adj adj' ξ).app (M ⊗ N) ≫ R'.map (δb M N))) := by
    rw [key, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    infer_instance
  rw [Functor.map_comp] at this
  exact IsIso.of_isIso_comp_right _ (H.map ((mateEquiv adj adj' ξ).app (M ⊗ N) ≫
    R'.map (δb M N)))

end BaseChange

end CategoryTheory.Adjunction
