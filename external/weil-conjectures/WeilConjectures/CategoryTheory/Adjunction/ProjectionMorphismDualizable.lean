/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
public import WeilConjectures.CategoryTheory.MonoidalProjectionConjugate
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!

# Projection morphisms at dualizable objects

Let `F ⊣ G` be an adjunction between monoidal categories whose left adjoint `F` is strong
monoidal. For a dualizable object `B`, the left projection morphism
`B ⊗ G A ⟶ G (F B ⊗ A)` (`CategoryTheory.Adjunction.leftProjectionMorphism`) is an isomorphism:
it is the conjugate of the isomorphism `F (Bᘁ ⊗ -) ≅ F Bᘁ ⊗ F -` under the adjunctions
`(Bᘁ ⊗ -) ⊣ (B ⊗ -)` composed with `F ⊣ G` (`CategoryTheory.monoidal_projection_conjugate`).

## Main statements

- `CategoryTheory.Adjunction.isIso_leftProjectionMorphism_of_isDualizable`: the left projection
  morphism is an isomorphism at a dualizable object.
- `CategoryTheory.Adjunction.isIso_projectionMorphism_of_exactPairing`,
  `CategoryTheory.Adjunction.isIso_projectionMorphism_of_isDualizable`: the projection morphism
  `G A ⊗ B ⟶ G (A ⊗ F B)` is an isomorphism at an object with a left dual (at a dualizable
  object, for braided `D`).
- `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_of_isDualizable`: the transpose of
  `F (B ⊗ X) ⟶ F B ⊗ F X ⟶ A₁ ⊗ A₂` is an isomorphism for dualizable `B`, `a : F B ⟶ A₁` an
  isomorphism and `c : F X ⟶ A₂` with invertible transpose.
- `CategoryTheory.Adjunction.homEquiv_hom_app_comp_map_counit`: the transpose of
  `θ (Rf K) ≫ G' (ε_K)` is the exchange morphism of `θ`.
- `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_exchangeRight_of_isDualizable`: the
  Künneth map along a base change with a dualizable first factor is an isomorphism if the
  exchange morphism is.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]

/-- For a strong monoidal left adjoint `F ⊣ G` and an object `B` with an exact pairing
`B ⊗ B' ⟶ 𝟙`, the left projection morphism `B ⊗ G A ⟶ G (F B ⊗ A)` is an isomorphism. -/
lemma isIso_leftProjectionMorphism_of_exactPairing (B B' : D) [ExactPairing B B'] (A : C) :
    IsIso (adj.leftProjectionMorphism B A) := by
  let := ExactPairing.map F B B'
  rw [leftProjectionMorphism, ← Functor.Monoidal.μIso_inv]
  exact monoidal_projection_conjugate F G adj B B' A ▸ inferInstance

/-- For a strong monoidal left adjoint `F ⊣ G` and a dualizable object `B`, the left projection
morphism `B ⊗ G A ⟶ G (F B ⊗ A)` is an isomorphism. -/
lemma isIso_leftProjectionMorphism_of_isDualizable {B : D} (hB : IsDualizable B) (A : C) :
    IsIso (adj.leftProjectionMorphism B A) := by
  obtain ⟨_⟩ := hB
  exact adj.isIso_leftProjectionMorphism_of_exactPairing B Bᘁ A

/-- **Künneth maps with a dualizable first factor**: for a strong monoidal left adjoint `F ⊣ G`,
a dualizable `B`, an isomorphism `a : F B ⟶ A₁` and a morphism `c : F X ⟶ A₂` whose transpose
`X ⟶ G A₂` is an isomorphism, the transpose `B ⊗ X ⟶ G (A₁ ⊗ A₂)` of
`F (B ⊗ X) ⟶ F B ⊗ F X ⟶ A₁ ⊗ A₂` is an isomorphism. It is `B ◁ c♯` followed by the left
projection morphism and `G (a ▷ A₂)` (`homEquiv_δ_whiskerLeft`). -/
lemma isIso_homEquiv_δ_tensorHom_of_isDualizable {B X : D} (hB : IsDualizable B) {A₁ A₂ : C}
    (a : F.obj B ⟶ A₁) (ha : IsIso a) (c : F.obj X ⟶ A₂) (hc : IsIso (adj.homEquiv _ _ c)) :
    IsIso (adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F B X ≫ (a ⊗ₘ c))) := by
  have := adj.isIso_leftProjectionMorphism_of_isDualizable hB A₂
  rw [tensorHom_def', ← Category.assoc, homEquiv_naturality_right, homEquiv_δ_whiskerLeft]
  infer_instance

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']

/-- The transpose of `θ (Rf K) ≫ G' (ε_K) : Lf' G Rf K ⟶ G' K` along `Lf' ⊣ Rf'` is the exchange
morphism `G Rf K ⟶ Rf' G' K` of `θ : G ⋙ Lf' ≅ Lf ⋙ G'`. -/
lemma homEquiv_hom_app_comp_map_counit {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'}
    {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') (K : A) :
    af'.homEquiv (G.obj (Rf.obj K)) (G'.obj K) (θ.hom.app (Rf.obj K) ≫ G'.map (af.counit.app K)) =
      (exchangeRight af af' θ).app K := by
  rw [← Equiv.eq_symm_apply, homEquiv_counit]
  simp [exchangeRight_app]


/-- The transpose of `θ (Rf K) ≫ G' (ε_K) : Lf' G Rf K ⟶ G' K` along `Lf' ⊣ Rf'` is an
isomorphism if the exchange morphism of `θ : G ⋙ Lf' ≅ Lf ⋙ G'` is. The source of the
composite is written `Lf' (G (Rf K))`, so that the lemma can be instantiated by unification with
concrete morphisms written in this form. -/
lemma isIso_homEquiv_hom_app_comp_map_counit {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'}
    {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') (K : A) (hK : IsIso (exchangeRight af af' θ)) :
    IsIso (af'.homEquiv (G.obj (Rf.obj K)) (G'.obj K)
      (@CategoryStruct.comp A' _ (Lf'.obj (G.obj (Rf.obj K))) ((Lf ⋙ G').obj (Rf.obj K))
        (G'.obj K) (θ.hom.app (Rf.obj K)) (G'.map (af.counit.app K)))) := by
  have h := homEquiv_hom_app_comp_map_counit af af' θ K
  exact h ▸ NatIso.isIso_app_of_isIso _ K

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]

/-- **Künneth maps along a base change with a dualizable first factor.** Let `F ⊣ G` be an
adjunction with `F` strong monoidal, `Lj ⊣ Rj` an adjunction and `θ : P ⋙ F ≅ Lj ⋙ Q` a natural
isomorphism whose exchange morphism `Rj ⋙ P ⟶ Q ⋙ G` is an isomorphism. For a dualizable `E`
and an isomorphism `a : F E ⟶ A₁`, the transpose of
`F (E ⊗ P Rj K) ⟶ F E ⊗ F P Rj K ⟶ A₁ ⊗ Q Lj Rj K ⟶ A₁ ⊗ Q K` is an isomorphism.

All data are variables, so that the lemma can be instantiated by unification with the
components of a concrete Künneth map. -/
lemma isIso_homEquiv_δ_tensorHom_exchangeRight_of_isDualizable {D₂ D₂' : Type*} [Category D₂]
    [Category D₂'] {Lj : D₂ ⥤ D₂'} {Rj : D₂' ⥤ D₂} (adjj : Lj ⊣ Rj) {P : D₂ ⥤ D}
    {Q : D₂' ⥤ C} (θ : P ⋙ F ≅ Lj ⋙ Q) {E : D} (hE : IsDualizable E) {A₁ : C}
    (a : F.obj E ⟶ A₁) (ha : IsIso a) (K : D₂') (hK : IsIso (exchangeRight adjj adj θ)) :
    IsIso (adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F E (P.obj (Rj.obj K)) ≫
      (a ⊗ₘ (θ.hom.app (Rj.obj K) ≫ Q.map (adjj.counit.app K))))) := by
  refine adj.isIso_homEquiv_δ_tensorHom_of_isDualizable hE a ha _ ?_
  have := homEquiv_hom_app_comp_map_counit adjj adj θ K
  exact this ▸ NatIso.isIso_app_of_isIso _ K

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]

/-- The projection morphism `G A ⊗ B ⟶ G (A ⊗ F B)` is the component of the right adjoint
projection map attached to the comonoidal structure `δ` of `F`. -/
lemma projectionMorphism_eq_rightAdjointProjectionMap (A : C) (B : D) :
    adj.projectionMorphism A B =
      ((adj.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app A).app B :=
  rfl

/-- For a strong monoidal left adjoint `F ⊣ G` and an object `B` with a left dual `B'`, the
projection morphism `G A ⊗ B ⟶ G (A ⊗ F B)` is an isomorphism. -/
lemma isIso_projectionMorphism_of_exactPairing (B' B : D) [ExactPairing B' B] (A : C) :
    IsIso (adj.projectionMorphism A B) := by
  rw [projectionMorphism_eq_rightAdjointProjectionMap]
  exact adj.isIso_rightAdjointProjectionMap_app_app_of_exactPairing _ (fun _ _ ↦ rfl) A B' B

/-- For a strong monoidal left adjoint `F ⊣ G` and a dualizable object `B` of a braided
category, the projection morphism `G A ⊗ B ⟶ G (A ⊗ F B)` is an isomorphism. -/
lemma isIso_projectionMorphism_of_isDualizable [BraidedCategory D] {B : D}
    (hB : IsDualizable B) (A : C) :
    IsIso (adj.projectionMorphism A B) := by
  rw [projectionMorphism_eq_rightAdjointProjectionMap]
  exact adj.isIso_rightAdjointProjectionMap_app_app_of_isDualizable _ (fun _ _ ↦ rfl) A hB

end CategoryTheory.Adjunction
