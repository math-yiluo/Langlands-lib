/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Adjunctions with a trace counit

Let `F ⊣ G` be an adjunction between monoidal categories, `F : C ⥤ D` strong monoidal (think
of `q^* ⊣ q_*` for a morphism of schemes `q : P ⟶ S`). The *projection map*
`π_{M, N} : G M ⊗ N ⟶ G (M ⊗ F N)` is the adjoint transpose of
`F (G M ⊗ N) ≅ F G M ⊗ F N ⟶ M ⊗ F N` (`CategoryTheory.Adjunction.monoidalProjection`).

Let `T : D` be an object with `π_{T, N}` invertible for all `N` (the projection formula) and
`t : G T ⟶ 𝟙_ C` a *trace*. The *trace counit* is
`ε_N : G (T ⊗ F N) ≅ G T ⊗ N ⟶ 𝟙_ C ⊗ N ≅ N`
(`CategoryTheory.Adjunction.traceCounit`); for `q : ℙ¹_S ⟶ S`, `T = Λ(1)[2]` and the trace of
`q`, it is the counit of blueprint `proposition-adjunction-projective-line` (G7).

We show that `ε` is the counit of an adjunction `G ⊣ T ⊗ F (-)` as soon as there is a unit
candidate `η_M : M ⟶ T ⊗ F G M` which is

* *linear*: `η_{M ⊗ F N}` is `η_M ⊗ F N` followed by `F G M ⊗ F N ≅ F (G M ⊗ N) ⟶ F G (M ⊗ F N)`
  (the projection map), and
* *normalized* at the unit and at `T`: `ε_{G 𝟙} ∘ G η_𝟙 = 1` and
  `T ≅ T ⊗ 𝟙 ⟵ T ⊗ F 𝟙 ⟵ T ⊗ F G T ⟵ T` (`t` after `η_T`) is the identity
  (`CategoryTheory.Adjunction.ofTraceCounit`).

These are the two "integrals" of blueprint `proposition-adjunction-projective-line` (G5): for the
unit built from the cycle class `δ` of the diagonal, `G η_𝟙` and `η_T` are the integrals of `δ`
along the two projections, and linearity reduces the triangle identities to them, as in (G8) and
(G9).

The first triangle identity is checked on the objects `𝟙 ⊗ F N`, which is enough since
`G (𝟙 ⊗ F G M) ⟶ G M` is a split epimorphism
(`CategoryTheory.Adjunction.monoidalProjection_unit_section`).

## Main definitions
- `CategoryTheory.Adjunction.monoidalProjection`
- `CategoryTheory.Adjunction.traceCounit`
- `CategoryTheory.Adjunction.ofTraceCounit`

## Main statements
- `CategoryTheory.Adjunction.ofTraceCounit_counit`
- `CategoryTheory.Adjunction.map_unit_app_comp_traceCounit` and
  `CategoryTheory.Adjunction.unit_app_tensor_comp_map_traceCounit`: the triangle identities
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G)

/-- The *projection map* `π_{M, N} : G M ⊗ N ⟶ G (M ⊗ F N)` of an adjunction `F ⊣ G` with
monoidal left adjoint: the adjoint transpose of `F (G M ⊗ N) ≅ F G M ⊗ F N ⟶ M ⊗ F N`. -/
noncomputable def monoidalProjection (M : D) (N : C) : G.obj M ⊗ N ⟶ G.obj (M ⊗ F.obj N) :=
  adj.homEquiv _ _ (δ F (G.obj M) N ≫ adj.counit.app M ▷ F.obj N)

lemma homEquiv_symm_monoidalProjection (M : D) (N : C) :
    (adj.homEquiv _ _).symm (adj.monoidalProjection M N) =
      δ F (G.obj M) N ≫ adj.counit.app M ▷ F.obj N :=
  Equiv.symm_apply_apply _ _

@[reassoc]
lemma map_monoidalProjection_counit (M : D) (N : C) :
    F.map (adj.monoidalProjection M N) ≫ adj.counit.app _ =
      δ F (G.obj M) N ≫ adj.counit.app M ▷ F.obj N := by
  rw [← homEquiv_symm_monoidalProjection, homEquiv_counit]

/-- Naturality of the projection map in the first variable. -/
@[reassoc]
lemma monoidalProjection_naturality_left {M M' : D} (f : M ⟶ M') (N : C) :
    G.map f ▷ N ≫ adj.monoidalProjection M' N =
      adj.monoidalProjection M N ≫ G.map (f ▷ F.obj N) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, map_monoidalProjection_counit]
  simp only [counit_naturality, Functor.id_obj,
    map_monoidalProjection_counit_assoc]
  rw [← δ_natural_left_assoc, ← comp_whiskerRight, counit_naturality, comp_whiskerRight]

/-- Naturality of the projection map in the second variable. -/
@[reassoc]
lemma monoidalProjection_naturality_right (M : D) {N N' : C} (g : N ⟶ N') :
    G.obj M ◁ g ≫ adj.monoidalProjection M N' =
      adj.monoidalProjection M N ≫ G.map (M ◁ F.map g) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, map_monoidalProjection_counit]
  rw [← δ_natural_right_assoc]
  simp [whisker_exchange, map_monoidalProjection_counit_assoc]

/-- Associativity of the projection map. -/
@[reassoc]
lemma monoidalProjection_assoc (M : D) (N N' : C) :
    adj.monoidalProjection M N ▷ N' ≫ adj.monoidalProjection (M ⊗ F.obj N) N' ≫
        G.map ((α_ _ _ _).hom ≫ M ◁ μ F N N') =
      (α_ _ _ _).hom ≫ adj.monoidalProjection M (N ⊗ N') := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, map_monoidalProjection_counit,
    Functor.Monoidal.map_associator, Functor.Monoidal.μ_δ_assoc, Functor.id_obj]
  simp only [counit_naturality, counit_naturality_assoc]
  rw [map_monoidalProjection_counit_assoc, ← δ_natural_left_assoc, ← comp_whiskerRight_assoc,
    map_monoidalProjection_counit]
  simp only [comp_whiskerRight, assoc, whisker_exchange]
  erw [associator_naturality_left_assoc]
  rfl

/-- The projection map at `𝟙_ D` is split by the unit: the composite
`G M ≅ 𝟙 ⊗ G M ⟶ G 𝟙 ⊗ G M ⟶ G (𝟙 ⊗ F G M) ⟶ G (F G M) ⟶ G M` is the identity. -/
@[reassoc]
lemma monoidalProjection_unit_section (M : D) :
    (λ_ (G.obj M)).inv ≫ (adj.unit.app (𝟙_ C) ≫ G.map (η F)) ▷ G.obj M ≫
        adj.monoidalProjection (𝟙_ D) (G.obj M) ≫
          G.map ((λ_ (F.obj (G.obj M))).hom ≫ adj.counit.app M) = 𝟙 _ := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, Functor.map_id, id_comp,
    Functor.Monoidal.map_leftUnitor_inv]
  simp only [counit_naturality, counit_naturality_assoc, Functor.id_obj]
  rw [map_monoidalProjection_counit_assoc, ← δ_natural_left_assoc, Functor.Monoidal.μ_δ_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  simp

section TraceCounit

variable (T : D) (t : G.obj T ⟶ 𝟙_ C) [∀ N, IsIso (adj.monoidalProjection T N)]

/-- The *trace counit* `ε_N : G (T ⊗ F N) ≅ G T ⊗ N ⟶ 𝟙 ⊗ N ≅ N` of a trace `t : G T ⟶ 𝟙`,
for an object `T` satisfying the projection formula. -/
@[simps]
noncomputable def traceCounit : (F ⋙ tensorLeft T) ⋙ G ⟶ 𝟭 C where
  app N := inv (adj.monoidalProjection T N) ≫ t ▷ N ≫ (λ_ N).hom
  naturality N N' g := by
    dsimp
    rw [← cancel_epi (adj.monoidalProjection T N)]
    simp only [assoc, IsIso.hom_inv_id_assoc]
    rw [← adj.monoidalProjection_naturality_right_assoc, IsIso.hom_inv_id_assoc,
      whisker_exchange_assoc, leftUnitor_naturality]

variable {adj T t}

/-- The second triangle identity, from linearity and the normalization at `T`. -/
lemma unit_app_tensor_comp_map_traceCounit (u : 𝟭 D ⟶ G ⋙ F ⋙ tensorLeft T)
    (hlin : ∀ (M : D) (N : C), u.app (M ⊗ F.obj N) =
      u.app M ▷ F.obj N ≫ (α_ _ _ _).hom ≫ T ◁ (μ F (G.obj M) N ≫
        F.map (adj.monoidalProjection M N)))
    (h₂ : u.app T ≫ T ◁ (F.map t ≫ η F) ≫ (ρ_ T).hom = 𝟙 T) (N : C) :
    u.app (T ⊗ F.obj N) ≫ T ◁ F.map ((adj.traceCounit T t).app N) = 𝟙 _ := by
  rw [hlin, traceCounit_app]
  simp only [assoc, ← whiskerLeft_comp, Functor.map_comp, Functor.map_inv,
    IsIso.hom_inv_id_assoc]
  rw [← μ_natural_left_assoc, Functor.Monoidal.map_leftUnitor F N, Functor.Monoidal.μ_δ_assoc]
  simp only [whiskerLeft_comp, ← associator_naturality_middle_assoc, triangle]
  simp only [← comp_whiskerRight]
  simp only [whiskerLeft_comp, assoc] at h₂
  rw [h₂]
  simp

/-- The first triangle identity on the objects `𝟙 ⊗ F N`, precomposed with the projection
map, from linearity and the normalization at the unit. -/
@[reassoc]
lemma monoidalProjection_comp_map_unit_app_comp_traceCounit (u : 𝟭 D ⟶ G ⋙ F ⋙ tensorLeft T)
    (hlin : ∀ (M : D) (N : C), u.app (M ⊗ F.obj N) =
      u.app M ▷ F.obj N ≫ (α_ _ _ _).hom ≫ T ◁ (μ F (G.obj M) N ≫
        F.map (adj.monoidalProjection M N)))
    (h₁ : G.map (u.app (𝟙_ D)) ≫ (adj.traceCounit T t).app (G.obj (𝟙_ D)) = 𝟙 _) (N : C) :
    adj.monoidalProjection (𝟙_ D) N ≫ G.map (u.app (𝟙_ D ⊗ F.obj N)) ≫
        (adj.traceCounit T t).app (G.obj (𝟙_ D ⊗ F.obj N)) =
      adj.monoidalProjection (𝟙_ D) N := by
  have hα : adj.monoidalProjection (T ⊗ F.obj (G.obj (𝟙_ D))) N ≫ G.map (α_ _ _ _).hom ≫
      G.map (T ◁ μ F (G.obj (𝟙_ D)) N) =
        inv (adj.monoidalProjection T (G.obj (𝟙_ D))) ▷ N ≫ (α_ _ _ _).hom ≫
          adj.monoidalProjection T (G.obj (𝟙_ D) ⊗ N) := by
    rw [← cancel_epi (adj.monoidalProjection T (G.obj (𝟙_ D)) ▷ N), ← Functor.map_comp,
      monoidalProjection_assoc, ← comp_whiskerRight_assoc, IsIso.hom_inv_id, id_whiskerRight,
      id_comp]
  rw [hlin, traceCounit_app]
  simp only [Functor.map_comp, whiskerLeft_comp, assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj, curriedTensor_obj_obj]
  rw [← monoidalProjection_naturality_left_assoc, reassoc_of% hα,
    ← monoidalProjection_naturality_right_assoc, IsIso.hom_inv_id_assoc, whisker_exchange_assoc,
    leftUnitor_naturality, ← associator_naturality_left_assoc, leftUnitor_tensor_hom, assoc,
    Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc]
  rw [traceCounit_app] at h₁
  simp only [assoc]
  rw [h₁]
  simp

/-- The first triangle identity, from linearity and the normalization at the unit. -/
lemma map_unit_app_comp_traceCounit (u : 𝟭 D ⟶ G ⋙ F ⋙ tensorLeft T)
    (hlin : ∀ (M : D) (N : C), u.app (M ⊗ F.obj N) =
      u.app M ▷ F.obj N ≫ (α_ _ _ _).hom ≫ T ◁ (μ F (G.obj M) N ≫
        F.map (adj.monoidalProjection M N)))
    (h₁ : G.map (u.app (𝟙_ D)) ≫ (adj.traceCounit T t).app (G.obj (𝟙_ D)) = 𝟙 _) (M : D) :
    G.map (u.app M) ≫ (adj.traceCounit T t).app (G.obj M) = 𝟙 _ := by
  set g := (λ_ (F.obj (G.obj M))).hom ≫ adj.counit.app M
  have hu := u.naturality g
  have hε := (adj.traceCounit T t).naturality (G.map g)
  dsimp at hu hε
  have hs := adj.monoidalProjection_unit_section M
  calc G.map (u.app M) ≫ (adj.traceCounit T t).app (G.obj M)
      = ((λ_ (G.obj M)).inv ≫ (adj.unit.app (𝟙_ C) ≫ G.map (η F)) ▷ G.obj M ≫
          adj.monoidalProjection (𝟙_ D) (G.obj M) ≫ G.map g) ≫ G.map (u.app M) ≫
            (adj.traceCounit T t).app (G.obj M) := by rw [hs, id_comp]
    _ = (λ_ (G.obj M)).inv ≫ (adj.unit.app (𝟙_ C) ≫ G.map (η F)) ▷ G.obj M ≫
          adj.monoidalProjection (𝟙_ D) (G.obj M) ≫ G.map g := by
      simp only [assoc]
      rw [← Functor.map_comp_assoc, hu, Functor.map_comp_assoc, hε,
        monoidalProjection_comp_map_unit_app_comp_traceCounit_assoc u hlin h₁]
    _ = 𝟙 _ := hs

/-- **Adjunction with a trace counit.** For an adjunction `F ⊣ G` with `F` strong monoidal, an
object `T` satisfying the projection formula and a trace `t : G T ⟶ 𝟙`, a linear unit candidate
`u : M ⟶ T ⊗ F G M` normalized at `𝟙` and at `T` makes `G` left adjoint to `T ⊗ F (-)`, with
unit `u` and counit the trace counit `CategoryTheory.Adjunction.traceCounit`. -/
noncomputable def ofTraceCounit (u : 𝟭 D ⟶ G ⋙ F ⋙ tensorLeft T)
    (hlin : ∀ (M : D) (N : C), u.app (M ⊗ F.obj N) =
      u.app M ▷ F.obj N ≫ (α_ _ _ _).hom ≫ T ◁ (μ F (G.obj M) N ≫
        F.map (adj.monoidalProjection M N)))
    (h₁ : G.map (u.app (𝟙_ D)) ≫ (adj.traceCounit T t).app (G.obj (𝟙_ D)) = 𝟙 _)
    (h₂ : u.app T ≫ T ◁ (F.map t ≫ η F) ≫ (ρ_ T).hom = 𝟙 T) :
    G ⊣ F ⋙ tensorLeft T :=
  Adjunction.mkOfUnitCounit
    { unit := u
      counit := adj.traceCounit T t
      left_triangle := by
        ext M
        simpa using map_unit_app_comp_traceCounit u hlin h₁ M
      right_triangle := by
        ext N
        simpa using unit_app_tensor_comp_map_traceCounit u hlin h₂ N }

@[simp]
lemma ofTraceCounit_unit (u : 𝟭 D ⟶ G ⋙ F ⋙ tensorLeft T)
    (hlin : ∀ (M : D) (N : C), u.app (M ⊗ F.obj N) =
      u.app M ▷ F.obj N ≫ (α_ _ _ _).hom ≫ T ◁ (μ F (G.obj M) N ≫
        F.map (adj.monoidalProjection M N)))
    (h₁ : G.map (u.app (𝟙_ D)) ≫ (adj.traceCounit T t).app (G.obj (𝟙_ D)) = 𝟙 _)
    (h₂ : u.app T ≫ T ◁ (F.map t ≫ η F) ≫ (ρ_ T).hom = 𝟙 T) :
    (ofTraceCounit u hlin h₁ h₂).unit = u :=
  rfl

@[simp]
lemma ofTraceCounit_counit (u : 𝟭 D ⟶ G ⋙ F ⋙ tensorLeft T)
    (hlin : ∀ (M : D) (N : C), u.app (M ⊗ F.obj N) =
      u.app M ▷ F.obj N ≫ (α_ _ _ _).hom ≫ T ◁ (μ F (G.obj M) N ≫
        F.map (adj.monoidalProjection M N)))
    (h₁ : G.map (u.app (𝟙_ D)) ≫ (adj.traceCounit T t).app (G.obj (𝟙_ D)) = 𝟙 _)
    (h₂ : u.app T ≫ T ◁ (F.map t ≫ η F) ≫ (ρ_ T).hom = 𝟙 T) :
    (ofTraceCounit u hlin h₁ h₂).counit = adj.traceCounit T t :=
  rfl

end TraceCounit

end CategoryTheory.Adjunction
