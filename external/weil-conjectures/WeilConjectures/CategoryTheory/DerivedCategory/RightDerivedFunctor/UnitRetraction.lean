/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat

/-!
# Retractions of the unbounded derived unit

Let `adj : f ⊣ g` be an adjunction between abelian categories, with `f` exact and `g` left
exact, and consider the unbounded derived adjunction
`adj.derivedAdjunction : f.leftDerivedFunctor ⊣ g.rightDerivedFunctor`.

Let `K` be a bounded below complex such that every `f(Kⁿ)` is `g`-acyclic. Then `g(f(K))`
computes `Rg(Lf(K))`, and under this identification the derived unit at `K` is the levelwise
unit `K ⟶ g(f(K))` of `adj`. Consequently, a retraction `t : g(f(K)) ⟶ K` of the levelwise unit,
as a morphism of complexes, induces a retraction of the derived unit at `K`.

## Main results

- `CategoryTheory.Adjunction.derivedUnitIso`: the isomorphism `g(f(K)) ≅ Rg(Lf(K))`.
- `CategoryTheory.Adjunction.Q_map_unit_comp_derivedUnitIso_hom`: under this isomorphism, the
  derived unit at `K` is the levelwise unit of `adj`.
- `CategoryTheory.Adjunction.derivedUnitRetraction`: the retraction of the derived unit induced by
  a retraction `t` of the levelwise unit.
- `CategoryTheory.Adjunction.isSplitMono_derivedAdjunction_unit_app_of_retraction`: the derived
  unit at `K` is then a split monomorphism.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]

/-- The unit of the derived adjunction on the image `Qh(X)` of an object `X` of the homotopy
category is the unit of `adj` followed by the unit of the right derived functor of `g`, modulo
the counit of the left derived functor of `f`, i.e. the square
```
      Qh(X)  ──── η_{Qh(X)} ────→  Rg(Lf(Qh(X)))
        │                               │
  Qh(adj.unit_X)                   Rg(ε_X)
        ↓                               ↓
   Qh(g(f(X))) ── unit of Rg ──→   Rg(Qh(f(X)))
```
commutes, where `η` is the unit of the derived adjunction and `ε` the counit of `Lf`. -/
@[reassoc]
theorem derivedAdjunction_unit_app_Qh_fac (adj : f ⊣ g)
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    adj.derivedAdjunction.unit.app (DerivedCategory.Qh.obj X) ≫
        g.rightDerivedFunctor.map (f.leftDerivedFunctorCounit.app X) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app X) ≫
        g.rightDerivedFunctorUnit.app ((f.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) :=
  adj.mapHomotopyCategory (ComplexShape.up ℤ) |>.derivedη_fac_app
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f.leftDerivedFunctorCounit
    g.rightDerivedFunctorUnit X

variable [EnoughInjectives D] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g]
  (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
  (hK : ∀ n, g.rightAcyclic (f.obj (K.X n)))

/-- For a bounded below complex `K` such that every `f(Kⁿ)` is `g`-acyclic, the isomorphism
`g(f(K)) ≅ Rg(Lf(K))` in the derived category: it is given by the unit of the right derived
functor of `g` at `f(K)` and the counit of the left derived functor of the exact functor `f`. -/
noncomputable def derivedUnitIso :
    DerivedCategory.Q.obj ((g.mapHomologicalComplex _).obj ((f.mapHomologicalComplex _).obj K)) ≅
      g.rightDerivedFunctor.obj (f.leftDerivedFunctor.obj (DerivedCategory.Q.obj K)) :=
  have := g.isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE
    ((f.mapHomologicalComplex _).obj K) a hK
  ((DerivedCategory.quotientCompQhIso C).app _).symm ≪≫
    asIso (g.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D _).obj ((f.mapHomologicalComplex _).obj K))) ≪≫
    g.rightDerivedFunctor.mapIso
      ((asIso (f.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient C _).obj K))).symm ≪≫
        f.leftDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso C).app K))

/-- Under the isomorphism `Adjunction.derivedUnitIso : g(f(K)) ≅ Rg(Lf(K))`, the unit of the
derived adjunction at `K` is the levelwise unit `K ⟶ g(f(K))` of `adj`:
```
   Q(K) ── Q(adj.unit_K) ──→ Q(g(f(K)))
      ╲                          │
       η_{Q(K)}          derivedUnitIso.hom
          ╲                      ↓
           ╰──────────→   Rg(Lf(Q(K)))
```
-/
@[reassoc]
theorem Q_map_unit_comp_derivedUnitIso_hom (adj : f ⊣ g) :
    DerivedCategory.Q.map ((adj.mapHomologicalComplex _).unit.app K) ≫
        (derivedUnitIso K a hK).hom =
      adj.derivedAdjunction.unit.app (DerivedCategory.Q.obj K) := by
  have h₁ := DerivedCategory.quotientCompQhIso_inv_naturality
    ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K)
  have h₂ := adj.derivedAdjunction.unit.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at h₂
  have h₃ : DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K)) ≫
      g.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient D _).obj ((f.mapHomologicalComplex _).obj K)) =
      adj.derivedAdjunction.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C _).obj K)) ≫
        g.rightDerivedFunctor.map
          (f.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient C _).obj K)) := by
    rw [← mapHomotopyCategory_unit_app_quotient]
    exact (derivedAdjunction_unit_app_Qh_fac adj _).symm
  simp only [derivedUnitIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, asIso_hom,
    Functor.mapIso_hom, Iso.app_hom, asIso_inv, Functor.map_comp]
  rw [reassoc_of% h₁, reassoc_of% h₃, ← Functor.map_comp_assoc,
    IsIso.hom_inv_id, Functor.map_id, Category.id_comp]
  exact (Iso.inv_comp_eq ((DerivedCategory.quotientCompQhIso C).app K)).2 h₂.symm

variable (t : (g.mapHomologicalComplex _).obj ((f.mapHomologicalComplex _).obj K) ⟶ K)

/-- The morphism `Rg(Lf(K)) ⟶ K` in the derived category induced by a morphism of complexes
`t : g(f(K)) ⟶ K` via the isomorphism `Adjunction.derivedUnitIso : g(f(K)) ≅ Rg(Lf(K))`. When `t`
is a retraction of the levelwise unit of the adjunction, this is a retraction of the derived unit
(`Adjunction.derivedAdjunction_unit_app_comp_derivedUnitRetraction`). -/
noncomputable def derivedUnitRetraction :
    g.rightDerivedFunctor.obj (f.leftDerivedFunctor.obj (DerivedCategory.Q.obj K)) ⟶
      DerivedCategory.Q.obj K :=
  (derivedUnitIso K a hK).inv ≫ DerivedCategory.Q.map t

/-- A retraction `t` of the levelwise unit `K ⟶ g(f(K))` induces a retraction
`Adjunction.derivedUnitRetraction` of the unit of the derived adjunction at `K`. -/
@[reassoc]
theorem derivedAdjunction_unit_app_comp_derivedUnitRetraction (adj : f ⊣ g)
    (ht : (adj.mapHomologicalComplex _).unit.app K ≫ t = 𝟙 K) :
    adj.derivedAdjunction.unit.app (DerivedCategory.Q.obj K) ≫
        derivedUnitRetraction K a hK t = 𝟙 _ := by
  rw [← Q_map_unit_comp_derivedUnitIso_hom K a hK adj, derivedUnitRetraction, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, ht]
  exact Functor.map_id _ _

/-- The composite of `Adjunction.derivedUnitRetraction` with the unit of the derived adjunction
at `K` is, via `Adjunction.derivedUnitIso`, the composite of `t` with the levelwise unit. -/
@[reassoc]
theorem derivedUnitRetraction_comp_derivedAdjunction_unit_app (adj : f ⊣ g) :
    derivedUnitRetraction K a hK t ≫ adj.derivedAdjunction.unit.app (DerivedCategory.Q.obj K) =
      (derivedUnitIso K a hK).inv ≫
        DerivedCategory.Q.map (t ≫ (adj.mapHomologicalComplex _).unit.app K) ≫
          (derivedUnitIso K a hK).hom := by
  rw [← Q_map_unit_comp_derivedUnitIso_hom K a hK adj, derivedUnitRetraction, Functor.map_comp,
    Category.assoc, Category.assoc]

/-- If the levelwise unit `K ⟶ g(f(K))` of `adj` admits a retraction as a morphism of complexes,
where `K` is a bounded below complex such that every `f(Kⁿ)` is `g`-acyclic, then the unit of the
derived adjunction at `K` is a split monomorphism. -/
theorem isSplitMono_derivedAdjunction_unit_app_of_retraction (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, g.rightAcyclic (f.obj (K.X n))) (adj : f ⊣ g)
    (ht : (adj.mapHomologicalComplex _).unit.app K ≫ t = 𝟙 K) :
    IsSplitMono (adj.derivedAdjunction.unit.app (DerivedCategory.Q.obj K)) :=
  IsSplitMono.mk' ⟨_, derivedAdjunction_unit_app_comp_derivedUnitRetraction K a hK t adj ht⟩

end Adjunction

end CategoryTheory
