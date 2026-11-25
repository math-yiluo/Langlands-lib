/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointBijective
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Localization

/-!
# Lifting a right adjoint of a right derived functor to algebras

Let `F` and `G` be exact autoequivalences of Grothendieck abelian categories `C` and `D`, and let
`L : C ⥤ D` be an additive functor with `e : L ⋙ G ≅ F ⋙ L`, so that `L` lifts to
`IsoAlgebra.mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G`. In the `ℓ`-adic formalism `F`, `G` are
the Frobenius pullbacks on the geometric fibres, `IsoAlgebra F` is the category of pro-étale Weil
sheaves and `L` is the pushforward along `ḡ : Z̄ ⟶ Ȳ`.

Suppose that the total right derived functor `RL` restricts to full subcategories `P_C ⊆ D(C)`,
`P_D ⊆ D(D)` of bounded objects (bounded constructible complexes), that the restriction has a
right adjoint (`Rḡ_* ⊣ ḡ^!` on `Dᵇc`), and that `RL` commutes with `ℤ`-indexed coproducts of
uniformly bounded below objects. Then the total right derived functor of `mapOfNatIso e`,
restricted to the objects whose underlying object lies in `P_C` (the Weil complexes), is a left
adjoint
(`CategoryTheory.Endofunctor.IsoAlgebra.isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor`).

## Proof

For `L' ∈ P_D` lifted to the algebras, `ḡ^! (U L')` carries the Weil structure mate of
`RL ∘ F ≅ G ∘ RL`, and it is realized as an object `H` of `D(IsoAlgebra F)`
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_cyclicDerivedActionRealization`). The counit
`RL (ḡ^! U L') ⟶ U L'` is equivariant, hence it lifts to `d : R(mapOfNatIso e) H ⟶ L'`. That
`u ↦ R(mapOfNatIso e) u ≫ d` is bijective follows from the five lemma applied to the free
resolution triangle `Free U M ⟶ Free U M ⟶ M ⟶` of the source
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_freeDerivedWeilResolution`): on the free terms
the map is the adjunction bijection of `RL ⊣ ḡ^!`, as `R(mapOfNatIso e)` commutes with the free
functor on bounded objects (this is where coproducts are used).
-/

@[expose] public section

universe v v'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category.{v} C] [Abelian C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions C]

/-- **Lifting the right adjoint of a right derived functor to algebras.** Let `P_C ⊆ D(C)` be a
property of bounded objects closed under isomorphisms and shifts, and `P_D ⊆ D(D)` one closed
under isomorphisms, with `RL` mapping `P_C` into `P_D`, `P_C` stable under `F` and `F⁻¹` and
`P_D` stable under `G` (on derived categories). Let `P_C^W`, `P_D^W` be the properties of objects
of the derived categories of algebras whose underlying object satisfies `P_C`, resp. `P_D`. If
the restriction `RL : P_C ⥤ P_D` is a left adjoint and `RL` preserves `ℤ`-indexed coproducts of
uniformly bounded below objects, then the restriction `R(mapOfNatIso e) : P_C^W ⥤ P_D^W` is a
left adjoint. -/
theorem isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
    (PC : ObjectProperty (DerivedCategory C)) (PD : ObjectProperty (DerivedCategory D))
    [PC.IsClosedUnderIsomorphisms] [PD.IsClosedUnderIsomorphisms]
    (hPC : ∀ K, PC K → DerivedCategory.TStructure.t.bounded K)
    (hPC_shift : ∀ (K : DerivedCategory C) (n : ℤ), PC K → PC (K⟦n⟧))
    (hPC_F : ∀ K, PC (F.mapDerivedCategory.obj K) ↔ PC K)
    (hPD_G : ∀ K, PD K → PD (G.mapDerivedCategory.obj K))
    (hR : ∀ K, PC K → PD (L.rightDerivedFunctor.obj K))
    (hadj : (PC.liftFullSubcategory PD L.rightDerivedFunctor hR).IsLeftAdjoint)
    (hcoprod : ∀ (X : ℤ → DerivedCategory C) (a : ℤ), (∀ n, (X n).IsGE a) →
      PreservesColimit (Discrete.functor X) L.rightDerivedFunctor)
    (PCW : ObjectProperty (DerivedCategory (IsoAlgebra F)))
    (PDW : ObjectProperty (DerivedCategory (IsoAlgebra G)))
    (hPCW : ∀ M, PCW M ↔ PC ((forget F).mapDerivedCategory.obj M))
    (hPDW : ∀ M, PDW M ↔ PD ((forget G).mapDerivedCategory.obj M))
    (hRW : ∀ M, PCW M → PDW ((mapOfNatIso e).rightDerivedFunctor.obj M)) :
    (PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW).IsLeftAdjoint := by
  have := hadj
  suffices h : ∀ L'' : PDW.FullSubcategory, ∃ (X : PCW.FullSubcategory)
      (d : (PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW).obj X ⟶ L''),
      ∀ M, Function.Bijective (fun u : M ⟶ X ↦
        (PCW.liftFullSubcategory PDW (mapOfNatIso e).rightDerivedFunctor hRW).map u ≫ d) by
    choose X d hd using h
    exact Functor.isLeftAdjoint_of_bijective _ d fun Y W ↦ hd Y W
  intro L''
  obtain ⟨H, hH, -, d, hd⟩ := exists_bijective_rightDerivedFunctor_map_comp_free e PC PD hPC hR
    (Adjunction.ofIsLeftAdjoint (PC.liftFullSubcategory PD L.rightDerivedFunctor hR)) hPC_F hPD_G
    hcoprod L''.obj ((hPDW _).1 L''.property)
  refine ⟨⟨H, (hPCW H).2 hH⟩, ObjectProperty.homMk d, fun M ↦ ?_⟩
  have hb := bijective_rightDerivedFunctor_map_comp e PC hPC_shift d hd M.obj
    ((hPCW _).1 M.property)
  refine ⟨fun u u' h ↦ ObjectProperty.hom_ext _ (hb.1 (congrArg InducedCategory.Hom.hom h)),
    fun y ↦ ?_⟩
  obtain ⟨u, hu⟩ := hb.2 y.hom
  exact ⟨ObjectProperty.homMk u, ObjectProperty.hom_ext _ hu⟩

end CategoryTheory.Endofunctor.IsoAlgebra
