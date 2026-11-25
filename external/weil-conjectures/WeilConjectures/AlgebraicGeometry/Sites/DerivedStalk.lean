/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Conservativity of geometric stalks on the derived category

A morphism `f: K ⟶ L` in the derived category of `A`-valued sheaves on the small étale site
of a scheme `S` is an isomorphism as soon as, for every `i: ℤ` and every geometric point
`s̄` of `S`, the map of geometric stalks `ℋⁱ(K)_s̄ ⟶ ℋⁱ(L)_s̄` is an isomorphism.

## Main statements

- `AlgebraicGeometry.Scheme.isIso_iff_isIso_sheafFiber_map_homologyFunctor_map`: the statement
  on the unbounded derived category.
- `AlgebraicGeometry.Scheme.isIso_iff_isIso_sheafFiber_map_homologyFunctor_map_plus`
: the statement on the bounded below derived
  category.
-/

@[expose] public section

universe w u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {A : Type u'} [Category.{u + 1} A]
  [HasColimitsOfSize.{u + 1, u + 1} A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)} [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [hC : ConcreteCategory.{u + 1} A FC] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  [Abelian (Sheaf S.smallEtaleTopology A)]
  [HasDerivedCategory.{w} (Sheaf S.smallEtaleTopology A)]

include hC hJ in
/-- **Geometric stalks are conservative on the derived category.** A morphism `f : K ⟶ L` of
`D(S_ét, A)` is an isomorphism if and only if the maps of geometric stalks
`ℋⁱ(K)_s̄ ⟶ ℋⁱ(L)_s̄` are isomorphisms for every `i : ℤ` and every point `s` of `S`. -/
lemma isIso_iff_isIso_sheafFiber_map_homologyFunctor_map
    {K L : DerivedCategory (Sheaf S.smallEtaleTopology A)} (f : K ⟶ L) :
    IsIso f ↔ ∀ (i : ℤ) (s : S), IsIso ((S.uliftPointSmallEtale s).sheafFiber.map
      ((DerivedCategory.homologyFunctor _ i).map f)) := by
  rw [DerivedCategory.isIso_iff]
  exact ⟨fun _ _ _ ↦ inferInstance, fun h i ↦ isIso_of_isIso_sheafFiber_map _ (h i)⟩

include hC hJ in
/-- Conservativity of geometric stalks on
the derived category.

A morphism `f: K ⟶ L` of `D⁺(S_ét, A)` is an isomorphism if and only if the maps of geometric
stalks `ℋⁱ(K)_s̄ ⟶ ℋⁱ(L)_s̄` are isomorphisms for every `i: ℤ` and every point `s` of `S`. -/
lemma isIso_iff_isIso_sheafFiber_map_homologyFunctor_map_plus
    {K L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology A)} (f : K ⟶ L) :
    IsIso f ↔ ∀ (i : ℤ) (s : S), IsIso ((S.uliftPointSmallEtale s).sheafFiber.map
      ((DerivedCategory.Plus.homologyFunctor _ i).map f)) := by
  rw [DerivedCategory.Plus.isIso_iff]
  exact ⟨fun _ _ _ ↦ inferInstance, fun h i ↦ isIso_of_isIso_sheafFiber_map _ (h i)⟩

end AlgebraicGeometry.Scheme
