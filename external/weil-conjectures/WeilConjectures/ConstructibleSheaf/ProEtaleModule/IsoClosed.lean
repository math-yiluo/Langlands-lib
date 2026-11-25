/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-!

# Constructibility is invariant under isomorphism

The finiteness conditions on module objects over a ring object `R` of pro-étale sheaves
(`Mod.IsFinitelyPresented`, `ProEtale.IsLocallyFinitelyPresented`,
`ProEtale.IsConstructibleModuleObject`) are all defined up to isomorphism; this file records that
they are invariant under isomorphisms, so that the bounded constructible complexes
`ProEtale.boundedConstructible R` are closed under isomorphisms in the derived category.

## Main results

- `ProEtale.IsConstructibleModuleObject.of_iso`: constructibility is invariant under isomorphism.
- `ProEtale.isClosedUnderIsomorphisms_boundedConstructible`: the bounded constructible complexes
  are closed under isomorphisms.

-/

@[expose] public section

universe v u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R]

/-- Being pro-étale locally finitely presented is invariant under isomorphism of module
objects. -/
lemma IsLocallyFinitelyPresented.of_iso {M N : Mod (Sheaf (Scheme.ProEt.topology X) A) R}
    (e : M ≅ N) (h : IsLocallyFinitelyPresented R M) : IsLocallyFinitelyPresented R N := by
  obtain ⟨𝒰, h⟩ := h
  exact ⟨𝒰, fun i ↦
    Mod.IsFinitelyPresented.of_iso (((ProEtale.upperStar A (𝒰.f i)).mapMod R).mapIso e) (h i)⟩

/-- Constructibility of module objects is invariant under isomorphism. -/
lemma IsConstructibleModuleObject.of_iso {M N : Mod (Sheaf (Scheme.ProEt.topology X) A) R}
    (e : M ≅ N) (h : IsConstructibleModuleObject R M) : IsConstructibleModuleObject R N := by
  obtain ⟨S, h⟩ := h
  exact ⟨S, fun a ↦ IsLocallyFinitelyPresented.of_iso
    (((ProEtale.upperStar A (S.immersion a)).mapMod R).mapIso e) (h a)⟩

variable (R) [IsCommMonObj R]

/-- The bounded constructible complexes are closed under isomorphisms in the derived category:
boundedness and the constructibility of the cohomology sheaves are invariant under
isomorphism. -/
instance isClosedUnderIsomorphisms_boundedConstructible :
    (boundedConstructible R).IsClosedUnderIsomorphisms where
  of_iso e h := ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1,
    fun n ↦ (h.2 n).of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e)⟩

end AlgebraicGeometry.ProEtale
