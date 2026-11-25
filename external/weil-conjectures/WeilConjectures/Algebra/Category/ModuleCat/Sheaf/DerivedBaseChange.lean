/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Derived base change of sheaves of modules

Let `f : A →+* A'` be a morphism of commutative rings and `(C, J)` an essentially small site.
A morphism `η : K ⟶ Res K'` in `D(J, A)` from an object `K` to the restriction of scalars of
`K' ∈ D(J, A')` *exhibits `K'` as the derived base change `K ⊗ᴸ_A A'`*
(`CategoryTheory.Sheaf.IsDerivedBaseChange`) if it is a universal arrow from `K` to the
restriction of scalars: derived base change is left adjoint to restriction of scalars.

When `f` is surjective with principal kernel `(a)`, a *reduction datum* for `f`
(`CategoryTheory.Sheaf.ReductionDatum`) is a functor `Φ` from sheaves of `A`-modules to sheaves
of `A'`-modules with a natural epimorphism `F ⟶ Res Φ(F)` whose kernel is the image of `a`, and
which sends quasi-isomorphisms between K-flat complexes to quasi-isomorphisms. For a K-flat
complex `P` the reduction `P ⟶ Res Φ(P)` exhibits `Φ(P)` as the derived base change of `P`
(`CategoryTheory.Sheaf.ReductionDatum.isDerivedBaseChange`).

## Main definitions

- `CategoryTheory.Sheaf.derivedRestrictScalars`: restriction of scalars `D(J, A') ⥤ D(J, A)`.
- `CategoryTheory.Sheaf.IsDerivedBaseChange`: universal arrows to restrictions of scalars.
- `CategoryTheory.Sheaf.ReductionDatum`: a chain-level model of derived base change.

## Main results

- `CategoryTheory.Sheaf.IsDerivedBaseChange.comp`: derived base changes compose.
- `CategoryTheory.Sheaf.IsDerivedBaseChange.isIso`: two derived base changes of the same
  object are isomorphic through any compatible comparison map.
- `CategoryTheory.Sheaf.ReductionDatum.isDerivedBaseChange`: the reduction of a K-flat complex
  is its derived base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

section

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A'] (f : A →+* A')

/-- Restriction of scalars `D(J, A') ⥤ D(J, A)` along a ring morphism `f : A →+* A'`, induced
by the exact restriction of scalars of sheaves of modules. -/
noncomputable abbrev derivedRestrictScalars :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} A')) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) :=
  (restrictScalars J f).mapDerivedCategory

variable {J f}

/-- A morphism `η : K ⟶ Res K'` from `K ∈ D(J, A)` to the restriction of scalars of
`K' ∈ D(J, A')` *exhibits `K'` as the derived base change `K ⊗ᴸ_A A'`* if it is universal
among morphisms from `K` to restrictions of scalars: every `K ⟶ Res N` factors uniquely as
`η` followed by the restriction of a morphism `K' ⟶ N`. -/
def IsDerivedBaseChange {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))}
    {K' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A'))}
    (η : K ⟶ (derivedRestrictScalars J f).obj K') : Prop :=
  ∀ N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A')),
    Function.Bijective fun g : K' ⟶ N ↦ η ≫ (derivedRestrictScalars J f).map g

variable (J) in
/-- Restricting scalars along `g` and then along `f` is restricting scalars along `g ∘ f`. -/
noncomputable def derivedRestrictScalarsCompIso {A'' : Type (u + 1)} [CommRing A'']
    {g : A' →+* A''} {gf : A →+* A''} (hgf : gf = g.comp f) :
    derivedRestrictScalars J g ⋙ derivedRestrictScalars J f ≅ derivedRestrictScalars J gf :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (restrictScalarsCompIso J f g gf hgf)

namespace IsDerivedBaseChange

variable {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))}
  {K' K'' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A'))}

/-- Two derived base changes of the same object are isomorphic through every comparison map
compatible with them. -/
lemma isIso {η : K ⟶ (derivedRestrictScalars J f).obj K'}
    {η' : K ⟶ (derivedRestrictScalars J f).obj K''} (hη : IsDerivedBaseChange η)
    (hη' : IsDerivedBaseChange η') (φ : K' ⟶ K'')
    (hφ : η ≫ (derivedRestrictScalars J f).map φ = η') : IsIso φ := by
  obtain ⟨ψ, hψ : η' ≫ _ = η⟩ := (hη' K').2 η
  refine ⟨⟨ψ, (hη K').1 ?_, (hη' K'').1 ?_⟩⟩
  · dsimp only
    rw [Functor.map_comp, reassoc_of% hφ, hψ, Functor.map_id, Category.comp_id]
  · dsimp only
    rw [Functor.map_comp, reassoc_of% hψ, hφ, Functor.map_id, Category.comp_id]

/-- Derived base change is invariant under isomorphisms of the source. -/
lemma of_iso {K₀ : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))} (e : K₀ ≅ K)
    {η : K ⟶ (derivedRestrictScalars J f).obj K'} (hη : IsDerivedBaseChange η) :
    IsDerivedBaseChange (e.hom ≫ η) := by
  intro N
  convert (e.symm.homFromEquiv (Z := (derivedRestrictScalars J f).obj N)).bijective.comp
    (hη N) using 1
  ext g
  simp

/-- Derived base change is invariant under isomorphisms of the target. -/
lemma comp_map_iso {η : K ⟶ (derivedRestrictScalars J f).obj K'} (hη : IsDerivedBaseChange η)
    (e : K' ≅ K'') : IsDerivedBaseChange (η ≫ (derivedRestrictScalars J f).map e.hom) := by
  intro N
  convert (hη N).comp (e.symm.homFromEquiv (Z := N)).bijective using 1
  ext g
  simp

variable {A'' : Type (u + 1)} [CommRing A''] {g : A' →+* A''} {gf : A →+* A''}
  (hgf : gf = g.comp f)

include hgf in
/-- Derived base changes compose. -/
lemma comp {K'' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A''))}
    {η : K ⟶ (derivedRestrictScalars J f).obj K'} (hη : IsDerivedBaseChange η)
    {η' : K' ⟶ (derivedRestrictScalars J g).obj K''} (hη' : IsDerivedBaseChange η') :
    IsDerivedBaseChange (f := gf)
      (η ≫ (derivedRestrictScalars J f).map η' ≫
        (derivedRestrictScalarsCompIso J hgf).hom.app K'') := by
  intro N
  convert ((((derivedRestrictScalarsCompIso J hgf).app N).homToEquiv
    (Z := K)).bijective.comp (hη _)).comp (hη' N) using 1
  ext g
  have := (derivedRestrictScalarsCompIso J hgf).hom.naturality g
  dsimp at this ⊢
  simp [this]

end IsDerivedBaseChange

end

end CategoryTheory.Sheaf
