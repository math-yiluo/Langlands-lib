/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.MixedGlobalExtension
public import WeilConjectures.AlgebraicGeometry.Cohomology.DerivedGlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift

/-!
# Derived extension of global scalars along a flat morphism

For a flat morphism `g : T ⟶ S` of affine schemes, extension of scalars along
`g^♯ : Γ(S, ⊤) → Γ(T, ⊤)` is exact, and the functor it induces on derived categories is the
derived extension of scalars `AlgebraicGeometry.mixedGlobalExtension g`: both are left adjoint
to the derived restriction of scalars.
-/

@[expose] public section

universe wA u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- For flat `g` between affine schemes, the derived extension of global scalars is induced by the
exact functor `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} -`. -/
noncomputable def mixedGlobalExtensionIsoOfFlat {T S : Scheme.{u}} [IsAffine S] [IsAffine T]
    (g : T ⟶ S) [Flat g] :
    mixedGlobalExtension g ≅ (ModuleCat.extendScalars.{u, u, u} g.appTop.hom).mapDerivedCategory :=
  (mixedGlobalExtensionAdjunction g).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} g.appTop.hom).mapDerivedCategoryAdjunction

end AlgebraicGeometry
