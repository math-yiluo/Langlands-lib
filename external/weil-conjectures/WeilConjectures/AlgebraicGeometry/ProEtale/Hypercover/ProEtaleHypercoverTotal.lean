/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Total sections of an augmented pro-etale simplicial object

## References

* Stacks Project, Tag 09A2

## Implementation details

`hypercoverTotal` forms section rows for each coefficient degree, flips the bicomplex so that
simplicial degree is first, and takes Mathlib's (coproduct) signed total complex. For
coefficients supported in degrees at least `N`, only `0 ≤ p ≤ r - N` contribute in total
degree `r`, so every effective diagonal is finite.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The functor-category preadditive structure on cosimplicial modules. -/
instance cosimplicialModulePreadditive (A : Type (u + 1)) [Ring A] :
    Preadditive (CosimplicialObject (ModuleCat.{u + 1} A)) :=
  inferInstanceAs (Preadditive (SimplexCategory ⥤ ModuleCat.{u + 1} A))

/-- Sections on the simplices, as a cosimplicial module over the augmentation ring.
Restriction to the slice makes its identity object terminal, so all section modules
have scalars in `R(W)` and all face restrictions are linear over that ring. -/
noncomputable def hypercoverSections (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) :
    ringedSiteModules.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
      CosimplicialObject (ModuleCat.{u + 1}
        (((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj (op W))) :=
  SheafOfModules.forget.{u + 1}
      ((sheafCompose (topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⋙
    PresheafOfModules.pushforward₀ (Over.forget W) _ ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op (Over.mk (𝟙 W)))
      Over.mkIdTerminal.op ⋙
    (Functor.whiskeringLeft _ _ _).obj U.rightOp

/-- The section functor is additive. -/
theorem hypercoverSections_additive (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) : (hypercoverSections X R W U).Additive := by
  constructor
  intro M N f g
  ext n x
  rfl

attribute [instance] hypercoverSections_additive

/-- Alternating coface sums preserve addition on coefficient morphisms. -/
theorem alternatingCofaceMapComplex_additive
    (A : Type (u + 1)) [Ring A] :
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u + 1} A)).Additive := by
  constructor
  intro M N f g
  ext n
  rfl

attribute [instance] alternatingCofaceMapComplex_additive

/-- The nonnegative alternating section complex, extended by zero to negative degrees.
Its degree `p` differential is the sum of `(-1)^j` times the face restrictions. -/
noncomputable def hypercoverSectionRows (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) :=
  hypercoverSections X R W U ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _ ⋙
    ComplexShape.embeddingUpNat.extendFunctor _

/-- Additivity of the alternating section complex. -/
theorem hypercoverSectionRows_additive (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) : (hypercoverSectionRows X R W U).Additive := by
  unfold hypercoverSectionRows
  infer_instance

attribute [instance] hypercoverSectionRows_additive

/-- The total section functor with differential `delta + (-1)^p d`: the signed total
complex of the section bicomplex, with simplicial degree first. -/
noncomputable def hypercoverTotal (X : Scheme.{u})
    (R : Sheaf (topology X) CommRingCat.{u + 1}) (W : X.ProEt)
    (U : SimplicialObject (Over W)) :=
  (hypercoverSectionRows X R W U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.totalFunctor _ _ _ (ComplexShape.up ℤ)

end AlgebraicGeometry.Scheme.ProEt
