/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat

import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
# Flat sheaves of modules with independent universes

Source: Stacks Project, Modules on Sites, Definition 03ER, item (3)
(auxiliary; not a blueprint node).

The blueprint node `def-pc-flat-sheaf-modules` is `SheafOfModules.IsFlat`, which needs the
site and the coefficients in one universe. `SheafOfModules.IsFlatOnSite` is the same notion
for independent site-object, site-morphism, coefficient and module universes. Its tensor
functor is `siteSheafTensorRight`, the sheafification of the sectionwise balanced tensor
product. When the universes agree, the two predicates are equivalent
(`SheafOfModules.isFlatOnSite_iff_isFlat`).
-/

@[expose] public section

universe uC vC r m

open CategoryTheory MonoidalCategory

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  {R : Sheaf J CommRingCat.{r}}

/-- A sheaf of modules `F` over a sheaf of commutative rings `R` is *flat* when the functor
`G ↦ G ⊗_R F` on sheaves of `R`-modules (the sheafified sectionwise tensor product
`siteSheafTensorRight`) is exact: it preserves finite limits and finite colimits. The
sheafification instance arguments on the site provide the sheafification of presheaves of
modules, hence the abelian category `Mod(R)`. This is `SheafOfModules.IsFlat` with independent
universes, see `SheafOfModules.isFlatOnSite_iff_isFlat`.
Source: Stacks Project, Tag 03ER, item (3) (auxiliary; not a blueprint node). -/
def IsFlatOnSite
    (F : SheafOfModules.{m} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :
    Prop :=
  exactFunctor _ _ (siteSheafTensorRight F)

end SheafOfModules

namespace SheafOfModules

/-- When the site and the coefficients live in one universe, `IsFlatOnSite` agrees with
`SheafOfModules.IsFlat`, the formalisation of `def-pc-flat-sheaf-modules`
(auxiliary; not a blueprint node).

Proof: `siteSheafTensorRightIso` identifies `siteSheafTensorRight F` with `tensorRight F` for
the monoidal structure `SheafOfModules.monoidalCategory R`, and exactness is invariant under
natural isomorphisms. -/
theorem isFlatOnSite_iff_isFlat {C : Type uC} [Category.{uC} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{uC}] [HasWeakSheafify J AddCommGrpCat.{uC}]
    {R : Sheaf J CommRingCat.{uC}}
    (F : SheafOfModules.{uC} ((sheafCompose J (forget₂ CommRingCat.{uC} RingCat.{uC})).obj R)) :
    IsFlatOnSite F ↔ IsFlat F := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let e := siteSheafTensorRightIso R F
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨@Limits.preservesFiniteLimits_of_natIso _ _ _ _ _ _ e h₁,
      @Limits.preservesFiniteColimits_of_natIso _ _ _ _ _ _ e h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨@Limits.preservesFiniteLimits_of_natIso _ _ _ _ _ _ e.symm h₁,
      @Limits.preservesFiniteColimits_of_natIso _ _ _ _ _ _ e.symm h₂⟩


end SheafOfModules
