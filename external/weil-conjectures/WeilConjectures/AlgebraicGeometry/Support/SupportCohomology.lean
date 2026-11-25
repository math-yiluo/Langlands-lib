/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Sheafification
public import WeilConjectures.SixFunctors.Etale.SupportCohomology

/-!
# Cohomology with support

Source: the blueprint, `sec-smooth-purity/sk-def-purity-conv`,
`definition-local-cohomology` (blueprint: definition-local-cohomology).

## Main definitions

* `CategoryTheory.Sheaf.supportedSectionsFunctor`: kernel of restriction on sections.
* `AlgebraicGeometry.Etale.supportCohomology`: the natural-number derived functors.
* `AlgebraicGeometry.Etale.derivedSupportSections`: bounded-below derived sections.
* `AlgebraicGeometry.Etale.supportHypercohomology`: their integer-indexed cohomology.
* The same three constructions in `AlgebraicGeometry.ProEtale` use the small pro-etale site.

The constructions are defined for all abelian sheaves, hence in particular on the torsion
sheaves and bounded-below complexes with torsion cohomology of the node. On the pro-etale
site the coefficient category may be `ModuleCat Λ`, in particular for each finite-torsion
coefficient ring of the purity conventions. No twist is needed to define supported sections.
-/

@[expose] public section

universe v w c a u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A] {V W : C} (j : W ⟶ V)

/-- The kernel of restriction from `V` to `W`, on objects and morphisms of sheaves.
Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, kernel formula
(blueprint: definition-local-cohomology). This single construction is used in both topologies. -/
noncomputable def supportedSectionsFunctor : Sheaf J A ⥤ A where
  obj F := kernel (F.obj.map j.op)
  map f := kernel.map _ _ (f.hom.app (op V)) (f.hom.app (op W))
    (f.hom.naturality j.op)
  map_id F := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

/-- Additivity needed to derive the kernel-of-restriction functor.
Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, derived-functor clause
(blueprint: definition-local-cohomology).
Proof: compose each proposed equality with the kernel inclusion. The resulting equality
is additivity of evaluation on sections; the kernel inclusion is monic. -/
theorem supportedSectionsFunctor_additive : (supportedSectionsFunctor J A j).Additive := by
  refine ⟨?_⟩
  intro F G f g
  apply equalizer.hom_ext
  simp [supportedSectionsFunctor, Preadditive.add_comp, Preadditive.comp_add]

attribute [instance] supportedSectionsFunctor_additive

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

namespace Etale

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The open-complement restriction arrow in the small etale site.
Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, restriction along `j`
(blueprint: definition-local-cohomology). -/
def supportRestrictionArrow :
    Scheme.Etale.mk i.openComplement.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk i.openComplement.ι
    (by change i.openComplement.ι ≫ 𝟙 X = _; simp)

/-- Sections of an abelian etale sheaf with support in the closed subscheme `Z`.
Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, kernel formula
(blueprint: definition-local-cohomology). -/
noncomputable abbrev supportSections :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.supportedSectionsFunctor X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (supportRestrictionArrow i)

/-- `R Γ_Z` on the bounded-below derived category of abelian etale sheaves.
Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, derived-complex clause
(blueprint: definition-local-cohomology). -/
noncomputable def derivedSupportSections :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  (supportSections i).rightDerivedFunctorPlus

/-- `H^q_Z(X,K) = H^q(R Γ_Z(X,K))` for every integer, in particular when `K` has
 torsion cohomology. Source: blueprint `sec-smooth-purity/sk-def-purity-conv`
(blueprint: definition-local-cohomology). -/
noncomputable def supportHypercohomology (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    AddCommGrpCat.{u + 1} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
    ((derivedSupportSections i).obj K)

end Etale

namespace ProEtale

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The same restriction arrow in the small pro-etale site.
Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, pro-etale clause
(blueprint: definition-local-cohomology). -/
def supportRestrictionArrow :
    Scheme.ProEt.mk i.openComplement.ι ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk i.openComplement.ι
    (by change i.openComplement.ι ≫ 𝟙 X = _; simp)

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Sections with closed support of a pro-etale `Λ`-module sheaf, in particular for each
finite-torsion coefficient ring `A_{E,n}`. The kernel carries the induced `Λ` action.
Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, pro-etale clause
(blueprint: definition-local-cohomology). -/
noncomputable abbrev supportSections :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
  Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
    (supportRestrictionArrow i)

/-- Bounded-below right derived supported sections on the small pro-etale site.
Source: blueprint `sec-smooth-purity/sk-def-purity-conv`, pro-etale clause
(blueprint: definition-local-cohomology). -/
noncomputable def derivedSupportSections :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Λ) :=
  (supportSections i Λ).rightDerivedFunctorPlus

/-- Cohomology of derived supported sections, in every integer degree, with pro-etale
finite-torsion coefficients. Source: blueprint `sec-smooth-purity/sk-def-purity-conv`
(blueprint: definition-local-cohomology). -/
noncomputable def supportHypercohomology (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    ModuleCat.{u + 1} Λ :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
    ((derivedSupportSections i Λ).obj K)

end ProEtale
end AlgebraicGeometry
