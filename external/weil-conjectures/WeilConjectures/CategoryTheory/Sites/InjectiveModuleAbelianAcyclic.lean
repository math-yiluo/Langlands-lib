/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleNerveAcyclic
import WeilConjectures.CategoryTheory.Sites.PresheafCechVanishingCriterion

/-!
# Injective module sheaves are acyclic after forgetting to abelian sheaves

Source: literature/stacks-project/sites-cohomology.tex, Lemma Tag 03FD
(lemma-cohomology-modules-abelian-agree), proof, second paragraph (via Lemmas 03FC and 03F9)
(blueprint: lem-sc-injective-module-abelian-acyclic-zariski).

The proof uses the presheaf-nerve form of the Čech argument: fibre products are formed
in presheaves, where they always exist, and the presheaf Čech vanishing criterion
passes from Čech vanishing to derived cohomology. This avoids imposing extra pullback
or universe hypotheses on the site.
-/

@[expose] public section

universe u v w'

open CategoryTheory

namespace CategoryTheory

/-- The underlying abelian sheaf of an injective sheaf of modules has no positive
cohomology over any object of the site.
Source: Stacks Project, `sites-cohomology.tex`, Tag 03FD
(`lemma-cohomology-modules-abelian-agree`), proof, second paragraph, via Tags 03FC and 03F9.
(blueprint: lem-sc-injective-module-abelian-acyclic-zariski)

Proof: exact module sheafification makes `I.val` injective as a module presheaf
(Tag 03FB). For every map of small-valued presheaves of sets, its free-module
Čech nerve is exact in positive degrees by the fibrewise contraction of Tags
03F5 and 03AT. Applying Hom into `I.val` gives positive Čech vanishing for the
underlying abelian presheaf. Apply the presheaf-nerve Čech vanishing criterion
(Tags 03F9 and 079Z), then turn `IsZero` into `Subsingleton`. All fibre products
in this variant are taken in presheaves, so no pullbacks of `C` are required. -/
theorem injective_module_abelian_acyclic
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}} [HasSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (U : C) (I : SheafOfModules.{v} R) [Injective I] :
    ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H' ((SheafOfModules.toSheaf R).obj I) q U) := by
  let F := (SheafOfModules.toSheaf R).obj I
  have hI : Injective I.val := injective_module_sheaf_injective_presheaf R I
  have hcech (f : Arrow (Cᵒᵖ ⥤ Type v)) (q : ℕ) (hq : 0 < q) :
      CategoryTheory.Limits.IsZero ((presheafCechComplex f F.obj).homology q) := by
    exact injective_presheaf_module_nerve_acyclic R.obj I.val f q hq
  intro q hq
  exact AddCommGrpCat.subsingleton_of_isZero
    (Sheaf.isZero_H'_of_presheafCech_vanishing F hcech U q hq)

end CategoryTheory
