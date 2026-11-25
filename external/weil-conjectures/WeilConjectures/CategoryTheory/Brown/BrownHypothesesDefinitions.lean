/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# The Brown-hypotheses bundle

Source: blueprint latest, sec-six-functors-basics/sk-lem-brown-hypotheses/_section.md.
The definition and canonical instance abbreviations are shared by the unresolved
arbitrary-field assertion and the proved criteria. This module contains no compactness
assertion and imports no coefficient-specific compactness proof.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.all false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

/-- Cache the canonical monoidal structure on condensed abelian groups.
This is the existing instance, with its site-size witnesses inferred once. -/
noncomputable abbrev brownHypothesesCondensedMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  inferInstance

attribute [local instance 30000] brownHypothesesCondensedMonoidal

/-- Cache the canonical braiding on condensed abelian groups. -/
noncomputable abbrev brownHypothesesCondensedBraided :
    BraidedCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  inferInstance

attribute [local instance 30000] brownHypothesesCondensedBraided

/-- Cache the canonical monoidal structure on pro-etale abelian sheaves. -/
noncomputable abbrev brownHypothesesSheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory Ab X

attribute [local instance 30000] brownHypothesesSheafMonoidal

/-- Cache the canonical braiding on pro-etale abelian sheaves. -/
noncomputable abbrev brownHypothesesSheafBraided (X : Scheme.{u}) :
    BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab X

attribute [local instance 30000] brownHypothesesSheafBraided

/-- Cache the existing ring-object structure pulled back from condensed coefficients. -/
noncomputable abbrev brownHypothesesCoefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  Functor.monObjObj (F := upperStarFromPoint X) Λ

attribute [local instance 30000] brownHypothesesCoefficientMonObj

/-- Cache the existing closed tensor structure on pro-etale module objects. -/
noncomputable abbrev brownHypothesesModuleMonoidalClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    MonoidalClosed (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  inferInstance

attribute [local instance 30000] brownHypothesesModuleMonoidalClosed

-- Use the direct sheaf braiding when synthesizing the module-object tensor structure.
-- Reducing both the symmetric and braided localization constructions is expensive.
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

/-- The conclusions of the Brown-hypotheses lemma, for a specified coefficient ring.
The localizing closure and constructible finite-Tor property are the recorded definitions.
All size assertions and coproducts use the fixed indexing universe `u + 1`. The existential
triangulation witness installs the canonical shift inherited from the ambient derived
category; no independently chosen shift is allowed. The coproduct witness also precedes
compactness and generation, so these clauses cannot be vacuous for lack of coproducts.
This is only a bundle of the lemma's conclusions, not an assertion for arbitrary rings.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-brown-hypotheses/_section.md, conclusion
(blueprint: def-sfb-brown-hypotheses-for). -/
def BrownHypothesesFor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  let S := constantModelBoundedConstructible Λ X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  let L := localizingClosureProEtale Λ X
  LocallySmall.{u + 1} L.FullSubcategory ∧
    ∃ hTri : L.IsTriangulated,
      letI := hTri
      L.IsClosedUnderIsomorphisms ∧
        S.IsTriangulated ∧ S.IsClosedUnderIsomorphisms ∧ S.IsStableUnderRetracts ∧
        ObjectProperty.EssentiallySmall.{u + 1} S ∧
        IsIdempotentComplete L.FullSubcategory ∧
        ∃ hSums : HasCoproducts.{u + 1} L.FullSubcategory,
          letI := hSums
          ∀ (G : Type (u + 1)) [Category.{u + 1} G] (e : G ≌ S.FullSubcategory)
            (hL : ∀ g : G, L (e.functor.obj g).1),
            (∀ g : G, IsCompactObject
              (⟨(e.functor.obj g).1, hL g⟩ : L.FullSubcategory)) ∧
            IsTriangulatedGeneratingFamily
              (fun g : G ↦ (⟨(e.functor.obj g).1, hL g⟩ : L.FullSubcategory))

end CategoryTheory
