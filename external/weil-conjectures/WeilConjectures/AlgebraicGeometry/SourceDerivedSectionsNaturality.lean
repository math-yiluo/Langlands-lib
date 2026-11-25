/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.SourceDerivedSectionsNaturalityCore

/-! # Naturality of the derived Hom to sections comparison

Source: Stacks Project, Tag 03Q8, computation with injective complexes.
(blueprint: lem-weil-pbc-source-derived-sections-naturality).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

/-- Localizing Hom classes and evaluating the free generator commutes with restriction.
Source: Stacks Project, Tag 03Q8, injective-complex computation of higher direct images.
(blueprint: lem-weil-pbc-source-derived-sections-naturality).

Proof: For each W, use the single complex on the free sheaf of W. Precomposition
by the free-sheaf map of a sends a cocycle to its precomposition and respects
boundaries. The Hom-complex cohomology isomorphism intertwines this operation
with the homology map of the precomposition chain map: check after the surjection
from cocycles, where both maps are the class of that cocycle. The equivalence
from classes to homotopy maps sends it to precomposition by the single-complex
map, by equivHomShift_symm_precomp and functoriality of the homotopy quotient.
Applying Qh preserves this equality. Its map is bijective into the shifted
K-injective L; therefore its inverse also respects precomposition. Naturality of
quotientCompQhIso and singleFunctorIsoCompQ cancels the two localization
comparisons. The fully faithful inclusion of D+ and transport by q respect
precomposition by functoriality and associativity. Finally, evaluating the free
sheaf generator after precomposition is restriction of the section, by naturality
of the sheafification, free abelian group, and Yoneda adjunctions. This gives an
equality of chain maps under sourceFreeSectionsComplexIso. Taking homology and
composing the preceding squares gives the displayed equality. Identity arrows
act identically; zero L gives zero groups; the argument uses any integer degree,
without an assumption that n is nonnegative. -/
theorem sourceDerivedSections_naturality
    {C : Type (v + 1)} [Category.{v} C]
    {T : GrothendieckTopology C} [HasSheafify T AddCommGrpCat.{v + 1}]
    [HasDerivedCategory.{v + 1} (Sheaf T AddCommGrpCat.{v + 1})]
    (K : DerivedCategory.Plus (Sheaf T AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf T AddCommGrpCat.{v + 1}) ℤ) [L.IsKInjective]
    (q : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) {U V : C} (a : U ⟶ V) :
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n
    let e := fun W : C ↦
      sourcePlusHomIso ((strictLocalFreeSheaf T).obj W) K L q n ≪≫
      (sourceClassDerivedHomIso ((strictLocalFreeSheaf T).obj W) L n).symm ≪≫
      (leftHomologyData ((CochainComplex.singleFunctor _ 0).obj
        ((strictLocalFreeSheaf T).obj W)) L n).homologyIso.symm ≪≫
      H.mapIso (sourceFreeSectionsComplexIso W L)
    AddCommGrpCat.ofHom (Preadditive.leftComp (K⟦n⟧)
      ((DerivedCategory.Plus.singleFunctor _ 0).map ((strictLocalFreeSheaf T).map a))) ≫
        (e U).hom =
      (e V).hom ≫ H.map
        ((NatTrans.mapHomologicalComplex
          ((sheafSections T AddCommGrpCat.{v + 1}).map a.op) (.up ℤ)).app L) := by
  simpa only [Iso.trans_hom, Category.assoc] using
    (sourceDerivedSections_naturality_compose K L q n a)


end AlgebraicGeometry.Etale
