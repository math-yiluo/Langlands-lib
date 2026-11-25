/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleFilteredData
import WeilConjectures.AlgebraicGeometry.ConstructibleColimitCocone

/-!
# Constructible filtered presentations of etale module sheaves

Source: Stacks Project, Tag 03SA, part (3)
(blueprint: lem-weil-pbc-module-sheaf-colimit-constructible).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every module sheaf on the small etale site of a quasi-compact quasi-separated scheme,
with coefficients in a finite commutative ring, admits a filtered colimit presentation
by constructible module sheaves. The maps and the universal property are in the category
of module-valued sheaves, the constant-ring module-sheaf encoding used by
`IsConstructibleEtaleModuleSheaf`.

Source: Stacks Project, Tag 03SA(3)
(blueprint: lemma-finiteness-small-etale-topoi--1).

Proof:
1. Constructible module sheaves generate the category: choose an epimorphism from a
   coproduct of constructible sheaves to `F` (`lemma-finiteness-small-etale-topoi--1`).
   Constructible sheaves are finitely presented
   (`lemma-finiteness-small-etale-topoi--1`), so maps from them into a filtered
   colimit factor through a stage and equalities hold after a common refinement.
2. Take a small model of the category of constructible sheaves equipped with a map to
   `F`, with morphisms commuting with these maps. The zero sheaf gives nonemptiness,
   finite sums give common successors, and constructible cokernels equalize parallel
   arrows. Thus the category is filtered. Generation and finite presentation show
   that the canonical cocone is a colimit (`lemma-finiteness-small-etale-topoi--1`): compatible
   maps descend uniquely through the generating epimorphism, and local epimorphism
   detection gives uniqueness.
3. This construction takes place in module sheaves, with all maps linear over `Λ`.
   The cocone is therefore a colimit in that category, and every diagram object is
   constructible (`lemma-finiteness-small-etale-topoi--1`, `situation-conventions`).
-/
theorem exists_filtered_colimit_constructible
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (A : Type (u + 1)) (_ : SmallCategory A) (_ : IsFiltered A)
      (D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ a : A, IsConstructibleEtaleModuleSheaf (D.obj a)) ∧
        ∃ ι : D ⟶ (Functor.const A).obj F,
          Nonempty (IsColimit (Cocone.mk F ι)) := by
  obtain ⟨A, hA, hfiltered, D, ι, hconstructible, hfactor, hrelations⟩ :=
    exists_filtered_constructible_data F
  let := hA
  let := hfiltered
  exact ⟨A, hA, hfiltered, D, hconstructible, ι,
    exists_constructible_colimit_cocone F A D ι hfactor hrelations⟩

end AlgebraicGeometry.Scheme
