/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.CategoryTheory.SheafAlgebrasDirectedColimitAlgebraCore
import WeilConjectures.CategoryTheory.SheafAlgebrasDirectedColimitModuleCore
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Directed colimits of sheaves of commutative algebras

Source: Stacks Project, Sheaves, Sections 009D and 009E, Lemmas 0087 and 0089;
Modules, Lemma 01AH (blueprint: lem-weil-pbc-sheaf-algebras-directed-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CategoryTheory

/-- Sheafifying the sectionwise directed ring colimit produces the algebra-sheaf colimit
and the underlying module colimit. The structure morphism of the presheaf colimit is
independent of the stage, and its composite with sheafification is the structure morphism
of the resulting algebra. The legs are exactly the sheafified presheaf coprojections.
Source: Stacks Project, Sheaves, Sections 009D and 009E, Lemmas 0087 and 0089;
Modules, Lemma 01AH (blueprint: lem-weil-pbc-sheaf-algebras-directed-colimit).

1. On each open U, take the colimit of O(U)-algebras. By
   lem-weil-pbc-commutative-algebras-colimits-exist and
   lem-weil-pbc-filtered-colimit-algebras-elementwise it is also the ring colimit.
   Its structure map equals every coprojection composed with the stage structure map.
   The universal property induces restriction maps; uniqueness proves functoriality
   and compatibility of the structure map with restriction.
2. Each section is represented at a stage, and two representatives agree at a later
   stage. These facts give the module colimit sectionwise, hence in presheaves of modules
   by situation-conventions.
3. Sheafify the ring presheaf, using lem-weil-pbc-ring-sheafification-space-underlying-abelian.
   Compose the structure map and coprojections with the sheafification unit. They are
   algebra maps and satisfy the cocone identities.
4. A compatible family of algebra maps gives a unique presheaf ring map from the
   sectionwise colimit. Sheafification factors this uniquely through the sheafified ring;
   the resulting map commutes with the structure maps, proving the algebra universal property.
5. By situation-conventions, module sheafification takes the
   presheaf module colimit to a module sheaf colimit. The ring and module sheafifications
   have the same underlying abelian sheafification. Its comparison is an O-linear bijection,
   hence a module isomorphism, respecting the coprojections. Transport the module colimit
   along it. -/
theorem sheafAlgebras_directed_colimit
    (X : Type u) [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ Under O)
    (p : Cocone (F ⋙ Under.forget O ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat))
    (hp : ∀ U : Opens X, Nonempty (IsColimit
      (((evaluation (Opens X)ᵒᵖ CommRingCat).obj (Opposite.op U)).mapCocone p))) :
    ∃ (σP : O.obj ⟶ p.pt)
      (σ : O ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt)
      (ι : F ⟶ (Functor.const I).obj (Under.mk σ)),
      (∀ i : I, (F.obj i).hom.hom ≫ p.ι.app i = σP) ∧
      σ.hom = σP ≫ toSheafify (Opens.grothendieckTopology X) p.pt ∧
      (∀ i : I, (ι.app i).right.hom =
        p.ι.app i ≫ toSheafify (Opens.grothendieckTopology X) p.pt) ∧
      Nonempty (IsColimit (Cocone.mk (Under.mk σ) ι)) ∧
      Nonempty (IsColimit
        ((commAlgebraSheafModuleFunctor O).mapCocone (Cocone.mk (Under.mk σ) ι))) := by
  obtain ⟨σP, σ, ι, hP, hσ, hι, hc⟩ :=
    sheafAlgebras_directed_colimit_algebra_core X O I F p hp
  refine ⟨σP, σ, ι, hP, hσ, hι, hc, ?_⟩
  exact sheafAlgebras_directed_colimit_module_core X O I F p σ ι hp hι

end CategoryTheory
