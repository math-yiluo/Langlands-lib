/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.CategoryTheory.Sites.ZariskiTorsorRepresentativeExists

/-!
# Torsor classes as boundaries of the representative extension

Source: literature/stacks-project/cohomology.tex, Lemma 02FQ
(cohomology-lemma-torsors-h1), construction of the extension and its boundary of one
(blueprint: lem-sc-torsor-h1-boundary-representative).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace CategoryTheory.Sheaf

/-- Every Zariski torsor is represented by the fibre over one of an extension by the
constant integer sheaf, and that fibre has the connecting class of one. Conversely,
the fibre of every such extension is a torsor with this class.

Source: Stacks Project, Cohomology of Sheaves, Lemma 02FQ (lemma-torsors-h1).
Proof: (1) Construct the extension as the coproduct of contracted powers of the torsor,
with degree zero equal to `G` and negative powers formed from the inverse torsor
(`lem-sc-zariski-ext-torsor`). Concatenation defines addition; the exponent map is
surjective with kernel `G`, and its fibre over one is the given torsor.
(2) The long exact sequence (`def-sc-topological-abelian-cohomology`) supplies the
boundary map. The boundary characterization (`lem-sc-torsor-h1-zariski-boundary-class`)
identifies the class of the fibre under the canonical bijection
(`lemma-cohomology-multiplicative-group--3`) with the boundary of one. The fibre is isomorphic to
the original torsor by (1). (3) For every short exact sequence, the same boundary characterization
constructs its fibre as a `G`-torsor and identifies its class with the boundary of one.
(blueprint: lem-sc-torsor-h1-boundary-representative) -/
theorem torsor_h1_boundary_representative (X : Scheme.{u})
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (T : G.Torsor) :
    (∃ (E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ι : G ⟶ E) (p : E ⟶
        (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u, 0} ℤ)))
      (hzero : ι ≫ p = 0)
      (hS : (ShortComplex.mk ι p hzero).ShortExact),
      Nonempty (Torsor.Iso T
        (Torsor.lifts (IsTerminal.ofUnique (⊤ : Opens X))
          hS
          ((toSheafify (Opens.grothendieckTopology X)
            ((Functor.const (Opens X)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩))) ∧
      CategoryTheory.Sheaf.Torsor.classH1 G (IsTerminal.ofUnique (⊤ : Opens X)) ⟦T⟧ =
        H.δSections hS
          (IsTerminal.ofUnique (⊤ : Opens X))
          ((toSheafify (Opens.grothendieckTopology X)
            ((Functor.const (Opens X)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩)) ∧
      ∀ (E : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ι : G ⟶ E) (p : E ⟶
          (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u, 0} ℤ)))
        (hzero : ι ≫ p = 0)
        (hS : (ShortComplex.mk ι p hzero).ShortExact),
        CategoryTheory.Sheaf.Torsor.classH1 G (IsTerminal.ofUnique (⊤ : Opens X))
            ⟦Torsor.lifts (IsTerminal.ofUnique (⊤ : Opens X)) hS
              ((toSheafify (Opens.grothendieckTopology X)
                ((Functor.const (Opens X)ᵒᵖ).obj
                  (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩)⟧ =
          H.δSections hS (IsTerminal.ofUnique (⊤ : Opens X))
            ((toSheafify (Opens.grothendieckTopology X)
              ((Functor.const (Opens X)ᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u, 0} ℤ)))).app (op ⊤) ⟨1⟩) := by
  constructor
  · obtain ⟨E, ι, p, hzero, hS, hT⟩ := zariski_torsor_representative_exists X G T
    refine ⟨E, ι, p, hzero, hS, hT, ?_⟩
    rw [_root_.Quotient.sound hT]
    exact Torsor.classH1_lifts (IsTerminal.ofUnique (⊤ : Opens X)) hS _
  · intro E ι p hzero hS
    exact Torsor.classH1_lifts (IsTerminal.ofUnique (⊤ : Opens X)) hS _

end CategoryTheory.Sheaf
