/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverCohomology
public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverBaseChange

/-! # Pullback maps on the concrete hypercover colimit -/

@[expose] public section
universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}}
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

attribute [local instance] instHasColimitsOfSize

/-- The injection of a hypercover cohomology summand into the concrete colimit. -/
noncomputable def hypercoverCohomologyι (F : Sheaf X.smallEtaleTopology A) (q : ℕ)
    (U : FiniteSplitEtaleHypercover X) :
    (cohomologyFunctor A U q).obj F ⟶ hypercoverCohomology A F q :=
  colimit.ι (homotopyCohomologyDiagram A F q) ⟨op U⟩

/-- Colimit injections identify refinement maps. -/
theorem cohomologyRefinement_comp_ι (F : Sheaf X.smallEtaleTopology A) (q : ℕ)
    {U V : FiniteSplitEtaleHypercover X} (r : U.Refinement V) :
    (cohomologyRefinement A r q).app F ≫ hypercoverCohomologyι A F q U =
      hypercoverCohomologyι A F q V := by
  let r' : (show Index X from U) ⟶ (show Index X from V) := ⟨r⟩
  exact colimit.w (homotopyCohomologyDiagram A F q)
    ((CategoryTheory.Quotient.functor _).map r'.op)

/-- Pull back one summand and apply a morphism of coefficient sheaves. -/
noncomputable def baseChangeCohomologyComponent (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology A) (G : Sheaf X.smallEtaleTopology A)
    (k : (Etale.upperStar A f).obj F ⟶ G) (q : ℕ)
    (U : FiniteSplitEtaleHypercover Y) :
    (cohomologyFunctor A U q).obj F ⟶ hypercoverCohomology A G q :=
  baseChangeCohomologyMap A U f F q ≫
    (cohomologyFunctor A (U.baseChange f) q).map k ≫
      hypercoverCohomologyι A G q (U.baseChange f)

/-- Naturality of pullback on summands under hypercover refinements. -/
theorem baseChangeCohomologyComponent_refinement (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology A) (G : Sheaf X.smallEtaleTopology A)
    (k : (Etale.upperStar A f).obj F ⟶ G) (q : ℕ)
    {U V : FiniteSplitEtaleHypercover Y} (r : U.Refinement V) :
    (cohomologyRefinement A r q).app F ≫
        baseChangeCohomologyComponent A f F G k q U =
      baseChangeCohomologyComponent A f F G k q V := by
  dsimp only [baseChangeCohomologyComponent]
  rw [← Category.assoc, baseChangeCohomologyMap_refinement]
  simp only [Category.assoc]
  rw [← (cohomologyRefinement A (baseChangeRefinement r f) q).naturality_assoc k,
    cohomologyRefinement_comp_ι]

/-- The refinement-compatible pullback maps form a cocone on the homotopy quotient. -/
noncomputable def hypercoverPullbackCocone (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology A) (G : Sheaf X.smallEtaleTopology A)
    (k : (Etale.upperStar A f).obj F ⟶ G) (q : ℕ) :
    Cocone (homotopyCohomologyDiagram A F q) where
  pt := hypercoverCohomology A G q
  ι :=
    { app := fun U ↦ baseChangeCohomologyComponent A f F G k q U.as.unop
      naturality := by
        rintro ⟨U⟩ ⟨V⟩ r
        refine Quot.inductionOn r ?_
        intro r
        change (cohomologyRefinement A r.unop.hom q).app F ≫
          baseChangeCohomologyComponent A f F G k q V.unop =
            baseChangeCohomologyComponent A f F G k q U.unop ≫ 𝟙 _
        simpa only [Category.comp_id] using
          baseChangeCohomologyComponent_refinement A f F G k q r.unop.hom }

/-- The pullback map determined by the cochain maps on every hypercover.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2.
For each hypercover U, compose its base-change cohomology map, the coefficient map, and the target
colimit injection. Refinement compatibility follows from naturality of the coefficient
transformation and of the adjunction unit, and the colimit relation. These components define a
cocone on the homotopy quotient: quotient morphisms are represented by refinements. Take its
colimit descent. The universal colimit equation gives the component formula.
(auxiliary; not a blueprint node) -/
noncomputable def hypercoverPullback (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology A) (G : Sheaf X.smallEtaleTopology A)
    (k : (Etale.upperStar A f).obj F ⟶ G) (q : ℕ) :
    hypercoverCohomology A F q ⟶ hypercoverCohomology A G q :=
  colimit.desc _ (hypercoverPullbackCocone A f F G k q)

/-- On a summand, the pullback map is the map constructed from the adjunction unit. -/
theorem hypercoverCohomologyι_comp_pullback (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology A) (G : Sheaf X.smallEtaleTopology A)
    (k : (Etale.upperStar A f).obj F ⟶ G) (q : ℕ)
    (U : FiniteSplitEtaleHypercover Y) :
    hypercoverCohomologyι A F q U ≫ hypercoverPullback A f F G k q =
      baseChangeCohomologyComponent A f F G k q U :=
  colimit.ι_desc _ _

end AlgebraicGeometry.FiniteSplitEtaleHypercover
