/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap


public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Canonical derived sections and strict-local cohomology germs

Source: Stacks Project, Tags 03Q8 and 03Q9. The derived Hom comparison is the
explicit free-abelian-sheaf construction used in AbelianHigherDirectImagePresheaf.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The fixed small affine pointed-neighbourhood functor to the small etale site.
Source: Stacks, Tag 03Q9, first proof paragraph
(blueprint: def-weil-pbc-strict-local-neighbourhood-geometry). -/
noncomputable def strictLocalNeighbourhoods {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s) ⥤ S.Etale :=
  (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
    Functor.Elements.π _ ⋙ Scheme.AffineEtale.Spec S

/-- The base-changed neighbourhood diagram, with the order V ×_S X.
Source: Stacks, Tag 03Q9, first proof paragraph
(blueprint: def-weil-pbc-strict-local-neighbourhood-geometry). -/
noncomputable def strictLocalNeighbourhoodDiagram {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s) ⥤ Scheme.{v} :=
  strictLocalNeighbourhoods s ⋙ Scheme.Etale.forget S ⋙ Over.pullback f ⋙ Over.forget X

/-- The stage projections to X.
Source: Stacks, Tag 03Q9, first proof paragraph
(blueprint: def-weil-pbc-strict-local-neighbourhood-geometry). -/
noncomputable def strictLocalNeighbourhoodProjection {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    strictLocalNeighbourhoodDiagram f s ⟶
      (Functor.const (SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))).obj X where
  app i := pullback.snd ((strictLocalNeighbourhoods s).obj i).hom f
  naturality i j a := by
    dsimp [strictLocalNeighbourhoodDiagram, strictLocalNeighbourhoods]
    simp

/-- Geometric data for the canonical pullback limit, without any cohomology or mate.
The first-component equation fixes each leg by the strict-henselization limit leg;
the second fixes its projection to X. Thus the data admit no arbitrary reindexing
or automorphism of the limit cone.
Source: Stacks, Tag 03Q9, first proof paragraph
(blueprint: def-weil-pbc-strict-local-neighbourhood-geometry). -/
structure StrictLocalNeighbourhoodGeometry {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) where
  legs : (Functor.const (SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))).obj
      (pullback f (Scheme.strictLocalizationToBase s)) ⟶
    strictLocalNeighbourhoodDiagram f s
  isLimit : IsLimit (Cone.mk _ legs)
  [compact : ∀ i, CompactSpace ((strictLocalNeighbourhoodDiagram f s).obj i)]
  [quasiSeparated : ∀ i, QuasiSeparatedSpace ((strictLocalNeighbourhoodDiagram f s).obj i)]
  [affine : ∀ {i j} (a : i ⟶ j), IsAffineHom ((strictLocalNeighbourhoodDiagram f s).map a)]
  first : ∀ i, legs.app i ≫ pullback.fst ((strictLocalNeighbourhoods s).obj i).hom f =
    pullback.snd f (Scheme.strictLocalizationToBase s) ≫
      (Scheme.strictHenselizationAffineCone s).π.app (op (op i)) ≫
        Spec.map (Scheme.ΓSpecIso
          ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            i).1.left.unop).inv
  over : ∀ i, legs.app i ≫ (strictLocalNeighbourhoodProjection f s).app i =
    pullback.fst f (Scheme.strictLocalizationToBase s)

end AlgebraicGeometry.Etale
