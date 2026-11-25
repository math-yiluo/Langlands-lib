/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdge
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf

/-! # Naturality of normalized derived local classes

Source: Stacks Project, Cohomology, Tags 01E4, 01FB, 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-square-local-class-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry.RingedSpace
variable {Y : RingedSpace.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
/-- Naturality of the normalized derived local class.
Source: Stacks Project, Cohomology, Tag 0BKJ
(blueprint: lem-weil-pbc-square-local-class-naturality).

Proof: On K-injective representatives, compose naturality of the derived unit,
localization homology and exact sheafification. Lift an arbitrary derived morphism
to a complex map into the K-injective representative and conjugate by the two
resolution isomorphisms. Finally use naturality of the sheafification unit. -/
theorem squareLocalClass_naturality (q : ℤ)
    {K L : DerivedCategory (SheafOfModules.{u} (moduleRings Y))} (a : K ⟶ L) :
    (localHypercohomologyPresheaf Y q).map a ≫ topEdgeLocalClass Y q L =
      topEdgeLocalClass Y q K ≫
        (localAbelianSections Y).map ((DerivedCategory.homologyFunctor _ q).map a) := by
  let P := localHypercohomologyPresheaf Y q
  let U := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let η := (sheafificationAdjunction (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}).unit
  let αK := (localHypercohomologySheafificationAt q K).hom
  let αL := (localHypercohomologySheafificationAt q L).hom
  let b := (SheafOfModules.toSheaf (moduleRings Y)).map
    ((DerivedCategory.homologyFunctor _ q).map a)
  have h : U.map (S.map (P.map a)) ≫ U.map αL = U.map αK ≫ U.map b := by
    have hh := congrArg U.map (sheafificationAt_naturality q a)
    change U.map (S.map (P.map a) ≫ αL) = U.map (αK ≫ b) at hh
    simpa only [Functor.map_comp] using hh
  have hu : P.map a ≫ η.app (P.obj L) = η.app (P.obj K) ≫ U.map (S.map (P.map a)) :=
    η.naturality (P.map a)
  change P.map a ≫ (η.app (P.obj L) ≫ U.map αL) =
    (η.app (P.obj K) ≫ U.map αK) ≫ U.map b
  calc
    _ = (P.map a ≫ η.app (P.obj L)) ≫ U.map αL := (Category.assoc _ _ _).symm
    _ = (η.app (P.obj K) ≫ U.map (S.map (P.map a))) ≫ U.map αL :=
      congrArg (fun z ↦ z ≫ U.map αL) hu
    _ = η.app (P.obj K) ≫ (U.map (S.map (P.map a)) ≫ U.map αL) :=
      Category.assoc _ _ _
    _ = η.app (P.obj K) ≫ (U.map αK ≫ U.map b) :=
      congrArg (fun z ↦ η.app (P.obj K) ≫ z) h
    _ = _ := (Category.assoc _ _ _).symm

end AlgebraicGeometry.RingedSpace
