/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.RingTheory.IndEtaleSmallIndex

/-! # Continuity maps and classical pro-étale sheaves

Source: current blueprint, sec-proetale-coefficients/sk-def-pe-classical-definition,
`sk-def-pe-classical-definition-continuity-map.md`, clauses 1--4 and final paragraph
(blueprint: det-pe-classical-definition-continuity-map).

The index categories and section values live in the common larger universe `u + 1`.
Module coefficients use the intrinsic constant-ring module category of the recorded
small pro-étale site, with the same coefficient lift as `Scheme.proEtaleDerivedCategory`.
-/

@[expose] public section

set_option autoImplicit false

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- An affine étale presentation with an affine vertex in the pro-étale site.
The universal property is taken in all schemes over `X`, not just in the site.
Source: current blueprint, continuity-map detail, clause 1
(blueprint: definition-classical-pro-etale-sheaves--1). -/
structure AffinePresentation (X : Scheme.{u}) (I : Type (u + 1))
    [SmallCategory I] [IsCofiltered I] where
  diagram : I ⥤ X.ProEt
  affine : ∀ i : I, IsAffine (diagram.obj i).left
  etale : ∀ i : I, Etale (diagram.obj i).hom
  cone : Cone diagram
  affineVertex : IsAffine cone.pt.left
  isLimit : IsLimit ((Scheme.ProEt.forget X).mapCone cone)

/-- Restriction of a presheaf to the stages of a presentation, contravariantly.
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map). -/
def sectionDiagram {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C) : Iᵒᵖ ⥤ C :=
  P.diagram.op ⋙ F

/-- The restriction cocone, obtained functorially from the projection cone.
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map). -/
def sectionCocone {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C) :
    Cocone (sectionDiagram P F) :=
  F.mapCocone P.cone.op

/-- The canonical map out of the chosen colimit, retaining the presentation.
Source: current blueprint, continuity-map detail, clause 2; Stacks, Categories, Tag 002F
(blueprint: definition-classical-pro-etale-sheaves--1). -/
noncomputable def continuityMap {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] (F : X.ProEtᵒᵖ ⥤ C)
    [HasColimit (sectionDiagram P F)] :
    colimit (sectionDiagram P F) ⟶ F.obj (op P.cone.pt) :=
  colimit.desc (sectionDiagram P F) (sectionCocone P F)

/-- Naturality of the continuity map in the sheaf (in fact in any presheaf).
Source: current blueprint, continuity-map detail, clause 2
(blueprint: det-pe-classical-definition-continuity-map).
Proof: precompose with every coprojection. Both composites become the restriction map
along `u_i` followed by the component of the sheaf morphism. They agree by naturality;
the colimit universal property gives equality. -/
theorem continuityMap_natural {X : Scheme.{u}} {I : Type (u + 1)} [SmallCategory I]
    [IsCofiltered I] (P : AffinePresentation X I)
    {C : Type uC} [Category.{vC} C] {F G : X.ProEtᵒᵖ ⥤ C} (α : F ⟶ G)
    [HasColimit (sectionDiagram P F)] [HasColimit (sectionDiagram P G)] :
    colimMap (G := sectionDiagram P F) (F := sectionDiagram P G)
      (Functor.whiskerLeft P.diagram.op α) ≫ continuityMap P G =
      continuityMap P F ≫ α.app (op P.cone.pt) := by
  apply colimit.hom_ext
  intro i
  obtain ⟨i⟩ := i
  simp [continuityMap, sectionCocone, sectionDiagram, α.naturality]

/-- A set sheaf is classical when every affine presentation gives a bijective map.
Source: current blueprint, continuity-map detail, clause 3
(blueprint: definition-classical-pro-etale-sheaves--1). -/
def IsClassical {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) : Prop :=
  ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I), Function.Bijective (continuityMap P F.obj)

/-- Set-sheaf classicality is invariant under isomorphism.
Source: current blueprint, continuity-map proof, third paragraph
(blueprint: det-pe-classical-definition-continuity-map).
Proof: naturality identifies the continuity maps through the component bijections of
an isomorphism and the colimit isomorphism induced by its stage components. Apply the
same construction to its inverse to see that these identifications are bijective. -/
theorem isClassical_iso_iff {X : Scheme.{u}}
    {F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))} (e : F ≅ G) :
    IsClassical F ↔ IsClassical G := by
  have h {F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))}
      (e : F ≅ G) (hF : IsClassical F) : IsClassical G := by
    intro I _ _ P
    have hmap := continuityMap_natural P e.hom.hom
    have : IsIso (continuityMap P F.obj) :=
      (CategoryTheory.isIso_iff_bijective _).mpr (hF P)
    have : IsIso (Functor.whiskerLeft P.diagram.op e.hom.hom) := by
      change IsIso (Functor.isoWhiskerLeft P.diagram.op
        ((sheafToPresheaf _ _).mapIso e)).hom
      infer_instance
    have : IsIso (e.hom.hom.app (op P.cone.pt)) := by infer_instance
    have : IsIso (continuityMap P G.obj) := by
      apply (isIso_comp_left_iff
        (colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
      rw [hmap]
      infer_instance
    exact (CategoryTheory.isIso_iff_bijective _).mp inferInstance
  exact ⟨h e, h e.symm⟩

section Modules

variable {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]

variable (F : ringedSiteModules.{u + 1}
  ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} Λ)))))

end Modules

end AlgebraicGeometry.ProEtale
