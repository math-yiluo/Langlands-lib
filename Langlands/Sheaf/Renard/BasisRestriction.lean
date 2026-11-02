import Langlands.Sheaf.Renard.GermSectionSheaf
import Mathlib.CategoryTheory.Whiskering

/-!
# Restriction of all-open presheaves to a chosen basis

Restriction is precomposition with the actual inclusion into the all-open
basis. The original value universe is unchanged.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X]

/-- Include a chosen basis into the canonical basis of all actual opens. -/
def basisToAllOpen (B : OpenBasis X) : BasisOpen B ⥤ BasisOpen (allOpenBasis X) where
  obj U := allOpen U.obj
  map f := ObjectProperty.homMk f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem basisToAllOpen_obj (B : OpenBasis X) (U : BasisOpen B) :
    (basisToAllOpen B).obj U = allOpen U.obj := rfl

@[simp]
theorem basisToAllOpen_map (B : OpenBasis X) {U V : BasisOpen B} (f : U ⟶ V) :
    ((basisToAllOpen B).map f).hom = f.hom := rfl

@[simp]
theorem basisToAllOpen_map_basisHom (B : OpenBasis X)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    (basisToAllOpen B).map (basisHom h) =
      basisHom (B := allOpenBasis X) (U := allOpen U.obj) (V := allOpen V.obj) h := rfl

/-- Forgetting the all-open packaging gives exactly the original basis inclusion. -/
theorem basisToAllOpen_comp_inclusion (B : OpenBasis X) :
    basisToAllOpen B ⋙ basisInclusion (allOpenBasis X) = basisInclusion B := rfl

/-- Actual raw restriction by opposite precomposition. -/
def rawBasisRestriction (B : OpenBasis X) :
    RawPresheaf.{u,v} (allOpenBasis X) ⥤ RawPresheaf.{u,v} B where
  obj F := (basisToAllOpen B).op ⋙ F
  map φ := Functor.whiskerLeft (basisToAllOpen B).op φ
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem rawBasisRestriction_obj (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) :
    (rawBasisRestriction B).obj F = (basisToAllOpen B).op ⋙ F := rfl

@[simp]
theorem rawBasisRestriction_sections (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : BasisOpen B) :
    Sections ((rawBasisRestriction B).obj F) U = Sections F (allOpen U.obj) := rfl

@[simp]
theorem rawBasisRestriction_restriction (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X))
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    restriction ((rawBasisRestriction B).obj F) h =
      restriction F (U := allOpen U.obj) (V := allOpen V.obj) h := rfl

@[simp]
theorem rawBasisRestriction_map_app (B : OpenBasis X)
    {F G : RawPresheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (U : BasisOpen B) :
    ((rawBasisRestriction B).map φ).app (op U) = φ.app (op (allOpen U.obj)) := rfl

@[simp]
theorem rawBasisRestriction_identity_app (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (U : BasisOpen B) :
    ((rawBasisRestriction B).map (𝟙 F)).app (op U) =
      𝟙 (Sections F (allOpen U.obj)) := rfl

@[simp]
theorem rawBasisRestriction_composition_app (B : OpenBasis X)
    {F G H : RawPresheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (ψ : G ⟶ H)
    (U : BasisOpen B) :
    ((rawBasisRestriction B).map (φ ≫ ψ)).app (op U) =
      φ.app (op (allOpen U.obj)) ≫ ψ.app (op (allOpen U.obj)) := rfl

/-- Empty basis opens are the same actual empty opens before restriction. -/
theorem rawBasisRestriction_isNormalized (B : OpenBasis X)
    (F : RawPresheaf.{u,v} (allOpenBasis X)) (hF : IsNormalized F) :
    IsNormalized ((rawBasisRestriction B).obj F) :=
  fun U hU => hF (allOpen U.obj) hU

/-- Restrict normalized presheaves, with their original natural transformations. -/
def basisRestriction (B : OpenBasis X) :
    Presheaf.{u,v} (allOpenBasis X) ⥤ Presheaf.{u,v} B where
  obj F := ⟨(rawBasisRestriction B).obj F.obj,
    rawBasisRestriction_isNormalized B F.obj F.property⟩
  map φ := ObjectProperty.homMk ((rawBasisRestriction B).map φ.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem basisRestriction_obj_raw (B : OpenBasis X)
    (F : Presheaf.{u,v} (allOpenBasis X)) :
    ((basisRestriction B).obj F).obj = (rawBasisRestriction B).obj F.obj := rfl

@[simp]
theorem basisRestriction_sections (B : OpenBasis X)
    (F : Presheaf.{u,v} (allOpenBasis X)) (U : BasisOpen B) :
    Sections ((basisRestriction B).obj F).obj U = Sections F.obj (allOpen U.obj) := rfl

@[simp]
theorem basisRestriction_restriction (B : OpenBasis X)
    (F : Presheaf.{u,v} (allOpenBasis X)) {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    restriction ((basisRestriction B).obj F).obj h =
      restriction F.obj (U := allOpen U.obj) (V := allOpen V.obj) h := rfl

@[simp]
theorem basisRestriction_map_hom (B : OpenBasis X)
    {F G : Presheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) :
    ((basisRestriction B).map φ).hom = (rawBasisRestriction B).map φ.hom := rfl

@[simp]
theorem basisRestriction_map_app (B : OpenBasis X)
    {F G : Presheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (U : BasisOpen B) :
    ((basisRestriction B).map φ).hom.app (op U) = φ.hom.app (op (allOpen U.obj)) := rfl

@[simp]
theorem basisRestriction_identity_app (B : OpenBasis X)
    (F : Presheaf.{u,v} (allOpenBasis X)) (U : BasisOpen B) :
    ((basisRestriction B).map (𝟙 F)).hom.app (op U) =
      𝟙 (Sections F.obj (allOpen U.obj)) := rfl

@[simp]
theorem basisRestriction_composition_app (B : OpenBasis X)
    {F G H : Presheaf.{u,v} (allOpenBasis X)} (φ : F ⟶ G) (ψ : G ⟶ H)
    (U : BasisOpen B) :
    ((basisRestriction B).map (φ ≫ ψ)).hom.app (op U) =
      φ.hom.app (op (allOpen U.obj)) ≫ ψ.hom.app (op (allOpen U.obj)) := rfl

/-- Normalized restriction commutes literally with the existing raw inclusions. -/
theorem basisRestriction_comp_inclusion (B : OpenBasis X) :
    basisRestriction.{u,v} B ⋙ presheafInclusion B =
      presheafInclusion (allOpenBasis X) ⋙ rawBasisRestriction B := rfl

end Langlands.Sheaf.Renard
