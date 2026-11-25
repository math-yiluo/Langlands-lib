/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # Building triangle diagrams from natural Mayer--Vietoris families

Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048


variable (Y : Scheme.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ Z : Y.Opens,
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toScheme.toRingedSpace))]
  (U V : Y.Opens)

/-- The geometric triangle, with adjunctions and boundary supplied explicitly.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
noncomputable def perfectHomMVTriangle
    (adjU : (schemeMVDerivedRestriction Y U) ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeMVDerivedRestriction Y V) ⊣ schemeDerivedDirectImage V.ι)
    (adjUV : (schemeMVDerivedRestriction Y (U ⊓ V)) ⊣
      schemeDerivedDirectImage (U ⊓ V).ι)
    (δ : ∀ E : schemeDerivedCategory Y,
      (schemeDerivedDirectImage (U ⊓ V).ι).obj
        ((schemeMVDerivedRestriction Y (U ⊓ V)).obj E) ⟶ E⟦(1 : ℤ)⟧)
    (E : schemeDerivedCategory Y) : Triangle (schemeDerivedCategory Y) :=
  Triangle.mk (biprod.lift (adjU.unit.app E) (adjV.unit.app E))
    (biprod.desc
      (schemeDerivedOpenDirectImageRestriction Y (homOfLE inf_le_left) adjU adjUV E)
      (-(schemeDerivedOpenDirectImageRestriction Y (homOfLE inf_le_right) adjV adjUV E)))
    (δ E)

/-- Data of a natural geometric Mayer--Vietoris family on quasi-coherent objects.
The three components determine each triangle morphism uniquely.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
structure PerfectHomMVFamily where
  adjU : (schemeMVDerivedRestriction Y U) ⊣ schemeDerivedDirectImage U.ι
  adjV : (schemeMVDerivedRestriction Y V) ⊣ schemeDerivedDirectImage V.ι
  adjUV : (schemeMVDerivedRestriction Y (U ⊓ V)) ⊣
    schemeDerivedDirectImage (U ⊓ V).ι
  boundary : ∀ E : schemeDerivedCategory Y,
    (schemeDerivedDirectImage (U ⊓ V).ι).obj
      ((schemeMVDerivedRestriction Y (U ⊓ V)).obj E) ⟶ E⟦(1 : ℤ)⟧
  distinguished : ∀ E : schemeDerivedCategory Y, schemeDerivedQCohProperty Y E →
    perfectHomMVTriangle Y U V adjU adjV adjUV boundary E ∈
      distTriang (schemeDerivedCategory Y)
  naturality : ∀ (E F : schemeDerivedCategory Y),
    schemeDerivedQCohProperty Y E → schemeDerivedQCohProperty Y F →
    ∀ φ : E ⟶ F,
    ∃ m : perfectHomMVTriangle Y U V adjU adjV adjUV boundary E ⟶
      perfectHomMVTriangle Y U V adjU adjV adjUV boundary F,
      m.hom₁ = φ ∧
      m.hom₂ = biprod.map
        ((schemeDerivedDirectImage U.ι).map ((schemeMVDerivedRestriction Y U).map φ))
        ((schemeDerivedDirectImage V.ι).map ((schemeMVDerivedRestriction Y V).map φ)) ∧
      m.hom₃ = (schemeDerivedDirectImage (U ⊓ V).ι).map
        ((schemeMVDerivedRestriction Y (U ⊓ V)).map φ)

namespace PerfectHomMVFamily
variable {Y U V} (A : PerfectHomMVFamily Y U V)

/-- The geometric triangle of the family, with first object exactly E.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
noncomputable def triangle (E : schemeDerivedCategory Y) :
    Triangle (schemeDerivedCategory Y) :=
  perfectHomMVTriangle Y U V A.adjU A.adjV A.adjUV A.boundary E

/-- The unique triangle map with the three geometric components.
The witness is unique by Triangle.hom_ext, so choosing it introduces no unpinned data.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
noncomputable def map {E F : schemeDerivedCategory Y}
    (hE : schemeDerivedQCohProperty Y E) (hF : schemeDerivedQCohProperty Y F)
    (φ : E ⟶ F) : A.triangle E ⟶ A.triangle F :=
  Classical.choose (A.naturality E F hE hF φ)

/-- The first component is the prescribed original morphism.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
@[simp] theorem map_hom₁ {E F : schemeDerivedCategory Y}
    (hE : schemeDerivedQCohProperty Y E) (hF : schemeDerivedQCohProperty Y F)
    (φ : E ⟶ F) : (A.map hE hF φ).hom₁ = φ :=
  (Classical.choose_spec (A.naturality E F hE hF φ)).1

/-- The second component is the prescribed pair of restricted direct images.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
@[simp] theorem map_hom₂ {E F : schemeDerivedCategory Y}
    (hE : schemeDerivedQCohProperty Y E) (hF : schemeDerivedQCohProperty Y F)
    (φ : E ⟶ F) : (A.map hE hF φ).hom₂ = biprod.map
      ((schemeDerivedDirectImage U.ι).map ((schemeMVDerivedRestriction Y U).map φ))
      ((schemeDerivedDirectImage V.ι).map ((schemeMVDerivedRestriction Y V).map φ)) :=
  (Classical.choose_spec (A.naturality E F hE hF φ)).2.1

/-- The third component is the prescribed intersection restriction.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
@[simp] theorem map_hom₃ {E F : schemeDerivedCategory Y}
    (hE : schemeDerivedQCohProperty Y E) (hF : schemeDerivedQCohProperty Y F)
    (φ : E ⟶ F) : (A.map hE hF φ).hom₃ =
      (schemeDerivedDirectImage (U ⊓ V).ι).map
        ((schemeMVDerivedRestriction Y (U ⊓ V)).map φ) :=
  (Classical.choose_spec (A.naturality E F hE hF φ)).2.2

private theorem binary_map_id {C : Type*} [Category C] [HasZeroMorphisms C]
    (E F : C) [HasBinaryBiproduct E F] : biprod.map (𝟙 E) (𝟙 F) = 𝟙 (E ⊞ F) := by
  apply biprod.hom_ext <;> simp only [biprod.map_fst, biprod.map_snd,
    Category.id_comp, Category.comp_id]

private theorem binary_map_comp {C : Type*} [Category C] [HasZeroMorphisms C]
    {E F G E' F' G' : C} [HasBinaryBiproduct E E'] [HasBinaryBiproduct F F']
    [HasBinaryBiproduct G G'] (a : E ⟶ F) (b : F ⟶ G)
    (a' : E' ⟶ F') (b' : F' ⟶ G') :
    biprod.map (a ≫ b) (a' ≫ b') = biprod.map a a' ≫ biprod.map b b' := by
  apply biprod.hom_ext <;> simp only [biprod.map_fst, biprod.map_snd,
    Category.assoc, biprod.map_fst_assoc, biprod.map_snd_assoc]

/-- All three components are identities; Triangle.hom_ext gives equality.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
@[simp] theorem map_id (E : schemeDerivedCategory Y) (hE : schemeDerivedQCohProperty Y E) :
    A.map hE hE (𝟙 E) = 𝟙 (A.triangle E) := by
  apply Triangle.hom_ext
  · rw [map_hom₁]
    rfl
  · rw [map_hom₂]
    change biprod.map _ _ = 𝟙 (_ ⊞ _)
    simp only [CategoryTheory.Functor.map_id]
    exact binary_map_id _ _
  · rw [map_hom₃]
    change (schemeDerivedDirectImage (U ⊓ V).ι).map
      ((schemeMVDerivedRestriction Y (U ⊓ V)).map (𝟙 E)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

/-- Each component respects composition; Triangle.hom_ext gives equality.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
@[simp] theorem map_comp {E F G : schemeDerivedCategory Y}
    (hE : schemeDerivedQCohProperty Y E) (hF : schemeDerivedQCohProperty Y F)
    (hG : schemeDerivedQCohProperty Y G) (φ : E ⟶ F) (ψ : F ⟶ G) :
    A.map hE hG (φ ≫ ψ) = A.map hE hF φ ≫ A.map hF hG ψ := by
  apply Triangle.hom_ext
  · simp only [comp_hom₁, map_hom₁]
  · simp only [comp_hom₂, map_hom₂, CategoryTheory.Functor.map_comp]
    exact binary_map_comp _ _ _ _
  · simp only [comp_hom₃, map_hom₃, CategoryTheory.Functor.map_comp]

variable {J : Type v} [Category J]

/-- Apply the natural family to a diagram of quasi-coherent objects.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
noncomputable def diagram (F : J ⥤ schemeDerivedCategory Y)
    (hF : ∀ j, schemeDerivedQCohProperty Y (F.obj j)) :
    J ⥤ Triangle (schemeDerivedCategory Y) where
  obj j := A.triangle (F.obj j)
  map {j k} f := A.map (hF j) (hF k) (F.map f)
  map_id j := by rw [F.map_id, A.map_id]
  map_comp f g := by rw [F.map_comp, A.map_comp]

/-- Apply the same natural family to every leg and the apex of a cocone.
Source: Stacks Project, Tag 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-diagram). -/
noncomputable def cocone (F : J ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (hF : ∀ j, schemeDerivedQCohProperty Y (F.obj j))
    (hd : schemeDerivedQCohProperty Y d.pt) : Cocone (A.diagram F hF) where
  pt := A.triangle d.pt
  ι :=
    { app j := A.map (hF j) hd (d.ι.app j)
      naturality := by
        intro j k f
        change A.map (hF j) (hF k) (F.map f) ≫ A.map (hF k) hd (d.ι.app k) =
          A.map (hF j) hd (d.ι.app j) ≫ 𝟙 _
        rw [← A.map_comp, d.w f, Category.comp_id] }

end PerfectHomMVFamily
end AlgebraicGeometry
