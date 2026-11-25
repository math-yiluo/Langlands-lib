/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals on a ringed site

Source: Stacks Project, Modules on Sites, finite type ideals; Algebraization, Tags 0999
and 099I (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- Forget only commutativity when forming the module category of a ringed site.
Source: Stacks Project, Modules on Sites (auxiliary; not a blueprint node).
-/
abbrev siteModuleRings {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

/-- An ideal subsheaf: ideals of sections, stable under restriction, with local membership.
Source: Stacks Project, Modules on Sites, sheaves of ideals; Algebraization, Tag 0999
(auxiliary; not a blueprint node). -/
structure RingedSiteIdeal {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) where
  /-- The ideal of sections on each object. -/
  sections (U : C) : Ideal (R.obj.obj (op U))
  /-- Restrictions preserve the ideal. -/
  restriction {U V : C} (g : V ⟶ U) (a : R.obj.obj (op U)) :
    a ∈ sections U → R.obj.map g.op a ∈ sections V
  /-- Ideal membership can be checked on a covering sieve. -/
  local_mem (U : C) (a : R.obj.obj (op U)) (S : Sieve U) :
    S ∈ J U → (∀ (V : C) (g : V ⟶ U), S g → R.obj.map g.op a ∈ sections V) →
      a ∈ sections U

namespace RingedSiteIdeal

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{u}}

/-- Restriction on the ideals of sections, as a semilinear module map.
Source: Stacks Project, Modules on Sites, ideal subsheaves
(auxiliary; not a blueprint node). -/
noncomputable def restrictionMap (I : RingedSiteIdeal R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of (R.obj.obj X) (I.sections X.unop) ⟶
      (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj Y) (I.sections Y.unop)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (R.obj.obj X) (I.sections X.unop))
    (Y := (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj Y) (I.sections Y.unop)))
    { toFun := fun a => ⟨R.obj.map f a, I.restriction f.unop a a.property⟩
      map_add' := fun a b => Subtype.ext (map_add (R.obj.map f).hom a.val b.val)
      map_smul' := fun r a => Subtype.ext (map_mul (R.obj.map f).hom r a.val) }

/-- Identity law for restriction on an ideal.
Source: Stacks Project, Modules on Sites (auxiliary; not a blueprint node).
Proof: after the inclusion into the ambient ring, the law is the identity law of `R`.
Subtype extensionality gives equality of the maps. -/
theorem restrictionMap_id (I : RingedSiteIdeal R) (X : Cᵒᵖ) :
    I.restrictionMap (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((siteModuleRings R).obj.map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((siteModuleRings R).obj.map_id X))).inv.app _ := by
  ext a
  apply Subtype.ext
  exact congrArg (fun k => k a.val) (R.obj.map_id X)

/-- Composition law for restriction on an ideal.
Source: Stacks Project, Modules on Sites (auxiliary; not a blueprint node).
Proof: include each output into the ambient ring and use the composition law of `R`;
subtype extensionality then proves the displayed equality. -/
theorem restrictionMap_comp (I : RingedSiteIdeal R) {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    I.restrictionMap (f ≫ g) = I.restrictionMap f ≫
      (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).map
        (I.restrictionMap g) ≫
      (ModuleCat.restrictScalarsComp' ((siteModuleRings R).obj.map f).hom
        ((siteModuleRings R).obj.map g).hom ((siteModuleRings R).obj.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom ((siteModuleRings R).obj.map_comp f g))).inv.app _ := by
  ext a
  apply Subtype.ext
  exact congrArg (fun k => k a.val) (R.obj.map_comp f g)

/-- The underlying module presheaf of an ideal subsheaf.
Source: Stacks Project, Modules on Sites (auxiliary; not a blueprint node). -/
noncomputable def modulePresheaf (I : RingedSiteIdeal R) :
    PresheafOfModules.{u} (siteModuleRings R).obj where
  obj X := ModuleCat.of (R.obj.obj X) (I.sections X.unop)
  map f := I.restrictionMap f
  map_id X := I.restrictionMap_id X
  map_comp f g := I.restrictionMap_comp f g

/-- The ideals of sections form a sheaf of modules.
Source: Stacks Project, Modules on Sites (auxiliary; not a blueprint node).
Proof: glue a matching family in the ambient ring sheaf. The restrictions of the glued
section lie in the ideal on the covering sieve, so `local_mem` puts it in the ideal.
Uniqueness follows from uniqueness of the ambient ring-sheaf gluing. -/
theorem modulePresheaf_isSheaf (I : RingedSiteIdeal R) :
    Presheaf.IsSheaf J I.modulePresheaf.presheaf := by
  let G : Subfunctor (R.obj ⋙ forget CommRingCat) :=
    { obj := fun X ↦ {a | a ∈ I.sections X.unop}
      map := fun f a ha ↦ I.restriction f.unop a ha }
  have hR : Presieve.IsSheaf J (R.obj ⋙ forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type J _).mp
      ((sheafCompose J (forget CommRingCat)).obj R).property
  have hG : Presieve.IsSheaf J G.toFunctor :=
    (G.isSheaf_iff hR).mpr fun X a ha ↦
      I.local_mem X.unop a (G.sieveOfSection a) ha (fun _ _ h ↦ h)
  rw [Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat),
    isSheaf_iff_isSheaf_of_type]
  exact hG

/-- The underlying module sheaf of the ideal, with its actual ideals of sections.
Finite generation is Mathlib's `SheafOfModules.IsFiniteType` applied to this module.
Source: Stacks Project, Modules on Sites (auxiliary; not a blueprint node). -/
noncomputable def module (I : RingedSiteIdeal R) : SheafOfModules.{u} (siteModuleRings R) where
  val := I.modulePresheaf
  isSheaf := I.modulePresheaf_isSheaf

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise inclusion of an ideal into the rank-one module.
Source: Stacks Project, Modules on Sites, ideal subsheaves
(auxiliary; not a blueprint node). -/
noncomputable def inclusionApp (I : RingedSiteIdeal R) (X : Cᵒᵖ) :
    I.module.val.obj X ⟶ (SheafOfModules.unit (siteModuleRings R)).val.obj X :=
  ModuleCat.ofHom
    (X := ModuleCat.of (R.obj.obj X) (I.sections X.unop))
    (Y := ModuleCat.of (R.obj.obj X) (R.obj.obj X))
    (I.sections X.unop).subtype

/-- Naturality of the sectionwise inclusion of an ideal subsheaf.
Source: Stacks Project, Modules on Sites, ideal subsheaves
(auxiliary; not a blueprint node).
Proof: both composites send an ideal section to its restriction in the ambient ring;
the subtype restriction was defined using precisely the ambient restriction map. -/
theorem inclusionApp_naturality (I : RingedSiteIdeal R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    I.module.val.map f ≫
        (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).map
          (I.inclusionApp Y) =
      I.inclusionApp X ≫ (SheafOfModules.unit (siteModuleRings R)).val.map f := by
  ext a
  rfl

/-- The canonical inclusion of the ideal module sheaf into the ring module sheaf.
Source: Stacks Project, Modules on Sites, ideal subsheaves
(auxiliary; not a blueprint node). -/
noncomputable def inclusion (I : RingedSiteIdeal R) :
    I.module ⟶ SheafOfModules.unit (siteModuleRings R) where
  val := { app := I.inclusionApp, naturality := I.inclusionApp_naturality }

/-- There is a unique ideal subsheaf whose sections locally lie in the ideal generated
by images of sections of `I`.
Source: Stacks Project, Modules on Sites, extension of ideals; Algebraization, Tag 099I
(auxiliary; not a blueprint node).
Proof: take the local saturation of the sectionwise image-generated ideals. Addition,
negation, and multiplication preserve local membership after intersecting covering sieves.
Restriction uses pullback of covering sieves; the local-membership axiom uses transitivity.
The displayed membership formula determines every ideal of sections and hence the subsheaf
uniquely by proof irrelevance. -/
theorem existsUnique_extension (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    ∃! K : RingedSiteIdeal B,
      ∀ (U : C) (b : B.obj.obj (op U)), b ∈ K.sections U ↔
        ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
          B.obj.map g.op b ∈
            Ideal.span (Set.range (fun a : I.sections V => φ.hom.app (op V) a)) := by
  let P (U : C) : Ideal (B.obj.obj (op U)) :=
    Ideal.span (Set.range (fun a : I.sections U ↦ φ.hom.app (op U) a))
  have hP {U V : C} (g : V ⟶ U) (b : B.obj.obj (op U)) (hb : b ∈ P U) :
      B.obj.map g.op b ∈ P V := by
    have hle : P U ≤ Ideal.comap (B.obj.map g.op).hom (P V) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      change B.obj.map g.op (φ.hom.app (op U) a.val) ∈ P V
      have he : B.obj.map g.op (φ.hom.app (op U) a.val) =
          φ.hom.app (op V) (R.obj.map g.op a.val) :=
        (congrArg (fun k ↦ k a.val) (φ.hom.naturality g.op)).symm
      rw [he]
      exact Ideal.subset_span ⟨⟨_, I.restriction g a.val a.property⟩, rfl⟩
    exact hle hb
  let G : Subfunctor (B.obj ⋙ forget CommRingCat) :=
    { obj := fun X ↦ {b | b ∈ P X.unop}
      map := fun f b hb ↦ hP f.unop b hb }
  let H := G.sheafify J
  have hB : Presieve.IsSheaf J (B.obj ⋙ forget CommRingCat) :=
    (isSheaf_iff_isSheaf_of_type J _).mp
      ((sheafCompose J (forget CommRingCat)).obj B).property
  have hlocal (U : C) (b : B.obj.obj (op U)) (S : Sieve U) (hS : S ∈ J U)
      (hb : ∀ (V : C) (g : V ⟶ U), S g → B.obj.map g.op b ∈ H.obj (op V)) :
      b ∈ H.obj (op U) := by
    apply (H.isSheaf_iff hB).mp
      (G.sheafify_isSheaf hB) (op U) b
    exact J.superset_covering hb hS
  have hadd (U : C) (a b : B.obj.obj (op U))
      (ha : a ∈ H.obj (op U)) (hb : b ∈ H.obj (op U)) :
      a + b ∈ H.obj (op U) := by
    change G.sieveOfSection (a + b) ∈ J U
    refine J.superset_covering (S := G.sieveOfSection a ⊓ G.sieveOfSection b) ?_
      (J.intersection_covering ha hb)
    intro V g hg
    change B.obj.map g.op (a + b) ∈ P V
    rw [map_add]
    exact (P V).add_mem hg.1 hg.2
  have hsmul (U : C) (r a : B.obj.obj (op U)) (ha : a ∈ H.obj (op U)) :
      r • a ∈ H.obj (op U) := by
    change G.sieveOfSection (r * a) ∈ J U
    refine J.superset_covering (S := G.sieveOfSection a) ?_ ha
    intro V g hg
    change B.obj.map g.op (r * a) ∈ P V
    rw [map_mul]
    exact (P V).mul_mem_left _ hg
  let K : RingedSiteIdeal B :=
    { sections := fun U ↦
        { carrier := H.obj (op U)
          zero_mem' := G.le_sheafify J (op U) (P U).zero_mem
          add_mem' := fun ha hb ↦ hadd U _ _ ha hb
          smul_mem' := fun r _ ha ↦ hsmul U r _ ha }
      restriction := fun g b hb ↦ H.map g.op hb
      local_mem := hlocal }
  have hK (U : C) (b : B.obj.obj (op U)) : b ∈ K.sections U ↔
      ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
        B.obj.map g.op b ∈ P V := by
    constructor
    · intro hb
      exact ⟨G.sieveOfSection b, hb, fun _ _ h ↦ h⟩
    · rintro ⟨S, hS, hb⟩
      exact J.superset_covering hb hS
  refine ⟨K, hK, ?_⟩
  intro L hL
  have hs : L.sections = K.sections := by
    funext U
    apply Ideal.ext
    intro b
    exact (hL U b).trans (hK U b).symm
  have hext (M N : RingedSiteIdeal B) (h : M.sections = N.sections) : M = N := by
    cases M
    cases N
    dsimp only at h
    cases h
    rfl
  exact hext L K hs

/-- Extension `I B`, the uniquely determined local saturation of the image-generated ideals.
Source: Stacks Project, Modules on Sites, extension of ideals; Algebraization, Tag 099I
(auxiliary; not a blueprint node). -/
noncomputable def extension (I : RingedSiteIdeal R) (φ : R ⟶ B) : RingedSiteIdeal B :=
  Classical.choose (existsUnique_extension I φ).exists

/-- The induced map of quotient ring sheaves `R/I → B/I B` is an isomorphism, expressed
by its local kernel and local lifting criterion. This avoids replacing sheaf quotients
by sectionwise quotients: the latter need not be sheaves.
Source: Stacks Project, Modules on Sites, locally bijective sheaf maps; Algebraization,
Tag 099I (auxiliary; not a blueprint node). -/
def IsQuotientIso (I : RingedSiteIdeal R) (φ : R ⟶ B) : Prop :=
  (∀ (U : C) (a : R.obj.obj (op U)),
    φ.hom.app (op U) a ∈ (I.extension φ).sections U ↔ a ∈ I.sections U) ∧
  (∀ (U : C) (b : B.obj.obj (op U)), ∃ S : Sieve U, S ∈ J U ∧
    ∀ (V : C) (g : V ⟶ U), S g → ∃ a : R.obj.obj (op V),
      B.obj.map g.op b - φ.hom.app (op V) a ∈ (I.extension φ).sections V)

end RingedSiteIdeal
end CategoryTheory
