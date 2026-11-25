/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Underlying modules of directed colimits of algebra sheaves

Source: Stacks Project, Modules, Lemma 01AH; Sheaves, Sections 009D and 009E
(blueprint: stage3-sheaf-algebras-directed-colimit-module-core).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace CategoryTheory

/-- Forgetting sheaf modules preserves colimits, by the sheafification counit. -/
private theorem module_toSheaf_preservesColimit
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {I : Type u} [Category I] (F : I ⥤ SheafOfModules.{u} R) :
    PreservesColimit F (SheafOfModules.toSheaf R) := by
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let G := SheafOfModules.toSheaf R
  let H := F ⋙
    (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj))
  have : PreservesColimit H (L ⋙ G) := by
    change PreservesColimit H
      (PresheafOfModules.toPresheaf R.obj ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    infer_instance
  have : PreservesColimit (H ⋙ L) G :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit H))
      (isColimitOfPreserves (L ⋙ G) (colimit.isColimit H))
  exact preservesColimit_of_iso_diagram G
    (Functor.associator F
      (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) L ≪≫
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit))

/-- Forgetting ring sheaves preserves directed colimits, by compatible sheafification. -/
private theorem ring_toAb_preservesColimit
    {X : Type u} [TopologicalSpace X]
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    PreservesColimit F (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) := by
  let J := Opens.grothendieckTopology X
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}
  have : PreservesLimits U := inferInstance
  have : PreservesFilteredColimits U :=
    comp_preservesFilteredColimits (forget₂ CommRingCat RingCat)
      (forget₂ RingCat AddCommGrpCat)
  have : ∀ V, PreservesColimitsOfShape (J.Cover V)ᵒᵖ U := fun _ ↦ inferInstance
  have : J.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification J U
  let L := presheafToSheaf J CommRingCat.{u}
  let G := sheafCompose J U
  let H := F ⋙ sheafToPresheaf J CommRingCat
  have : PreservesColimit H (L ⋙ G) :=
    preservesColimit_of_natIso H
      (sheafComposeNatIso J U (sheafificationAdjunction J CommRingCat)
        (sheafificationAdjunction J AddCommGrpCat))
  have : PreservesColimit (H ⋙ L) G :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit H))
      (isColimitOfPreserves (L ⋙ G) (colimit.isColimit H))
  exact preservesColimit_of_iso_diagram G
    (Functor.associator F (sheafToPresheaf J CommRingCat) L ≪≫
      Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J CommRingCat).counit))

/-- The underlying module cocone of the sheafified algebra colimit is a colimit.
Proof: choose i₀ in the nonempty directed index. The composites of the stage structure
maps with p's legs coincide: for any two stages, pass to a common upper bound and use
naturality. Their common value gives O.obj → p.pt, and the fact that ι is a morphism in
Under O, together with hι, identifies σ with its composite with the sheafification unit.
Equip p.pt sectionwise with the resulting O-module structure. By hp, each section is
represented at a stage and equality of representatives is detected at a later stage.
A compatible family of module maps therefore descends uniquely to p.pt: define its value
on a representative using the stage map; the equality criterion proves well-definedness,
and a common upper bound proves additivity and O-linearity. Uniqueness also proves
compatibility with restrictions, so this is the presheaf module colimit.
Module sheafification is left adjoint and preserves this colimit. Ring sheafification and
module sheafification have the same underlying abelian sheafification. Their canonical
comparison is O-linear: check on local stage representatives and use hι and the Under O
identities, then glue. It is an isomorphism and carries the sheafified presheaf legs to ι.
Transporting the module colimit along this cocone isomorphism gives the conclusion.
Source: Stacks Project, Modules, Lemma 01AH
(blueprint: stage3-sheaf-algebras-directed-colimit-module-core). -/
theorem sheafAlgebras_directed_colimit_module_core
    (X : Type u) [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ Under O)
    (p : Cocone (F ⋙ Under.forget O ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat))
    (σ : O ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt)
    (ι : F ⟶ (Functor.const I).obj (Under.mk σ))
    (hp : ∀ U : Opens X, Nonempty (IsColimit
      (((evaluation (Opens X)ᵒᵖ CommRingCat).obj (Opposite.op U)).mapCocone p)))
    (hι : ∀ i : I, (ι.app i).right.hom = p.ι.app i ≫
      toSheafify (Opens.grothendieckTopology X) p.pt) :
    Nonempty (IsColimit
      ((commAlgebraSheafModuleFunctor O).mapCocone (Cocone.mk (Under.mk σ) ι))) := by
  set_option backward.isDefEq.respectTransparency false in
  classical
  let J := Opens.grothendieckTopology X
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}
  let c := Cocone.mk (Under.mk σ) ι
  let d := (Under.forget O).mapCocone c
  have he : IsColimit (Sheaf.sheafifyCocone (F := F ⋙ Under.forget O) p) :=
    Sheaf.isColimitSheafifyCocone (F := F ⋙ Under.forget O) p
      (evaluationJointlyReflectsColimits p (fun V ↦ (hp V.unop).some))
  have hd : IsColimit d := IsColimit.ofIsoColimit he
    (Cocone.ext (Iso.refl _) (by
      intro i
      apply Sheaf.hom_ext
      change ((Sheaf.sheafifyCocone (F := F ⋙ Under.forget O) p).ι.app i).hom =
        (ι.app i).right.hom
      rw [Sheaf.sheafifyCocone_ι_app_val (F := F ⋙ Under.forget O), hι]))
  have : PreservesColimit (F ⋙ Under.forget O) (sheafCompose J U) :=
    ring_toAb_preservesColimit (F ⋙ Under.forget O)
  have ha : IsColimit ((sheafCompose J U).mapCocone d) :=
    isColimitOfPreserves (sheafCompose J U) hd
  have : PreservesColimit (F ⋙ commAlgebraSheafModuleFunctor O)
      (SheafOfModules.toSheaf R) :=
    module_toSheaf_preservesColimit R (F ⋙ commAlgebraSheafModuleFunctor O)
  have : ReflectsColimit (F ⋙ commAlgebraSheafModuleFunctor O)
      (SheafOfModules.toSheaf R) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact ⟨isColimitOfReflects (SheafOfModules.toSheaf R) ha⟩

end CategoryTheory
