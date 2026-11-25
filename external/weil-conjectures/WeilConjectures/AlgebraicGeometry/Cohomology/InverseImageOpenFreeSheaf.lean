/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisFreeComplex
/-! # Inverse image of a represented open free sheaf

Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
private noncomputable def openFreeSectionsEquiv {X : Scheme.{u}} (W : X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (H.openFreeSheaf W ⟶ F) ≃ F.obj.obj (Opposite.op W) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv
    (yoneda.obj W ⋙ AddCommGrpCat.free) F).trans
      (((AddCommGrpCat.adj.whiskerRight X.Opensᵒᵖ).homEquiv _ _).trans yonedaEquiv)

private theorem openFreeSectionsEquiv_naturality {X : Scheme.{u}} (W : X.Opens)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)
    (a : H.openFreeSheaf W ⟶ F) :
    openFreeSectionsEquiv W G (a ≫ f) =
      f.hom.app (Opposite.op W) (openFreeSectionsEquiv W F a) := by
  dsimp only [openFreeSectionsEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def inverseFreeHomEquiv {X Y : Scheme.{u}} (p : Y ⟶ X)
    (W : X.Opens) (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) :
    ((invImage p).obj (H.openFreeSheaf W) ⟶ F) ≃
      (H.openFreeSheaf (p ⁻¹ᵁ W) ⟶ F) :=
  (((TopologicalSpace.Opens.map p.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).homEquiv _ F).trans
      ((openFreeSectionsEquiv W _).trans (openFreeSectionsEquiv (p ⁻¹ᵁ W) F).symm)

private theorem inverseFreeHomEquiv_naturality {X Y : Scheme.{u}} (p : Y ⟶ X)
    (W : X.Opens) {F G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    (f : F ⟶ G) (a : (invImage p).obj (H.openFreeSheaf W) ⟶ F) :
    inverseFreeHomEquiv p W G (a ≫ f) = inverseFreeHomEquiv p W F a ≫ f := by
  let J := (TopologicalSpace.Opens.map p.base).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let adj := (TopologicalSpace.Opens.map p.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  apply (openFreeSectionsEquiv (p ⁻¹ᵁ W) G).injective
  change openFreeSectionsEquiv (p ⁻¹ᵁ W) G
      ((openFreeSectionsEquiv (p ⁻¹ᵁ W) G).symm
        (openFreeSectionsEquiv W (J.obj G) (adj.homEquiv _ G (a ≫ f)))) =
    openFreeSectionsEquiv (p ⁻¹ᵁ W) G
      ((openFreeSectionsEquiv (p ⁻¹ᵁ W) F).symm
        (openFreeSectionsEquiv W (J.obj F) (adj.homEquiv _ F a)) ≫ f)
  rw [Equiv.apply_symm_apply, openFreeSectionsEquiv_naturality, Equiv.apply_symm_apply]
  change openFreeSectionsEquiv W (J.obj G) (adj.homEquiv _ G (a ≫ f)) =
    (J.map f).hom.app (Opposite.op W)
      (openFreeSectionsEquiv W (J.obj F) (adj.homEquiv _ F a))
  erw [adj.homEquiv_naturality_right]
  exact openFreeSectionsEquiv_naturality W (J.map f) (adj.homEquiv _ F a)

/-- Inverse image carries the free sheaf of an open to that of its preimage.
Source: Stacks Project, Tag 04J0 and Section 01F7; inverse-image adjunction.
(blueprint: lem-pc-inverse-image-open-free-sheaf)

Proof: For any abelian sheaf F on Y, the inverse-image/direct-image adjunction
identifies morphisms from the inverse image of the free sheaf of W with morphisms
from that free sheaf to the direct image of F. The Yoneda, free/forgetful and
sheafification adjunctions identify these with sections of the direct image on W,
which by definition are sections of F on p⁻¹W. The same adjunctions identify these
sections with morphisms from the free sheaf of p⁻¹W to F. All identifications are
natural in F, so Yoneda gives the claimed object isomorphism. Empty opens give
zero objects, and the top open gives the usual constant-sheaf comparison. No
flatness, separation or coefficient condition is required.
-/
theorem H.invImage_openFreeSheaf_iso {X Y : Scheme.{u}} (p : Y ⟶ X) (W : X.Opens) :
    Nonempty ((invImage p).obj (H.openFreeSheaf W) ≅ H.openFreeSheaf (p ⁻¹ᵁ W))  := by
  exact ⟨(Coyoneda.ext _ _ (fun a => (inverseFreeHomEquiv p W _).symm a)
    (fun a => inverseFreeHomEquiv p W _ a)
    (fun a => Equiv.apply_symm_apply _ a)
    (fun a => Equiv.symm_apply_apply _ a)
    (fun a f => inverseFreeHomEquiv_naturality p W f a)).symm⟩

end AlgebraicGeometry.Scheme.Modules
