/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products

/-! # Flasqueness of the product of stalks -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Products of the actual module stalk skyscrapers are flasque.
Source: Stacks Project, Tag 0FKR, construction preceding Lemma 20.30.1.
(blueprint: lem-sc-module-cup-godement-object-flasque)
Proof: evaluation on an open set preserves the product of module sheaves.
Its underlying sections identify with families (s_x) indexed by points x of
the open, with s_x in F_x. The action of a section of the structure sheaf is
coordinatewise through its germs. Restriction to a smaller open forgets the
other coordinates. A family on the smaller open lifts by putting zero at
all additional coordinates. Thus every restriction is surjective on abelian
groups, hence an epimorphism; this is flasqueness. This argument includes the
empty open and the empty scheme, whose products have just the zero section. -/
theorem moduleCup_godement_object_flasque (X : Scheme.{u}) (F : X.Modules) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
        (moduleCup_godementObject X F))  := by
  classical
  let D := fun x : X ↦ skyscraper x (F.presheaf.stalk x)
  let E := fun W : X.Opensᵒᵖ ↦
    SheafOfModules.evaluation X.ringCatSheaf W ⋙
      CategoryTheory.forget (ModuleCat.{u} (X.ringCatSheaf.obj.obj W))
  let e := fun W : X.Opensᵒᵖ ↦
    asIso (piComparison (E W) D) ≪≫ Types.productIso (fun x ↦ (E W).obj (D x))
  have coord (W : X.Opensᵒᵖ) (s : Γ(moduleCup_godementObject X F, W.unop)) (x : X) :
      (e W).hom s x = (Pi.π D x).app W.unop s := by
    have hh : (e W).hom ≫ (↾fun t ↦ t x) = (E W).map (Pi.π D x) := by
      dsimp only [e, Iso.trans_hom, asIso_hom]
      rw [Category.assoc, Types.productIso_hom_comp_eval, piComparison_comp_π]
    exact ConcreteCategory.congr_hom hh s
  constructor
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro s
  let t : ∀ x : X, (E U).obj (D x) := fun x ↦
    show SkyscraperSections x (F.presheaf.stalk x) U.unop from
      fun _ ↦ if hv : x ∈ V.unop then (e V).hom s x ⟨hv⟩ else 0
  refine ⟨(e U).inv t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (e V).hom).injective
  funext x
  rw [coord]
  change (Pi.π D x).app V.unop
    ((moduleCup_godementObject X F).presheaf.map i ((e U).inv t)) = _
  have hr := ConcreteCategory.congr_hom ((Pi.π D x).mapPresheaf.naturality i)
    ((e U).inv t)
  change (Pi.π D x).app V.unop
      ((moduleCup_godementObject X F).presheaf.map i ((e U).inv t)) =
    (D x).presheaf.map i ((Pi.π D x).app U.unop ((e U).inv t)) at hr
  rw [hr]
  rw [← coord U]
  have he : (e U).hom ((e U).inv t) = t := by
    exact ConcreteCategory.congr_hom ((e U).inv_hom_id) t
  rw [he]
  change (fun hx : PLift (x ∈ V.unop) ↦
      if hv : x ∈ V.unop then (e V).hom s x ⟨hv⟩ else 0) = (e V).hom s x
  funext hx
  simp [hx.down]


end
end AlgebraicGeometry.Scheme.Modules
