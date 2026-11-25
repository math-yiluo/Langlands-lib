/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.SchemeDerivedHomGluing
import WeilConjectures.AlgebraicGeometry.OpenUnionRestrictionTransport

/-! # Gluing morphisms between fixed objects on an open union

Source: Stacks Project, Tag 08BW.
(blueprint: lem-sc-open-union-hom-gluing).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem transported_morphism_eq
    {C D B : Type*} [Category C] [Category D] [Category B]
    (r : C ⥤ D) (e : D ⥤ B) [e.Full] [e.Faithful]
    (T : C ⥤ B) (q : r ⋙ e ≅ T) {F H : C} (f : F ⟶ H)
    (a : T.obj F ⟶ T.obj H)
    (h : r.map f = e.preimage (q.hom.app F ≫ a ≫ q.inv.app H)) :
    T.map f = a := by
  apply (cancel_epi (q.hom.app F)).mp
  rw [← q.hom.naturality]
  change e.map (r.map f) ≫ q.hom.app H = _
  rw [h, Functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

-- Perform the cancellation with abstract functors before instantiating derived restrictions.
private theorem transported_morphism_comp_eq
    {C D B : Type*} [Category C] [Category D] [Category B]
    (r : C ⥤ D) (e : D ⥤ B) [e.Full] [e.Faithful]
    (T : C ⥤ B) (q : r ⋙ e ≅ T) {F H : C} (f : F ⟶ H)
    {M N : B} (kF : T.obj F ≅ M) (kH : T.obj H ≅ N) (a : M ⟶ N)
    (h : r.map f = e.preimage
      (q.hom.app F ≫ kF.hom ≫ a ≫ kH.inv ≫ q.inv.app H)) :
    T.map f ≫ kH.hom = kF.hom ≫ a := by
  have ht : T.map f = kF.hom ≫ a ≫ kH.inv :=
    transported_morphism_eq r e T q f _ (by simpa only [Category.assoc] using h)
  rw [ht]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Compatible local maps between restrictions of two fixed ambient objects glue on
an open union. The conclusion constructs a map, and does not construct objects
or local isomorphisms. No lift to a morphism on all of X is asserted.
Source: Stacks Project, Tag 08BW, exactness at the local Hom pair, on W union V.
(blueprint: lem-sc-open-union-hom-gluing).

Proof: Set Y = W union V and pull W and V back to covering opens of Y. Restrict
G and E to Y. Transport the local morphisms a and b through the canonical derived
equivalences for the pulled-back open schemes. Their transported forms are
kW(G) followed by a followed by kW(E) inverse, and similarly for V. The canonical
composition comparison for a chain of open inclusions is obtained from
Modules.overMapCompOverEquiv, overFunctorEquiv, restrictFunctorComp and
restrictFunctorCongr. Its naturality and the equivalence triangle identities
identify compatibility of these transported maps with exactly the hypothesis
using sW and sV. Apply scheme_derived_hom_gluing on Y to the two fixed objects
L(G), L(E) and this compatible pair. Transport its two restriction equations
back and compose on the right with kW(E) and kV(E); cancellation of each
comparison and its inverse gives the displayed equations. Additional derived
categories on the pulled-back opens in Hom universe w are obtained from
nonempty_derivedOpenLocalization and open_derived_localization_adjunction.
Empty opens, a disjoint intersection, and the empty union are included by
Mayer--Vietoris exactness; uniqueness is neither needed nor asserted. -/
theorem exists_open_union_hom
    (X : Scheme.{u}) (W V : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊔ V).toScheme.toRingedSpace))]
    (G E : schemeDerivedCategory X) :
    let L := (schemeOpenRestriction X (W ⊔ V)).mapDerivedCategory
    let JW := (schemeOpenRestriction X W).mapDerivedCategory
    let JV := (schemeOpenRestriction X V).mapDerivedCategory
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    let sW := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_left : W ⊓ V ⟶ W)
    let sV := schemeDerivedOpenRestrictionCompIso X (homOfLE inf_le_right : W ⊓ V ⟶ V)
    let PW := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_left : W ⟶ W ⊔ V)).mapDerivedCategory
    let PV := (schemeOpenOverlapRestriction X
      (homOfLE le_sup_right : V ⟶ W ⊔ V)).mapDerivedCategory
    let kW := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_left : W ⟶ W ⊔ V)
    let kV := schemeDerivedOpenRestrictionCompIso X (homOfLE le_sup_right : V ⟶ W ⊔ V)
    ∀ (a : JW.obj G ⟶ JW.obj E) (b : JV.obj G ⟶ JV.obj E),
      sW.inv.app G ≫ SW.map a ≫ sW.hom.app E =
        sV.inv.app G ≫ SV.map b ≫ sV.hom.app E →
      ∃ (α : L.obj G ⟶ L.obj E),
        PW.map α ≫ kW.hom.app E = kW.hom.app G ≫ a ∧
        PV.map α ≫ kV.hom.app E = kV.hom.app G ≫ b := by
  intro L JW JV SW SV sW sV PW PV kW kV a b hab
  let U := (W ⊔ V).ι ⁻¹ᵁ W
  let T := (W ⊔ V).ι ⁻¹ᵁ V
  have hcover : U ⊔ T = ⊤ := by
    exact (Scheme.Hom.preimage_sup (W ⊔ V).ι).symm.trans
      (W ⊔ V).ι_preimage_self
  obtain ⟨hU, hT, hI, eW, eV, qW, qV, hcompat⟩ :=
    open_union_restriction_transport X W V
  let := hU
  let := hT
  let := hI
  let a' := eW.functor.preimage
    (qW.hom.app (L.obj G) ≫ kW.hom.app G ≫ a ≫
      kW.inv.app E ≫ qW.inv.app (L.obj E))
  let b' := eV.functor.preimage
    (qV.hom.app (L.obj G) ≫ kV.hom.app G ≫ b ≫
      kV.inv.app E ≫ qV.inv.app (L.obj E))
  obtain ⟨α, hαW, hαV⟩ := scheme_derived_hom_gluing (W ⊔ V).toScheme U T hcover
    (L.obj G) (L.obj E) a' b' (hcompat G E a b hab)
  exact ⟨α,
    transported_morphism_comp_eq _ eW.functor PW qW α (kW.app G) (kW.app E) a hαW,
    transported_morphism_comp_eq _ eV.functor PV qV α (kV.app G) (kV.app E) b hαV⟩

end AlgebraicGeometry.Scheme
