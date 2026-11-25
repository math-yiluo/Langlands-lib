/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleGeometricFibreConstantSections
import all WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionSquare

/-! # Equal pullbacks of geometric constant sections

Source: Stacks Project, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-geometric-section-two-pullbacks).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

local notation "L" => Scheme.etaleSetPullback
local notation "I[" X "]" => Scheme.Etale.mk (𝟙 X)
set_option quotPrecheck false in
local notation "η[" X "," Y "]" e =>
  Adjunction.unit
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ e) _
      (Scheme.smallGrothendieckTopology @Etale X)
      (Scheme.smallGrothendieckTopology @Etale Y))
set_option quotPrecheck false in
local notation "R[" X "," Y "," e "," G "]" =>
  (((η[X,Y] e).app G).hom.app (op I[X]) ≫
    ((L e).obj G).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift e (𝟙 Y)
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp <;> rfl) :
        I[Y] ⟶ (MorphismProperty.Over.pullback @Etale ⊤ e).obj I[X]).op)

set_option quotPrecheck false in
local notation "P[" f "," k "," r "," hk "," F "]" =>
  (fun a => Eq.mp
    (congrArg (fun e => ((L e).obj F).obj.obj (op I[_])) (show k ≫ f = r from hk))
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2
      _ _ _ f k).hom.app F).hom.app (op I[_]))
      (R[_,_,k,(L f).obj F] a)))

set_option backward.isDefEq.respectTransparency false in
/-- Two maps over an algebraically closed field pull back a section on a connected
scheme to the same section. The receiving scheme may be empty or disconnected.

Source: Stacks Project, Tag 0A3H, final paragraph, and Tag 03P5.
(blueprint: lem-weil-pbc-etale-geometric-section-two-pullbacks).

Proof:
The bijection in etaleGeometricFibreConstantSections writes b as the constant section
of a stalk element e. Its naturality equation along each v_i identifies the composite
pullback with the section of value e, initially on the base change of the identity
etale object of U. Restrict to the identity object of E using its canonical pullback
lift. Naturality of the composition isomorphism, of the inverse constant comparison,
and of toSheafify moves this restriction through each map. Both v_i followed by h
are w, so both resulting sections are the same constant section of e under the same
comparison on E. Transport by associativity to w followed by q and then by ht to t.
No connectedness of E enters; for E empty the equality remains valid. -/
theorem etaleSet_geometricSection_two_pullbacks
    {S U E : Scheme.{u}} (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (q : Spec (.of Ω) ⟶ S) (h : U ⟶ Spec (.of Ω)) [ConnectedSpace U]
    (w : E ⟶ Spec (.of Ω)) (v₁ v₂ : E ⟶ U)
    (hw₁ : v₁ ≫ h = w) (hw₂ : v₂ ≫ h = w)
    (t : E ⟶ S) (ht : w ≫ q = t)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (b : ((L (h ≫ q)).obj F).obj.obj (op I[U])) :
    P[h ≫ q,v₁,t,(by rw [← Category.assoc, hw₁, ht]),F] b =
      P[h ≫ q,v₂,t,(by rw [← Category.assoc, hw₂, ht]),F] b := by
  classical
  obtain ⟨α, _, hα⟩ := etaleGeometricFibreConstantSections S Ω q
  obtain ⟨e, he⟩ := (hα U h F).1.2 b
  subst b
  subst t
  let z := ((α E w).inv.app F).hom.app (op I[E])
    ((toSheafify E.smallEtaleTopology
      ((Functor.const E.Etaleᵒᵖ).obj
        ((Scheme.pointSmallEtale q).sheafFiber.obj F))).app (op I[E]) e)
  have aux (v : E ⟶ U) (hw : v ≫ h = w) :
      P[h ≫ q,v,w ≫ q,(by rw [← Category.assoc, hw]),F]
        (((α U h).inv.app F).hom.app (op I[U])
          ((toSheafify U.smallEtaleTopology
            ((Functor.const U.Etaleᵒᵖ).obj
              ((Scheme.pointSmallEtale q).sheafFiber.obj F))).app (op I[U]) e)) = z := by
    let m : I[E] ⟶ (MorphismProperty.Over.pullback @Etale ⊤ v).obj I[U] :=
      MorphismProperty.Over.homMk
        (pullback.lift v (𝟙 E)
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp)
    have hn := (hα U h F).2 E v e
    have hn' := congrArg (((L (v ≫ h ≫ q)).obj F).obj.map m.op) hn
    have hc := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
      S U E (h ≫ q) v).hom.app F).hom.naturality m.op
    have hr := (((α E (v ≫ h)).inv.app F ≫
      eqToHom (congrArg (fun k : E ⟶ S => (L k).obj F)
        (Category.assoc v h q))).hom).naturality m.op
    have ht := (toSheafify E.smallEtaleTopology
      ((Functor.const E.Etaleᵒᵖ).obj
        ((Scheme.pointSmallEtale q).sheafFiber.obj F))).naturality m.op
    simp only [← CategoryTheory.types_comp_apply] at hn'
    rw [← hc, ← hr] at hn'
    simp only [CategoryTheory.types_comp_apply] at hn'
    have ht' := ConcreteCategory.congr_hom ht e
    simp only [Functor.const_obj_map,
      CategoryTheory.types_comp_apply] at ht'
    change _ = (((((Scheme.pointSmallEtale q).sheafFiber ⋙
      constantSheaf E.smallEtaleTopology (Type (u + 1))).obj F).obj.map m.op)
        ((toSheafify E.smallEtaleTopology
          ((Functor.const E.Etaleᵒᵖ).obj
            ((Scheme.pointSmallEtale q).sheafFiber.obj F))).app
              (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj I[U])) e)) at ht'
    rw [← ht'] at hn'
    simp only [CategoryTheory.types_comp_apply]
    erw [hn']
    change Eq.mp _
      (((eqToHom (congrArg (fun k : E ⟶ S => (L k).obj F)
        (Category.assoc v h q))).hom.app (op I[E]))
          (((α E (v ≫ h)).inv.app F).hom.app (op I[E])
            ((toSheafify E.smallEtaleTopology
              ((Functor.const E.Etaleᵒᵖ).obj
                ((Scheme.pointSmallEtale q).sheafFiber.obj F))).app (op I[E]) e))) = z
    rw [section_eqToHom ((v ≫ h) ≫ q) (v ≫ h ≫ q) (Category.assoc v h q)]
    have hz (j j' : E ⟶ Spec (.of Ω)) (hj : j = j') :
        Eq.mp (congrArg (fun k => ((L (k ≫ q)).obj F).obj.obj (op I[E])) hj)
          (((α E j).inv.app F).hom.app (op I[E])
            ((toSheafify E.smallEtaleTopology
              ((Functor.const E.Etaleᵒᵖ).obj
                ((Scheme.pointSmallEtale q).sheafFiber.obj F))).app (op I[E]) e)) =
        ((α E j').inv.app F).hom.app (op I[E])
          ((toSheafify E.smallEtaleTopology
            ((Functor.const E.Etaleᵒᵖ).obj
              ((Scheme.pointSmallEtale q).sheafFiber.obj F))).app (op I[E]) e) := by
      cases hj
      rfl
    have hm {A B C : Type (u + 1)} (hab : A = B) (hbc : B = C) (x : A) :
        Eq.mp hbc (Eq.mp hab x) = Eq.mp (hab.trans hbc) x := by
      cases hab
      cases hbc
      rfl
    rw [hm]
    exact hz (v ≫ h) w hw
  exact (aux v₁ hw₁).trans (aux v₂ hw₂).symm

end AlgebraicGeometry
