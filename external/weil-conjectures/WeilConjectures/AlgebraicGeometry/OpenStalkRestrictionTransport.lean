/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison

/-! # Transport of open-site stalk comparisons through further restriction

Source: Stacks Project, Sheaves Tag 00A0 (3), (5), and Tag 0096.
(blueprint: lem-sc-open-stalk-restriction-transport).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem descend_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (P : D ⥤ C) (adj : R ⊣ P) [IsIso adj.counit]
    (F G : D ⥤ E) (a : R ⋙ F ≅ R ⋙ G) :
    ∃ d : F ≅ G, ∀ M : C, d.hom.app (R.obj M) = a.hom.app M := by
  let e := asIso adj.counit
  let d : F ≅ G :=
    F.leftUnitor.symm ≪≫ Functor.isoWhiskerRight e.symm F ≪≫
      Functor.associator P R F ≪≫ Functor.isoWhiskerLeft P a ≪≫
      (Functor.associator P R G).symm ≪≫ Functor.isoWhiskerRight e G ≪≫
      G.leftUnitor
  refine ⟨d, ?_⟩
  intro M
  dsimp [d]
  simp only [Category.id_comp, Category.comp_id]
  simp only [e, asIso_hom, asIso_inv, NatIso.isIso_inv_app]
  change F.map (inv (adj.counit.app (R.obj M))) ≫
    a.hom.app (P.obj (R.obj M)) ≫ G.map (adj.counit.app (R.obj M)) = a.hom.app M
  have h := adj.left_triangle_components M
  have hi : inv (adj.counit.app (R.obj M)) = R.map (adj.unit.app M) := by
    apply (cancel_mono (adj.counit.app (R.obj M))).1
    simp [h]
  have hn := a.hom.naturality (adj.unit.app M)
  change F.map (R.map (adj.unit.app M)) ≫ a.hom.app (P.obj (R.obj M)) =
    a.hom.app M ≫ G.map (R.map (adj.unit.app M)) at hn
  rw [hi, ← Category.assoc, hn, Category.assoc,
    ← G.map_comp, h, G.map_id]
  exact Category.comp_id _

private def restriction_comp_iso
    (X : Scheme.{u}) (U V W : X.Opens) (hVU : V ≤ U) (hWV : W ≤ V) (hWU : W ≤ U) :
    SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU) ⋙
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWV) ≅
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWU) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_adjunction
    (X : Scheme.{u}) (U V : X.Opens) (hVU : V ≤ U) :
    ∃ P : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
        SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U),
      ∃ adj : SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU) ⊣ P, IsIso adj.counit := by
  let A := Modules.overEquiv U
  let B := Modules.overEquiv V
  let j := X.homOfLE hVU
  let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
  let P := B.functor ⋙ Modules.pushforward j ⋙ A.inverse
  let e : (A.functor ⋙ Modules.restrictFunctor j) ⋙ B.inverse ≅ R :=
    Functor.isoWhiskerRight (Modules.overMapCompOverEquiv (homOfLE hVU)).symm B.inverse ≪≫
      Functor.associator R B.functor B.inverse ≪≫
      Functor.isoWhiskerLeft R B.unitIso.symm ≪≫ R.rightUnitor
  let adj : R ⊣ P :=
    ((A.toAdjunction.comp (Modules.restrictAdjunction j)).comp B.symm.toAdjunction).ofNatIsoLeft e
  have : P.Full := inferInstance
  have : P.Faithful := inferInstance
  exact ⟨P, adj, inferInstance⟩

/-- An arbitrary comparison on an intermediate open can be transported through a further
restriction to the canonical comparison `openModuleStalkRestrictionComparison`.

Source: Stacks Project, Sheaves Tag 00A0 (3), (5), `lemma-restrict`, and Tag 0096,
`lemma-adjoint-pullback-pushforward-modules` (open-immersion pushforward).
(blueprint: lem-sc-open-stalk-restriction-transport).

Proof: Use the slice/open-subspace equivalences. The final functor of neighbourhoods
inside W gives the additive restriction-stalk isomorphism. Its germ formula,
checked on a common neighbourhood for a scalar and a vector, makes it linear
after the open-immersion stalk-ring scalar transports. The same formula proves
naturality. These canonical isomorphisms e are
`openModuleStalkRestrictionComparison`. The comparison c of two slice restrictions is
the sectionwise identity; associativity of inclusions gives its naturality. The canonical
W-to-V stalk comparison d0 satisfies the displayed law for the canonical V-to-U comparison e0:
both sides take a section germ to that same germ on U.

For an arbitrary comparison a on V, put R = restriction from U to V. Transport
open-immersion module pushforward back to the slice sites to obtain its right
adjoint P, with unit eta and invertible counit epsilon : R P --> Id. Define an
automorphism b of the V-stalk functor S by the composite
S(epsilon) inverse, e0 whiskered by P, a inverse whiskered by P, S(epsilon).
Naturality makes b a natural automorphism. Naturality of e0 and a at eta_F,
and the triangle identity R(eta_F) followed by epsilon_(R F) = identity, give
b_(R F) followed by a_F = e0_F. Thus d = d0 followed by b has the required law.
This argument applies to all module sheaves and all comparisons a: no free source,
finite presentation, local existence of a morphism, or prescribed stalk map is
used. If V=W the same counit calculation applies; the hypothesis x in W excludes
empty neighbourhoods. The canonical comparisons are determined by the germ formula;
d is adjusted to a by the explicit adjunction construction above.
-/
theorem exists_openStalk_restriction_transport
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U) :
    ∀ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U)
      (a : SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU) ⋙
        openModuleStalkFunctor X V ⟨x, hxV⟩ ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
      (W : X.Opens) (hxW : x ∈ W) (hWV : W ≤ V) (hWU : W ≤ U),
      let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU)
      let Q := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWV)
      let P := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU)
      ∃ (c : R ⋙ Q ≅ P)
        (d : Q ⋙ openModuleStalkFunctor X W ⟨x, hxW⟩ ≅
          openModuleStalkFunctor X V ⟨x, hxV⟩),
        (∀ M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U),
          c.hom.app M = 𝟙 _) ∧
        ∀ M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U),
          (openModuleStalkFunctor X W ⟨x, hxW⟩).map (c.hom.app M) ≫
              (openModuleStalkRestrictionComparison X U W hWU x hxU hxW).hom.app M =
            d.hom.app (R.obj M) ≫ a.hom.app M := by
  classical
  -- Any family of comparisons works: descend its composite with a.inv along restriction.
  -- This avoids a separate coherence theorem for canonical germ comparisons.
  let e := fun (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U) ↦
    openModuleStalkRestrictionComparison X U W hWU x hxU hxW
  intro V hxV hVU a W hxW hWV hWU
  dsimp only
  let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
  let Q := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWV)
  let S := openModuleStalkFunctor X W ⟨x, hxW⟩
  let T := openModuleStalkFunctor X V ⟨x, hxV⟩
  let c := restriction_comp_iso X U V W hVU hWV hWU
  obtain ⟨J, adj, h⟩ := restriction_adjunction X U V hVU
  let t : R ⋙ (Q ⋙ S) ≅ R ⋙ T :=
    (Functor.associator R Q S).symm ≪≫ Functor.isoWhiskerRight c S ≪≫
      e W hxW hWU ≪≫ a.symm
  obtain ⟨d, hd⟩ := descend_iso R J adj (Q ⋙ S) T t
  refine ⟨c, d, fun M ↦ rfl, fun M ↦ ?_⟩
  have hlaw : S.map (c.hom.app M) ≫ (e W hxW hWU).hom.app M =
      d.hom.app (R.obj M) ≫ a.hom.app M := by
    rw [hd M]
    simp only [t, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact hlaw

end
end AlgebraicGeometry.Scheme
