/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-!
# Compatibility of affine-chart pullback comparisons with units

Source: Stacks Project, Sheaves, Tags 00A0 and 0097.
(blueprint: lem-weil-pbc-module-pullback-affine-chart-unit).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The comparison between the two pullback routes through the affine-chart square
carries the unit on the source chart to the restriction of the unit of `f`.
Source: Stacks Project, Sheaves, Tags 00A0 and 0097.
(blueprint: lem-weil-pbc-module-pullback-affine-chart-unit).

Proof: compose the restriction adjunction for the source chart with the pullback
adjunction for `Spec.map (f.appLE ...)`. Compose the pullback adjunction for `f` with
restriction along the target chart. The chart square identifies their right adjoints.
The unit equation for uniqueness of left adjoints says that the comparison takes the
first composite unit to the second composite unit. The restriction-adjunction units
are restrictions of sections. The two sectionsRestrictFromSpecLinearEquiv maps are
inverse restrictions, so the first composite unit is the unit of Spec.map applied to
the inverse image of s under eV, and the second becomes the restriction to U of the
unit of f after applying eU. This gives the displayed equality. -/
theorem affineChart_pullback_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.affineOpens) (U : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) (G : Y.Modules) (s : Γ(G, V.1)) :
    let jV := V.2.fromSpec
    let jU := U.2.fromSpec
    let ρ := f.appLE V.1 U.1 hUV
    let ψ := Spec.map ρ
    let hsq : ψ ≫ jV = jU ≫ f := V.2.SpecMap_appLE_fromSpec f U.2 hUV
    let adj₁ := (restrictAdjunction jV).comp (pullbackPushforwardAdjunction ψ)
    let adj₂ := (pullbackPushforwardAdjunction f).comp (restrictAdjunction jU)
    let rightIso : pushforward ψ ⋙ pushforward jV ≅ pushforward jU ⋙ pushforward f :=
      pushforwardComp ψ jV ≪≫ pushforwardCongr hsq ≪≫ (pushforwardComp jU f).symm
    let k : restrictFunctor jV ⋙ pullback ψ ≅ pullback f ⋙ restrictFunctor jU :=
      adj₁.leftAdjointUniq (adj₂.ofNatIsoRight rightIso.symm)
    let eV := sectionsRestrictFromSpecLinearEquiv G V.2
    let eU := sectionsRestrictFromSpecLinearEquiv ((pullback f).obj G) U.2
    eU (((k.hom.app G).app ⊤)
      ((pullbackUnit ψ (G.restrict jV)).app ⊤ (eV.symm s))) =
      ((pullback f).obj G).presheaf.map (homOfLE hUV).op ((pullbackUnit f G).app V.1 s) := by
  classical
  dsimp only
  let jV := V.2.fromSpec
  let jU := U.2.fromSpec
  let ρ := f.appLE V.1 U.1 hUV
  let ψ := Spec.map ρ
  let hsq : ψ ≫ jV = jU ≫ f := V.2.SpecMap_appLE_fromSpec f U.2 hUV
  let adj₁ := (restrictAdjunction jV).comp (pullbackPushforwardAdjunction ψ)
  let adj₂ := (pullbackPushforwardAdjunction f).comp (restrictAdjunction jU)
  let rightIso : pushforward ψ ⋙ pushforward jV ≅ pushforward jU ⋙ pushforward f :=
    pushforwardComp ψ jV ≪≫ pushforwardCongr hsq ≪≫ (pushforwardComp jU f).symm
  let k : restrictFunctor jV ⋙ pullback ψ ≅ pullback f ⋙ restrictFunctor jU :=
    adj₁.leftAdjointUniq (adj₂.ofNatIsoRight rightIso.symm)
  let eV := sectionsRestrictFromSpecLinearEquiv G V.2
  let eU := sectionsRestrictFromSpecLinearEquiv ((pullback f).obj G) U.2
  change eU (((k.hom.app G).app ⊤)
    ((pullbackUnit ψ (G.restrict jV)).app ⊤ (eV.symm s))) = _
  have hu := adj₁.unit_leftAdjointUniq_hom_app (adj₂.ofNatIsoRight rightIso.symm) G
  have hv := congrArg (fun q ↦ q.app V.1 s) hu
  simp only [adj₁, adj₂, Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    Hom.comp_app, pushforward_map_app, Functor.comp_map, ConcreteCategory.comp_apply] at hv
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Hom.comp_app,
    ConcreteCategory.comp_apply, Adjunction.comp_unit_app, pushforward_map_app] at hv
  have hpreV : jV ⁻¹ᵁ V.1 = ⊤ := V.2.fromSpec_preimage_self
  have hpre : ψ ⁻¹ᵁ (jV ⁻¹ᵁ V.1) = ⊤ := by rw [hpreV]; rfl
  have H := congrArg (fun z ↦ eU
    (((pullback f ⋙ restrictFunctor jU).obj G).presheaf.map (eqToHom hpre.symm).op z)) hv
  have hV : (G.restrict jV).presheaf.map (eqToHom hpreV.symm).op
      (((restrictAdjunction jV).unit.app G).app V.1 s) = eV.symm s := by
    change G.presheaf.map (jV.opensFunctor.map (eqToHom hpreV.symm)).op
        (G.presheaf.map (homOfLE (jV.image_preimage_le V.1)).op s) =
      G.presheaf.map (homOfLE (V.2.fromSpec_image_le ⊤)).op s
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hη := (pullbackUnit ψ (G.restrict jV)).mapPresheaf.naturality
    (eqToHom hpreV.symm).op
  have hη' := congrArg (fun q ↦ q
    (((restrictAdjunction jV).unit.app G).app V.1 s)) hη
  have hk := (k.hom.app G).mapPresheaf.naturality (eqToHom hpre.symm).op
  have hk' := congrArg (fun q ↦ q
    ((pullbackUnit ψ (G.restrict jV)).app (jV ⁻¹ᵁ V.1)
      (((restrictAdjunction jV).unit.app G).app V.1 s))) hk
  change ((k.hom.app G).app ⊤)
      (((pullback ψ).obj (G.restrict jV)).presheaf.map (eqToHom hpre.symm).op
        ((pullbackUnit ψ (G.restrict jV)).app (jV ⁻¹ᵁ V.1)
          (((restrictAdjunction jV).unit.app G).app V.1 s))) =
    (((pullback f ⋙ restrictFunctor jU).obj G).presheaf.map (eqToHom hpre.symm).op
      (((k.hom.app G).app (ψ ⁻¹ᵁ (jV ⁻¹ᵁ V.1)))
        ((pullbackUnit ψ (G.restrict jV)).app (jV ⁻¹ᵁ V.1)
          (((restrictAdjunction jV).unit.app G).app V.1 s)))) at hk'
  change (pullbackUnit ψ (G.restrict jV)).app ⊤
      ((G.restrict jV).presheaf.map (eqToHom hpreV.symm).op
        (((restrictAdjunction jV).unit.app G).app V.1 s)) =
    ((pullback ψ).obj (G.restrict jV)).presheaf.map (eqToHom hpre.symm).op
      ((pullbackUnit ψ (G.restrict jV)).app (jV ⁻¹ᵁ V.1)
        (((restrictAdjunction jV).unit.app G).app V.1 s)) at hη'
  rw [hV] at hη'
  rw [← hη'] at hk'
  have H' := (congrArg eU hk').trans H
  let P := (pullback f).obj G
  have hR (z : Γ(P, f ⁻¹ᵁ V.1)) :
      eU ((P.restrict jU).presheaf.map (eqToHom hpre.symm).op
        ((rightIso.inv.app (P.restrict jU)).app V.1
          (((restrictAdjunction jU).unit.app P).app (f ⁻¹ᵁ V.1) z))) =
        P.presheaf.map (homOfLE hUV).op z := by
    simp only [rightIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Hom.comp_app, ConcreteCategory.comp_apply, pushforwardComp_hom_app_app,
      pushforwardComp_inv_app_app, pushforwardCongr_inv_app_app]
    have hU : U.1 ≤ jU ''ᵁ ⊤ :=
      (U.2.opensRange_fromSpec.symm.trans (Scheme.Hom.image_top_eq_opensRange _).symm).le
    have heq : ψ ⁻¹ᵁ (jV ⁻¹ᵁ V.1) = jU ⁻¹ᵁ (f ⁻¹ᵁ V.1) :=
      congrArg (fun g ↦ g ⁻¹ᵁ V.1) hsq
    change P.presheaf.map (homOfLE hU).op
        (P.presheaf.map (jU.opensFunctor.map (eqToHom hpre.symm)).op
          (P.presheaf.map (jU.opensFunctor.map (eqToHom heq)).op
            (P.presheaf.map (homOfLE (jU.image_preimage_le (f ⁻¹ᵁ V.1))).op z))) =
      P.presheaf.map (homOfLE hUV).op z
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  exact H'.trans (hR ((pullbackUnit f G).app V.1 s))

end AlgebraicGeometry.Scheme.Modules
