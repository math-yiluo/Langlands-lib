/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMate

/-!

# The mate of a base-change square under a change of coefficients

For adjunctions `c_! ⊣ c^!` and `d_! ⊣ d^!`, functors `ι^*` and `Δ^*` and an isomorphism
`σ : c_! ⋙ Δ^* ≅ ι^* ⋙ d_!`, the mate `c^! ⋙ ι^* ⟶ Δ^* ⋙ d^!` of `σ⁻¹` has component
`ι^* c^! P ⟶ d^! Δ^* P` the `d_! ⊣ d^!` adjoint of `σ⁻¹` followed by `Δ^*` of the counit of
`c_! ⊣ c^!` (`CategoryTheory.Adjunction.mateEquiv_app_eq_homEquiv`). For the fixed square
of a correspondence this is the supported restriction of the trace formula (blueprint
`lemma-local-term-restriction-map--1`). This file proves how it behaves under a change of
coefficients `T` commuting with `c_!`, `d_!` and `Δ^*`.

## Main statements

- `CategoryTheory.Adjunction.map_mateEquiv_app_comp`: if `T` also commutes with `ι^*`,
  compatibly with the base change isomorphisms, `T` carries the exchange restriction to the
  exchange restriction, up to the exchanges of `c^!` and `d^!`.
- `CategoryTheory.Adjunction.exists_map_mateEquiv_app_comp_eq`: if the new `d_!` is full,
  `T` of the exchange restriction factors through the new exchange restriction, without any
  compatibility with the base change isomorphisms.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open CategoryTheory

namespace CategoryTheory


variable {C₂ : Type u₁} {CC : Type u₂} {CF : Type u₃} {CX : Type u₄}
  [Category.{v₁} C₂] [Category.{v₂} CC] [Category.{v₃} CF] [Category.{v₄} CX]
  {C₂' : Type u₅} {CC' : Type u₆} {CF' : Type u₇} {CX' : Type u₈}
  [Category.{v₅} C₂'] [Category.{v₆} CC'] [Category.{v₇} CF'] [Category.{v₈} CX']

/-- The component at `P` of the mate `c^! ⋙ ι^* ⟶ Δ^* ⋙ d^!` of `σ⁻¹ : ι^* ⋙ d_! ⟶ c_! ⋙ Δ^*`
is the `d_! ⊣ d^!` adjoint of `σ⁻¹` followed by `Δ^*` of the counit of `c_! ⊣ c^!`. -/
lemma Adjunction.mateEquiv_app_eq_homEquiv {cL : CC ⥤ C₂} {cR : C₂ ⥤ CC} (a : cL ⊣ cR)
    {dL : CF ⥤ CX} {dR : CX ⥤ CF} (g : dL ⊣ dR) (ι : CC ⥤ CF) (Δ : C₂ ⥤ CX)
    (σ : cL ⋙ Δ ≅ ι ⋙ dL) (P : C₂) :
    (mateEquiv a g (TwoSquare.mk _ _ _ _ σ.inv)).app P =
      g.homEquiv (ι.obj (cR.obj P)) (Δ.obj P) (σ.inv.app (cR.obj P) ≫ Δ.map (a.counit.app P)) := by
  rw [Adjunction.homEquiv_unit]
  simp [mateEquiv_apply]

variable {cL : CC ⥤ C₂} {cR : C₂ ⥤ CC} (a : cL ⊣ cR) {dL : CF ⥤ CX} {dR : CX ⥤ CF}
    (g : dL ⊣ dR) (ι : CC ⥤ CF) (Δ : C₂ ⥤ CX) (σ : cL ⋙ Δ ≅ ι ⋙ dL)
  {cL' : CC' ⥤ C₂'} {cR' : C₂' ⥤ CC'} (a' : cL' ⊣ cR') {dL' : CF' ⥤ CX'} {dR' : CX' ⥤ CF'}
    (g' : dL' ⊣ dR') (ι' : CC' ⥤ CF') (Δ' : C₂' ⥤ CX') (σ' : cL' ⋙ Δ' ≅ ι' ⋙ dL')
  (T₂ : C₂ ⥤ C₂') (TC : CC ⥤ CC') (TF : CF ⥤ CF') (TX : CX ⥤ CX')
  (τc : cL ⋙ T₂ ≅ TC ⋙ cL') (τd : dL ⋙ TX ≅ TF ⋙ dL')
  (τι : ι ⋙ TF ≅ TC ⋙ ι') (τΔ : Δ ⋙ TX ≅ T₂ ⋙ Δ')

/-- **The mate of a base-change isomorphism commutes with a change of coefficients**: let `T` be a
change of coefficients commuting with `c_!`, `d_!`, `ι^*` and `Δ^*` (isomorphisms `τ`), compatibly
with base change `σ`, `σ'` (`hσ`), and write `ρ` and `ρ'` for the mates of `σ⁻¹` and `σ'⁻¹`
(for a fixed square, the supported restrictions). Then the square
```
T ι^* c^! P ---T ρ_P---> T d^! Δ^* P --ex_d--> d'^! T Δ^* P --d'^! τ_Δ--> d'^! Δ'^* T P
    |                                                                         ‖
   τ_ι                                                                        ‖
    v                                                                         ‖
ι'^* T c^! P --ι'^* ex_c--> ι'^* c'^! T P ---------------ρ'_{T P}-----------> d'^! Δ'^* T P
```
commutes, where `ex_c` and `ex_d` are the exchanges `T ⋙ c'^! ⟵ c^! ⋙ T` (the mates of `τ_c⁻¹`
and `τ_d⁻¹`). -/
theorem Adjunction.map_mateEquiv_app_comp
    (hσ : ∀ M : CC, TX.map (σ.hom.app M) ≫ τd.hom.app (ι.obj M) ≫ dL'.map (τι.hom.app M) =
      τΔ.hom.app (cL.obj M) ≫ Δ'.map (τc.hom.app M) ≫ σ'.hom.app (TC.obj M)) (P : C₂) :
    TF.map ((mateEquiv a g (TwoSquare.mk _ _ _ _ σ.inv)).app P) ≫
        (mateEquiv g g' (TwoSquare.mk _ _ _ _ τd.inv)).app (Δ.obj P) ≫
          dR'.map (τΔ.hom.app P) =
      τι.hom.app (cR.obj P) ≫
        ι'.map ((mateEquiv a a' (TwoSquare.mk _ _ _ _ τc.inv)).app P) ≫
          (mateEquiv a' g' (TwoSquare.mk _ _ _ _ σ'.inv)).app (T₂.obj P) := by
  rw [Adjunction.mateEquiv_app_eq_homEquiv a g ι Δ σ P,
    Adjunction.mateEquiv_app_eq_homEquiv a' g' ι' Δ' σ' (T₂.obj P)]
  apply (g'.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_symm_map_comp_mateEquiv_app]
  erw [Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_naturality_left_symm]
  have hc := Adjunction.homEquiv_symm_map_comp_mateEquiv_app a a' TC T₂ τc (𝟙 (cR.obj P))
  simp only [Functor.map_id, Category.id_comp, Adjunction.homEquiv_counit] at hc
  have hσ' : τd.inv.app (ι.obj (cR.obj P)) ≫ TX.map (σ.inv.app (cR.obj P)) =
      dL'.map (τι.hom.app (cR.obj P)) ≫ σ'.inv.app (TC.obj (cR.obj P)) ≫
        Δ'.map (τc.inv.app (cR.obj P)) ≫ τΔ.inv.app (cL.obj (cR.obj P)) := by
    have hI : TX.mapIso (σ.app (cR.obj P)) ≪≫ τd.app _ ≪≫ dL'.mapIso (τι.app (cR.obj P)) =
        τΔ.app _ ≪≫ Δ'.mapIso (τc.app (cR.obj P)) ≪≫ σ'.app _ := Iso.ext (by simpa using hσ _)
    have h2 := congrArg Iso.inv hI
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at h2
    rw [← h2]
    simp [← Functor.map_comp_assoc]
  have hn := σ'.inv.naturality ((mateEquiv a a' (TwoSquare.mk _ _ _ _ τc.inv)).app P)
  simp only [Functor.comp_map] at hn
  have hΔ := τΔ.inv.naturality (a.counit.app P)
  simp only [Functor.comp_map] at hΔ
  rw [Functor.map_comp, ← Category.assoc, hσ']
  erw [Equiv.symm_apply_apply]
  simp only [Category.assoc]
  congr 1
  rw [reassoc_of% hn, ← Functor.map_comp, hc, Functor.map_comp]
  congr 2
  rw [← cancel_mono (τΔ.inv.app P)]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  exact hΔ.symm

include τc in
/-- **The mate of a base-change square under a change of coefficients, up to the source**: let
`T` be a change of coefficients commuting with `c_!`, `d_!` and `Δ^*` (isomorphisms `τ`), with
`d'_!` full. Then `T` of the mate `ρ` of `σ⁻¹`, followed by the exchange `T ⋙ d'^! ⟵ d^! ⋙ T` (the
mate of `τ_d⁻¹`) and `d'^!` of `τ_Δ`, factors through the mate `ρ'` of `σ'⁻¹` for
the new coefficients. No compatibility of `T` with the base change isomorphisms `σ`, `σ'` is needed:
fullness of `d'_!` absorbs it into the factor on the source. That is, there is `s` such that
```
T ι^* c^! P ---T ρ_P---> T d^! Δ^* P --ex_d--> d'^! T Δ^* P --d'^! τ_Δ--> d'^! Δ'^* T P
    |                                                                         ‖
    s                                                                         ‖
    v                                                                         ‖
ι'^* c'^! T P --------------------------ρ'_{T P}----------------------------> d'^! Δ'^* T P
```
commutes. -/
theorem Adjunction.exists_map_mateEquiv_app_comp_eq [dL'.Full] (P : C₂) :
    ∃ s : TF.obj (ι.obj (cR.obj P)) ⟶ ι'.obj (cR'.obj (T₂.obj P)),
      TF.map ((mateEquiv a g (TwoSquare.mk _ _ _ _ σ.inv)).app P) ≫
          (mateEquiv g g' (TwoSquare.mk _ _ _ _ τd.inv)).app (Δ.obj P) ≫
            dR'.map (τΔ.hom.app P) =
        s ≫ (mateEquiv a' g' (TwoSquare.mk _ _ _ _ σ'.inv)).app (T₂.obj P) := by
  rw [Adjunction.mateEquiv_app_eq_homEquiv a g ι Δ σ P,
    Adjunction.mateEquiv_app_eq_homEquiv a' g' ι' Δ' σ' (T₂.obj P)]
  let m := (mateEquiv a a' (TwoSquare.mk _ _ _ _ τc.inv)).app P
  refine ⟨dL'.preimage (τd.inv.app _ ≫ TX.map (σ.inv.app _) ≫ τΔ.hom.app _ ≫
    Δ'.map (τc.hom.app _) ≫ Δ'.map (cL'.map m) ≫ σ'.hom.app _), ?_⟩
  apply (g'.homEquiv _ _).symm.injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_symm_map_comp_mateEquiv_app]
  erw [Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_naturality_left_symm]
  erw [Equiv.symm_apply_apply]
  rw [Functor.map_preimage]
  have hc := Adjunction.homEquiv_symm_map_comp_mateEquiv_app a a' TC T₂ τc (𝟙 (cR.obj P))
  simp only [Functor.map_id, Category.id_comp, Adjunction.homEquiv_counit] at hc
  have hΔ := τΔ.hom.naturality (a.counit.app P)
  simp only [Functor.comp_map] at hΔ
  simp only [Functor.map_comp, Category.assoc]
  erw [Iso.hom_inv_id_app_assoc, hΔ]
  congr 3
  simp only [← Functor.map_comp]
  congr 1
  rw [hc, Iso.hom_inv_id_app_assoc]

end CategoryTheory
