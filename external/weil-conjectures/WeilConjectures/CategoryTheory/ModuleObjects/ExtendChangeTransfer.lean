/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.HomEquivCompIso
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClColimit

/-!
# The maps `S ⊗_{R'} M ⟶ T ⊗_{R'} M` as adjoint transfers

Let `R, R', S, T` be commutative algebra objects with morphisms `a : R ⟶ S`, `b : S ⟶ T`,
`a' : R' ⟶ S`, and `ι = a ≫ b`, `ι' = a' ≫ b`. The extensions of scalars satisfy
`(T ⊗_S -) ∘ (S ⊗_R -) ≅ T ⊗_R -` (`CategoryTheory.Mod.extendScalarsCompIsoOfEq`), compatibly
with the units (`CategoryTheory.Mod.extendUnitHom_extendScalarsCompIsoOfEq_hom_app`).

The adjoint transfer `CategoryTheory.Adjunction.compIsoTransfer` of these isomorphisms along the
extension-restriction adjunctions is an `R`-linear map `Res_a(S ⊗_{R'} M) ⟶ Res_ι(T ⊗_{R'} M)`;
its underlying map is the map `x ⊗ m ↦ b(x) ⊗ m` (`CategoryTheory.Mod.extendChangeHom`), see
`CategoryTheory.Mod.compIsoTransfer_extendRestrictAdjunction_hom`. In particular, the maps
`extendChangeHom` are `R`-linear.
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]

section Units

variable {R S T : C} [MonObj R] [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S]

/-- The comparison `(S ⊗_R -) ∘ (T ⊗_S -) ≅ T ⊗_R -` is compatible with the units:
`m ↦ 1 ⊗ m ↦ 1 ⊗ (1 ⊗ m)`. -/
@[reassoc]
lemma extendUnitHom_extendScalarsComp_hom_app (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T)
    [IsMonHom ψ] (M : Mod C R) :
    extendUnitHom (φ ≫ ψ) M ≫ ((extendScalarsComp φ ψ).hom.app M).hom =
      extendUnitHom φ M ≫ extendUnitHom ψ (extendScalarsObj φ M) := by
  have h := congrArg Hom.hom (Adjunction.unit_leftAdjointUniq_hom_app
    (extendRestrictAdjunction (φ ≫ ψ))
    (((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
      (comapComp φ ψ).symm) M)
  simp only [comp_hom', comap_map_hom, extendRestrictAdjunction_unit_app_hom,
    Adjunction.ofNatIsoRight_unit, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
    Iso.symm_hom, comapComp_inv_app_hom,
    NatTrans.comp_app] at h
  exact h.trans (Category.comp_id _)

omit [IsCommMonObj S] in
/-- The comparison `S ⊗_R - ≅ S ⊗_R -` along equal morphisms `φ = ψ` is compatible with the
units. -/
@[reassoc]
lemma extendUnitHom_extendScalarsIsoOfEq_hom_app {φ ψ : R ⟶ S} [IsMonHom φ] [IsMonHom ψ]
    (h : φ = ψ) (M : Mod C R) :
    extendUnitHom φ M ≫ ((extendScalarsIsoOfEq h).hom.app M).hom = extendUnitHom ψ M := by
  have h' := congrArg Hom.hom (Adjunction.unit_leftAdjointUniq_hom_app
    (extendRestrictAdjunction φ)
    ((extendRestrictAdjunction ψ).ofNatIsoRight (comapCongr h).symm) M)
  simp only [comp_hom', comap_map_hom, extendRestrictAdjunction_unit_app_hom,
    Adjunction.ofNatIsoRight_unit, Functor.whiskerLeft_app, Iso.symm_hom, NatTrans.comp_app,
    comapCongr_inv_app_hom] at h'
  exact h'.trans (Category.comp_id _)

/-- The isomorphism `(S ⊗_R -) ∘ (T ⊗_S -) ≅ T ⊗_R -` for `a ≫ b = ι`. -/
noncomputable def extendScalarsCompIsoOfEq {a : R ⟶ S} {b : S ⟶ T} {ι : R ⟶ T} [IsMonHom a]
    [IsMonHom b] [IsMonHom ι] (h : a ≫ b = ι) :
    extendScalars a ⋙ extendScalars b ≅ extendScalars ι :=
  (extendScalarsComp a b).symm ≪≫ extendScalarsIsoOfEq h

/-- The isomorphism `extendScalarsCompIsoOfEq` is compatible with the units. -/
@[reassoc]
lemma extendUnitHom_extendScalarsCompIsoOfEq_hom_app {a : R ⟶ S} {b : S ⟶ T} {ι : R ⟶ T}
    [IsMonHom a] [IsMonHom b] [IsMonHom ι] (h : a ≫ b = ι) (M : Mod C R) :
    extendUnitHom a M ≫ extendUnitHom b (extendScalarsObj a M) ≫
        ((extendScalarsCompIsoOfEq h).hom.app M).hom = extendUnitHom ι M := by
  have h₁ := extendUnitHom_extendScalarsComp_hom_app a b M
  have h₂ := congrArg Hom.hom ((extendScalarsComp a b).hom_inv_id_app M)
  simp only [comp_hom'] at h₂
  rw [extendScalarsCompIsoOfEq, Iso.trans_hom, NatTrans.comp_app, comp_hom', Iso.symm_hom,
    ← Category.assoc, ← h₁, Category.assoc, reassoc_of% h₂]
  erw [Category.id_comp]
  exact extendUnitHom_extendScalarsIsoOfEq_hom_app h M

/-- The inverse of `extendScalarsCompIsoOfEq` is compatible with the units. -/
@[reassoc]
lemma extendUnitHom_extendScalarsCompIsoOfEq_inv_app {a : R ⟶ S} {b : S ⟶ T} {ι : R ⟶ T}
    [IsMonHom a] [IsMonHom b] [IsMonHom ι] (h : a ≫ b = ι) (M : Mod C R) :
    extendUnitHom ι M ≫ ((extendScalarsCompIsoOfEq h).inv.app M).hom =
      extendUnitHom a M ≫ extendUnitHom b (extendScalarsObj a M) := by
  rw [← extendUnitHom_extendScalarsCompIsoOfEq_hom_app h M, Category.assoc, Category.assoc,
    ← comp_hom', Iso.hom_inv_id_app]
  erw [Category.comp_id]

end Units

section Transfer

variable {R R' S T : C} [MonObj R] [MonObj R'] [MonObj S] [MonObj T] [IsCommMonObj R]
  [IsCommMonObj R'] [IsCommMonObj S] {a : R ⟶ S} {b : S ⟶ T} {ι : R ⟶ T} {a' : R' ⟶ S}
  {ι' : R' ⟶ T} [IsMonHom a] [IsMonHom b] [IsMonHom ι] [IsMonHom a'] [IsMonHom ι']

/-- The underlying map of the adjoint transfer `Res_a(S ⊗_{R'} M) ⟶ Res_ι(T ⊗_{R'} M)` of the
isomorphisms `extendScalarsCompIsoOfEq` is the map `x ⊗ m ↦ b(x) ⊗ m`. -/
lemma compIsoTransfer_extendRestrictAdjunction_hom (h : a ≫ b = ι) (h' : a' ≫ b = ι')
    (M : Mod C R') :
    (Adjunction.compIsoTransfer (extendRestrictAdjunction a) (extendRestrictAdjunction ι)
      (extendScalarsCompIsoOfEq h) (extendScalarsCompIsoOfEq h') M).hom =
        extendChangeHom b h' M := by
  have key : extendUnit b (extendScalarsObj a' M) ≫
      (comap b).map ((extendScalarsCompIsoOfEq h').hom.app M) = extendChange b h' M :=
    extendScalarsObj_hom_ext' (by
      rw [comp_hom', extendUnit_hom, comap_map_hom, extendUnitHom_extendScalarsCompIsoOfEq_hom_app,
        extendChange_hom, extendUnitHom_extendChangeHom])
  have hε := congrArg Hom.hom ((extendRestrictAdjunction a).right_triangle_components
    (extendScalarsObj a' M))
  simp only [comp_hom', comap_map_hom, extendRestrictAdjunction_unit_app_hom] at hε
  rw [Adjunction.compIsoTransfer, Adjunction.homEquiv_unit, comp_hom', comap_map_hom,
    extendRestrictAdjunction_unit_app_hom, comp_hom', comp_hom',
    extendUnitHom_extendScalarsCompIsoOfEq_inv_app_assoc, extendScalars_map]
  erw [extendUnitHom_extendScalarsMap_assoc, reassoc_of% hε, Category.id_comp]
  exact congrArg Hom.hom key

end Transfer

end CategoryTheory.Mod
