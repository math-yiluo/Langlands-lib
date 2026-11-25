/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjoints of morphisms between images of a cocone of functors

Consider functors `T : C ⥤ D`, `T' : C' ⥤ D`, `Φ : D ⥤ E`, `Ψ : C ⥤ E`, `Ψ' : C' ⥤ E`, with
isomorphisms `τ : T ⋙ Φ ≅ Ψ`, `τ' : T' ⋙ Φ ≅ Ψ'`, and adjunctions `T ⊣ R'`, `Ψ ⊣ R`. For a
morphism `g : T K ⟶ T' L`, the `Ψ ⊣ R`-adjoint of `τ⁻¹ ≫ Φ g ≫ τ' : Ψ K ⟶ Ψ' L` is the
`T ⊣ R'`-adjoint of `g` followed by a fixed map `R' (T' L) ⟶ R (Ψ' L)`
(`CategoryTheory.Adjunction.compIsoTransfer`,
`CategoryTheory.Adjunction.homEquiv_inv_app_comp_map_comp_hom_app`). Consequently, a morphism
`f : Ψ K ⟶ Ψ' L` is of the form `τ⁻¹ ≫ Φ g ≫ τ'` as soon as its adjoint factors through this
fixed map (`CategoryTheory.Adjunction.eq_inv_app_comp_map_comp_hom_app`).

When all the functors are induced, through comparison morphisms, by functors between other
categories (e.g. derived functors induced by functors on homotopy categories), the fixed map is
computed by the corresponding fixed map of the underlying functors
(`CategoryTheory.Adjunction.compIsoTransfer_comparison`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C C' D E : Type*} [Category C] [Category C'] [Category D] [Category E]
  {T : C ⥤ D} {T' : C' ⥤ D} {Φ : D ⥤ E} {Ψ : C ⥤ E} {Ψ' : C' ⥤ E} {R' : D ⥤ C} {R : E ⥤ C}

/-- The map `R' (T' L) ⟶ R (Ψ' L)` adjoint to `Ψ R' T' L ≅ Φ T R' T' L ⟶ Φ T' L ≅ Ψ' L`, for
adjunctions `T ⊣ R'`, `Ψ ⊣ R` and isomorphisms `τ : T ⋙ Φ ≅ Ψ`, `τ' : T' ⋙ Φ ≅ Ψ'`. -/
def compIsoTransfer (adj' : T ⊣ R') (adj : Ψ ⊣ R) (τ : T ⋙ Φ ≅ Ψ) (τ' : T' ⋙ Φ ≅ Ψ') (L : C') :
    R'.obj (T'.obj L) ⟶ R.obj (Ψ'.obj L) :=
  adj.homEquiv _ _ (τ.inv.app _ ≫ Φ.map (adj'.counit.app _) ≫ τ'.hom.app L)

/-- `compIsoTransfer` is natural: it is the component of a natural transformation
`T' ⋙ R' ⟶ Ψ' ⋙ R`. -/
@[simps]
def compIsoTransferNatTrans (adj' : T ⊣ R') (adj : Ψ ⊣ R) (τ : T ⋙ Φ ≅ Ψ) (τ' : T' ⋙ Φ ≅ Ψ') :
    T' ⋙ R' ⟶ Ψ' ⋙ R where
  app := compIsoTransfer adj' adj τ τ'
  naturality L L' f := by
    simp only [Functor.comp_map, compIsoTransfer]
    erw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
    congr 1
    erw [τ.inv.naturality_assoc]
    rw [Functor.comp_map, ← Φ.map_comp_assoc]
    erw [adj'.counit.naturality]
    rw [Φ.map_comp_assoc]
    erw [τ'.hom.naturality]
    simp

/-- The `Ψ ⊣ R`-adjoint of `τ⁻¹ ≫ Φ g ≫ τ'` is the `T ⊣ R'`-adjoint of `g` followed by
`compIsoTransfer`. -/
lemma homEquiv_inv_app_comp_map_comp_hom_app (adj' : T ⊣ R') (adj : Ψ ⊣ R) (τ : T ⋙ Φ ≅ Ψ)
    (τ' : T' ⋙ Φ ≅ Ψ') {K : C} {L : C'} (g : T.obj K ⟶ T'.obj L) :
    adj.homEquiv _ _ (τ.inv.app K ≫ Φ.map g ≫ τ'.hom.app L) =
      adj'.homEquiv _ _ g ≫ compIsoTransfer adj' adj τ τ' L := by
  rw [compIsoTransfer, ← adj.homEquiv_naturality_left, τ.inv.naturality_assoc,
    Functor.comp_map, ← Φ.map_comp_assoc]
  simp [homEquiv_unit]

/-- A morphism `f : Ψ K ⟶ Ψ' L` whose `Ψ ⊣ R`-adjoint factors through `compIsoTransfer` as
`h ≫ compIsoTransfer` is `τ⁻¹ ≫ Φ g ≫ τ'` for the `T ⊣ R'`-adjoint `g` of `h`. -/
lemma eq_inv_app_comp_map_comp_hom_app (adj' : T ⊣ R') (adj : Ψ ⊣ R) (τ : T ⋙ Φ ≅ Ψ)
    (τ' : T' ⋙ Φ ≅ Ψ') {K : C} {L : C'} (f : Ψ.obj K ⟶ Ψ'.obj L) (h : K ⟶ R'.obj (T'.obj L))
    (hf : adj.homEquiv _ _ f = h ≫ compIsoTransfer adj' adj τ τ' L) :
    f = τ.inv.app K ≫ Φ.map ((adj'.homEquiv _ _).symm h) ≫ τ'.hom.app L := by
  apply (adj.homEquiv _ _).injective
  rw [hf, homEquiv_inv_app_comp_map_comp_hom_app, Equiv.apply_symm_apply]

/-- **Computation of `compIsoTransfer` through comparison morphisms.** Suppose all the data are
induced by data `t, t', φ, ψ, ψ', r', r, t ⊣ r', ψ ⊣ r, e, e'` between categories `H, H', HD, HE`
through functors `QC, QC', QD, QE` and comparison morphisms `cT, cT', cΦ, cΨ, cΨ', fR', fR`,
compatibly with the units, counits and the isomorphisms `τ, τ'`. Then `compIsoTransfer` at
`QC' Y` is, modulo the comparison isomorphisms, the image under `QC` of the `compIsoTransfer` of
the underlying data: the square
```
  R' (T' (QC' Y)) ──compIsoTransfer adj' adj τ τ'──▶ R (Ψ' (QC' Y))
        │ R' cT' ≫ fR'                                  │ R cΨ' ≫ fR
        ▼                                                ▼
  QC (r' (t' Y)) ──QC (compIsoTransfer ad' ad e e')──▶ QC (r (ψ' Y))
```
commutes. -/
lemma compIsoTransfer_comparison {H H' HD HE : Type*} [Category H] [Category H'] [Category HD]
    [Category HE] {t : H ⥤ HD} {t' : H' ⥤ HD} {φ : HD ⥤ HE} {ψ : H ⥤ HE} {ψ' : H' ⥤ HE}
    {r' : HD ⥤ H} {r : HE ⥤ H} (ad' : t ⊣ r') (ad : ψ ⊣ r) (e : t ⋙ φ ≅ ψ) (e' : t' ⋙ φ ≅ ψ')
    (adj' : T ⊣ R') (adj : Ψ ⊣ R) (τ : T ⋙ Φ ≅ Ψ) (τ' : T' ⋙ Φ ≅ Ψ')
    {QC : H ⥤ C} {QC' : H' ⥤ C'} {QD : HD ⥤ D} {QE : HE ⥤ E}
    (cT : QC ⋙ T ⟶ t ⋙ QD) (cT' : QC' ⋙ T' ≅ t' ⋙ QD) (cΦ : QD ⋙ Φ ⟶ φ ⋙ QE)
    (cΨ : QC ⋙ Ψ ⟶ ψ ⋙ QE) (cΨ' : QC' ⋙ Ψ' ⟶ ψ' ⋙ QE)
    (fR' : QD ⋙ R' ≅ r' ⋙ QC) (fR : QE ⋙ R ≅ r ⋙ QC)
    (hunit : ∀ M : H, adj.unit.app (QC.obj M) ≫ R.map (cΨ.app M) =
      QC.map (ad.unit.app M) ≫ fR.inv.app (ψ.obj M))
    (hcounit : ∀ N : HD, T.map (fR'.inv.app N) ≫ adj'.counit.app (QD.obj N) =
      cT.app (r'.obj N) ≫ QD.map (ad'.counit.app N))
    (hτ : ∀ M : H, τ.hom.app (QC.obj M) ≫ cΨ.app M =
      Φ.map (cT.app M) ≫ cΦ.app (t.obj M) ≫ QE.map (e.hom.app M))
    (hτ' : ∀ Y : H', τ'.hom.app (QC'.obj Y) ≫ cΨ'.app Y =
      Φ.map (cT'.hom.app Y) ≫ cΦ.app (t'.obj Y) ≫ QE.map (e'.hom.app Y))
    (Y : H') :
    R'.map (cT'.hom.app Y) ≫ fR'.hom.app (t'.obj Y) ≫
        QC.map (compIsoTransfer ad' ad e e' Y) =
      compIsoTransfer adj' adj τ τ' (QC'.obj Y) ≫ R.map (cΨ'.app Y) ≫
        fR.hom.app (ψ'.obj Y) := by
  have key : T.map (R'.map (cT'.hom.app Y) ≫ fR'.hom.app (t'.obj Y)) ≫
      cT.app (r'.obj (t'.obj Y)) ≫ QD.map (ad'.counit.app (t'.obj Y)) =
        adj'.counit.app (T'.obj (QC'.obj Y)) ≫ cT'.hom.app Y := by
    rw [← hcounit, T.map_comp_assoc, ← T.map_comp_assoc (fR'.hom.app _), Iso.hom_inv_id_app,
      T.map_id, Category.id_comp]
    exact adj'.counit.naturality (cT'.hom.app Y)
  have key' : Ψ.map (R'.map (cT'.hom.app Y) ≫ fR'.hom.app (t'.obj Y)) ≫
      cΨ.app (r'.obj (t'.obj Y)) ≫ QE.map (e.inv.app _ ≫ φ.map (ad'.counit.app (t'.obj Y)) ≫
        e'.hom.app Y) =
      τ.inv.app _ ≫ Φ.map (adj'.counit.app (T'.obj (QC'.obj Y))) ≫ τ'.hom.app (QC'.obj Y) ≫
        cΨ'.app Y := by
    rw [← cancel_epi (τ.hom.app _)]
    simp only [Functor.comp_obj, Iso.hom_inv_id_app_assoc]
    rw [← τ.hom.naturality_assoc]
    erw [reassoc_of% (hτ (r'.obj (t'.obj Y))), hτ' Y]
    rw [← Φ.map_comp_assoc (adj'.counit.app _), ← key]
    simp only [Functor.map_comp, Category.assoc]
    rw [← QE.map_comp_assoc (e.hom.app _)]
    simp only [Iso.hom_inv_id_app, QE.map_id, Category.id_comp]
    congr 3
    exact (cΦ.naturality_assoc _ _).symm
  have hu : QC.map (ad.unit.app (r'.obj (t'.obj Y))) =
      adj.unit.app (QC.obj (r'.obj (t'.obj Y))) ≫ R.map (cΨ.app (r'.obj (t'.obj Y))) ≫
        fR.hom.app (ψ.obj (r'.obj (t'.obj Y))) := by
    erw [reassoc_of% (hunit (r'.obj (t'.obj Y)))]
    simp
  have hnat := fR.hom.naturality
    (e.inv.app _ ≫ φ.map (ad'.counit.app (t'.obj Y)) ≫ e'.hom.app Y)
  have hw : R'.map (cT'.hom.app Y) ≫ fR'.hom.app (t'.obj Y) ≫
      adj.unit.app (QC.obj (r'.obj (t'.obj Y))) =
        adj.unit.app _ ≫ R.map (Ψ.map (R'.map (cT'.hom.app Y) ≫ fR'.hom.app (t'.obj Y))) := by
    rw [← Category.assoc]
    exact adj.unit.naturality _
  simp only [Functor.comp_map] at hnat
  rw [compIsoTransfer, compIsoTransfer, homEquiv_unit, homEquiv_unit, QC.map_comp, hu]
  simp only [Category.assoc]
  rw [← hnat, reassoc_of% hw]
  have h := congrArg R.map key'
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  rw [reassoc_of% h]

end CategoryTheory.Adjunction
