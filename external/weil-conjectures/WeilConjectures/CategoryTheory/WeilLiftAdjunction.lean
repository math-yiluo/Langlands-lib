/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.WeilEquivariance
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Weil structures of right adjoints: the exceptional datum

Let `U_C : W_C ⥤ D_C` be the functor forgetting a Weil structure (in the `ℓ`-adic formalism
`W_C = D(X, Weil)` and `D_C = D(X̄)`), with structure maps `σ_C : F (U_C M) ⟶ U_C M` natural in
`M` (`F = Fr^*`), and similarly `U_D`, `σ_D`, `G` on another base. A functor `T : W_C ⥤ W_D` *lies
over* `T₀ : D_C ⥤ D_D` through an isomorphism `κ : U_D ∘ T ≅ T₀ ∘ U_C` and an exchange
`e : G ∘ T₀ ≅ T₀ ∘ F` if the structure of `T M` is the transport of that of `M`
(`CategoryTheory.IsWeilLift`).

If `T ⊣ RW` and `T₀ ⊣ R₀`, and `θ : U_C (RW L') ≅ R₀ (U_D L')` is compatible with the counits
(`CategoryTheory.CounitCompat`), then the Weil structure of `RW L'`, read through `θ`, is the
*exceptional datum* `rightWeilDatum adj₀ e (σ_D L')`: the unique Weil datum on `R₀ (U_D L')`
for which the counit `T₀ R₀ (U_D L') ⟶ U_D L'` is equivariant
(`CategoryTheory.isWeilEquivariant_rightWeilDatum_of_counitCompat`). This is the formal content
of "the Frobenius structure of the Weil `Rf^!` is the exceptional datum of the Frobenius square"
(blueprint `proposition-purity-trace-commute-frobenius`).

Lifts and counit-compatible comparisons compose (`CategoryTheory.isWeilLift_comp`,
`CategoryTheory.counitCompat_comp`) and transport along isomorphisms of the left adjoint
(`CategoryTheory.isWeilLift_of_iso`, `CategoryTheory.counitCompat_of_iso`): this is how the
statement for `Rf^! = i^* ∘ Rg^!` along a compactification `f = g ∘ i` is assembled from the
two factors.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category CategoryTheory.Functor
open Adjunction (leftWeilDatum rightWeilDatum)

section Unique

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {G : C ⥤ C} {H : D ⥤ D} (e : L ⋙ H ≅ G ⋙ L)

/-- **Uniqueness of the exceptional datum**: a Weil datum `v` on `R d` for which the counit
`L R d ⟶ d` is equivariant (for the datum `ψ` on `d`) is the right Weil datum
`CategoryTheory.Adjunction.rightWeilDatum`. -/
lemma Adjunction.eq_rightWeilDatum_of_isWeilEquivariant_counit {d : D} (ψ : H.obj d ⟶ d)
    {v : G.obj (R.obj d) ⟶ R.obj d}
    (hv : IsWeilEquivariant H (leftWeilDatum e v) ψ (adj.counit.app d)) :
    v = rightWeilDatum adj e ψ := by
  have h := adj.isWeilEquivariant_counit e ψ
  unfold IsWeilEquivariant leftWeilDatum at hv h
  have h' : e.hom.app (R.obj d) ≫ L.map v ≫ adj.counit.app d =
      e.hom.app (R.obj d) ≫ L.map (rightWeilDatum adj e ψ) ≫ adj.counit.app d := by
    rw [← Category.assoc, ← hv, h, Category.assoc]
  apply (adj.homEquiv _ _).symm.injective
  change L.map v ≫ adj.counit.app d = L.map (rightWeilDatum adj e ψ) ≫ adj.counit.app d
  exact (cancel_epi _).1 h'

end Unique

section Lift

variable {WC DC WD DD : Type*} [Category* WC] [Category* DC] [Category* WD] [Category* DD]
  {UC : WC ⥤ DC} {F : DC ⥤ DC} (σC : UC ⋙ F ⟶ UC)
  {UD : WD ⥤ DD} {G : DD ⥤ DD} (σD : UD ⋙ G ⟶ UD)
  {T : WC ⥤ WD} {T₀ : DC ⥤ DD} (e : T₀ ⋙ G ≅ F ⋙ T₀) (κ : T ⋙ UD ≅ UC ⋙ T₀)

/-- `T : W_C ⥤ W_D` lies over `T₀ : D_C ⥤ D_D` through `κ : U_D ∘ T ≅ T₀ ∘ U_C` and the exchange
`e : G ∘ T₀ ≅ T₀ ∘ F`: the structure map of `T M` corresponds to `T₀` of that of `M`. -/
def IsWeilLift : Prop :=
  ∀ M : WC, σD.app (T.obj M) ≫ κ.hom.app M =
    G.map (κ.hom.app M) ≫ e.hom.app (UC.obj M) ≫ T₀.map (σC.app M)

variable {RW : WD ⥤ WC} (adjW : T ⊣ RW) {R₀ : DD ⥤ DC} (adj₀ : T₀ ⊣ R₀)

/-- A comparison `θ : U_C (RW L') ≅ R₀ (U_D L')` is *counit compatible* if
`κ ≫ T₀ θ ≫ ε₀ = U_D ε_W` on `L'`. -/
def CounitCompat (L' : WD) (θ : UC.obj (RW.obj L') ≅ R₀.obj (UD.obj L')) : Prop :=
  κ.hom.app (RW.obj L') ≫ T₀.map θ.hom ≫ adj₀.counit.app (UD.obj L') =
    UD.map (adjW.counit.app L')

/-- The Weil structure of `RW L'` transported along `θ`. -/
def transportedDatum (L' : WD) (θ : UC.obj (RW.obj L') ≅ R₀.obj (UD.obj L')) :
    F.obj (R₀.obj (UD.obj L')) ⟶ R₀.obj (UD.obj L') :=
  F.map θ.inv ≫ σC.app (RW.obj L') ≫ θ.hom

variable {σC σD e κ adjW adj₀}

/-- **The transported structure is counit equivariant**: for a counit-compatible comparison `θ`,
the counit `T₀ R₀ (U_D L') ⟶ U_D L'` is equivariant for the structure of `RW L'` transported
along `θ` and the structure of `L'`. -/
lemma isWeilEquivariant_counit_transportedDatum (hlift : IsWeilLift σC σD e κ) (L' : WD)
    (θ : UC.obj (RW.obj L') ≅ R₀.obj (UD.obj L')) (hθ : CounitCompat κ adjW adj₀ L' θ) :
    IsWeilEquivariant G (leftWeilDatum e (transportedDatum σC L' θ)) (σD.app L')
      (adj₀.counit.app (UD.obj L')) := by
  have hθ' : κ.hom.app (RW.obj L') ≫ T₀.map θ.hom ≫ adj₀.counit.app (UD.obj L') =
      UD.map (adjW.counit.app L') := hθ
  have hε : adj₀.counit.app (UD.obj L') = T₀.map θ.inv ≫ κ.inv.app (RW.obj L') ≫
      UD.map (adjW.counit.app L') := by
    rw [← hθ', Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_map_assoc]
  have hnat : G.map (UD.map (adjW.counit.app L')) ≫ σD.app L' =
      σD.app (T.obj (RW.obj L')) ≫ UD.map (adjW.counit.app L') :=
    σD.naturality (adjW.counit.app L')
  have hcomm : G.map (T₀.map θ.inv) ≫ e.hom.app (UC.obj (RW.obj L')) =
      e.hom.app (R₀.obj (UD.obj L')) ≫ T₀.map (F.map θ.inv) :=
    e.hom.naturality θ.inv
  have hstr' : e.hom.app (UC.obj (RW.obj L')) ≫ T₀.map (σC.app (RW.obj L')) =
      G.map (κ.inv.app (RW.obj L')) ≫ σD.app (T.obj (RW.obj L')) ≫ κ.hom.app (RW.obj L') := by
    rw [hlift (RW.obj L'), ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  unfold IsWeilEquivariant leftWeilDatum transportedDatum
  rw [hε]
  simp only [Functor.map_comp, Category.assoc]
  rw [hnat, ← reassoc_of% hcomm, reassoc_of% hstr', Iso.hom_inv_id_map_assoc,
    Iso.hom_inv_id_app_assoc]

/-- **The Weil structure of a right adjoint is the exceptional datum**: for a counit-compatible
comparison `θ : U_C (RW L') ≅ R₀ (U_D L')`, the structure map of `RW L'` corresponds under `θ` to
the right Weil datum of the structure of `L'`, i.e. `θ` is equivariant. -/
lemma isWeilEquivariant_rightWeilDatum_of_counitCompat (hlift : IsWeilLift σC σD e κ) (L' : WD)
    (θ : UC.obj (RW.obj L') ≅ R₀.obj (UD.obj L')) (hθ : CounitCompat κ adjW adj₀ L' θ) :
    IsWeilEquivariant F (σC.app (RW.obj L')) (rightWeilDatum adj₀ e (σD.app L')) θ.hom := by
  rw [← adj₀.eq_rightWeilDatum_of_isWeilEquivariant_counit e _
    (isWeilEquivariant_counit_transportedDatum hlift L' θ hθ)]
  unfold IsWeilEquivariant transportedDatum
  rw [Iso.hom_inv_id_map_assoc]

/-- The form of `isWeilEquivariant_rightWeilDatum_of_counitCompat` for an arbitrary Weil datum
`v` on `R₀ (U_D L')` for which the counit is equivariant. -/
lemma isWeilEquivariant_of_counitCompat (hlift : IsWeilLift σC σD e κ) (L' : WD)
    (θ : UC.obj (RW.obj L') ≅ R₀.obj (UD.obj L')) (hθ : CounitCompat κ adjW adj₀ L' θ)
    {v : F.obj (R₀.obj (UD.obj L')) ⟶ R₀.obj (UD.obj L')}
    (hv : IsWeilEquivariant G (leftWeilDatum e v) (σD.app L') (adj₀.counit.app (UD.obj L'))) :
    IsWeilEquivariant F (σC.app (RW.obj L')) v θ.hom := by
  rw [adj₀.eq_rightWeilDatum_of_isWeilEquivariant_counit e _ hv]
  exact isWeilEquivariant_rightWeilDatum_of_counitCompat hlift L' θ hθ

end Lift

section Iso

variable {WC DC WD DD : Type*} [Category* WC] [Category* DC] [Category* WD] [Category* DD]
  {UC : WC ⥤ DC} {F : DC ⥤ DC} {σC : UC ⋙ F ⟶ UC}
  {UD : WD ⥤ DD} {G : DD ⥤ DD} {σD : UD ⋙ G ⟶ UD}
  {T T' : WC ⥤ WD} {T₀ : DC ⥤ DD} {e : T₀ ⋙ G ≅ F ⋙ T₀} {κ : T ⋙ UD ≅ UC ⋙ T₀}

/-- A lift transports along an isomorphism `α : T' ≅ T` of the Weil-level functor, with the
comparison `U_D α ≫ κ`. -/
lemma isWeilLift_of_iso (h : IsWeilLift σC σD e κ) (α : T' ≅ T) {κ' : T' ⋙ UD ≅ UC ⋙ T₀}
    (hκ' : ∀ M, κ'.hom.app M = UD.map (α.hom.app M) ≫ κ.hom.app M) :
    IsWeilLift σC σD e κ' := by
  intro M
  have hn : σD.app (T'.obj M) ≫ UD.map (α.hom.app M) =
      G.map (UD.map (α.hom.app M)) ≫ σD.app (T.obj M) := (σD.naturality (α.hom.app M)).symm
  rw [hκ', reassoc_of% hn, h M, Functor.map_comp, Category.assoc]

variable {RW RW' : WD ⥤ WC} {R₀ : DD ⥤ DC}

/-- Counit compatibility transports along an isomorphism `α : T' ≅ T` of the Weil-level left
adjoint, for any right adjoint `RW'` of `T'`: the comparison for `RW'` is the comparison for `RW`
precomposed with `U_C` of the canonical isomorphism `RW' ≅ RW`. -/
lemma counitCompat_of_iso {adjW : T ⊣ RW} {adj₀ : T₀ ⊣ R₀} (α : T' ≅ T)
    {κ' : T' ⋙ UD ≅ UC ⋙ T₀} (hκ' : ∀ M, κ'.hom.app M = UD.map (α.hom.app M) ≫ κ.hom.app M)
    (adjW' : T' ⊣ RW') (L' : WD) (θ : UC.obj (RW.obj L') ≅ R₀.obj (UD.obj L'))
    (hθ : CounitCompat κ adjW adj₀ L' θ) :
    CounitCompat κ' adjW' adj₀ L'
      (UC.mapIso ((adjW'.rightAdjointUniq (adjW.ofNatIsoLeft α.symm)).app L') ≪≫ θ) := by
  have hθ' : κ.hom.app (RW.obj L') ≫ T₀.map θ.hom ≫ adj₀.counit.app (UD.obj L') =
      UD.map (adjW.counit.app L') := hθ
  have hε' : adjW'.counit.app L' =
      T'.map ((adjW'.rightAdjointUniq (adjW.ofNatIsoLeft α.symm)).hom.app L') ≫
        α.hom.app (RW.obj L') ≫ adjW.counit.app L' := by
    rw [← Adjunction.rightAdjointUniq_hom_app_counit adjW' (adjW.ofNatIsoLeft α.symm) L']
    simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Iso.symm_inv]
  set ρ := adjW'.rightAdjointUniq (adjW.ofNatIsoLeft α.symm) with hρ
  have hκn : κ.hom.app (RW'.obj L') ≫ T₀.map (UC.map (ρ.hom.app L')) =
      UD.map (T.map (ρ.hom.app L')) ≫ κ.hom.app (RW.obj L') :=
    (κ.hom.naturality (ρ.hom.app L')).symm
  have hα : α.hom.app (RW'.obj L') ≫ T.map (ρ.hom.app L') =
      T'.map (ρ.hom.app L') ≫ α.hom.app (RW.obj L') := (α.hom.naturality (ρ.hom.app L')).symm
  unfold CounitCompat
  rw [hκ', hε']
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hκn, hθ', ← Functor.map_comp_assoc, hα, Functor.map_comp, Category.assoc]

end Iso

section Comp

variable {WC DC WD DD WE DE : Type*} [Category* WC] [Category* DC] [Category* WD] [Category* DD]
  [Category* WE] [Category* DE]
  {UC : WC ⥤ DC} {F : DC ⥤ DC} {σC : UC ⋙ F ⟶ UC}
  {UD : WD ⥤ DD} {G : DD ⥤ DD} {σD : UD ⋙ G ⟶ UD}
  {UE : WE ⥤ DE} {K : DE ⥤ DE} {σE : UE ⋙ K ⟶ UE}
  {T : WC ⥤ WD} {T₀ : DC ⥤ DD} {e : T₀ ⋙ G ≅ F ⋙ T₀} {κ : T ⋙ UD ≅ UC ⋙ T₀}
  {T' : WD ⥤ WE} {T₀' : DD ⥤ DE} {e' : T₀' ⋙ K ≅ G ⋙ T₀'} {κ' : T' ⋙ UE ≅ UD ⋙ T₀'}

/-- Lifts compose: if `T` lies over `T₀` and `T'` over `T₀'`, then `T ⋙ T'` lies over
`T₀ ⋙ T₀'`, for the composite exchange and comparison (given by their components). -/
lemma isWeilLift_comp (h : IsWeilLift σC σD e κ) (h' : IsWeilLift σD σE e' κ')
    {ecomp : (T₀ ⋙ T₀') ⋙ K ≅ F ⋙ (T₀ ⋙ T₀')}
    (he : ∀ c, ecomp.hom.app c = e'.hom.app (T₀.obj c) ≫ T₀'.map (e.hom.app c))
    {κcomp : (T ⋙ T') ⋙ UE ≅ UC ⋙ (T₀ ⋙ T₀')}
    (hκ : ∀ M, κcomp.hom.app M = κ'.hom.app (T.obj M) ≫ T₀'.map (κ.hom.app M)) :
    IsWeilLift σC σE ecomp κcomp := by
  intro M
  have h1 : σE.app (T'.obj (T.obj M)) ≫ κ'.hom.app (T.obj M) =
      K.map (κ'.hom.app (T.obj M)) ≫ e'.hom.app (UD.obj (T.obj M)) ≫
        T₀'.map (σD.app (T.obj M)) := h' (T.obj M)
  have h2 : T₀'.map (σD.app (T.obj M)) ≫ T₀'.map (κ.hom.app M) =
      T₀'.map (G.map (κ.hom.app M)) ≫ T₀'.map (e.hom.app (UC.obj M)) ≫
        T₀'.map (T₀.map (σC.app M)) := by
    simp only [← Functor.map_comp, h M]
  have hn : e'.hom.app (UD.obj (T.obj M)) ≫ T₀'.map (G.map (κ.hom.app M)) =
      K.map (T₀'.map (κ.hom.app M)) ≫ e'.hom.app (T₀.obj (UC.obj M)) :=
    (e'.hom.naturality (κ.hom.app M)).symm
  rw [hκ, he]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, h2, reassoc_of% hn]

variable {RW : WD ⥤ WC} {R₀ : DD ⥤ DC} {RW' : WE ⥤ WD} {R₀' : DE ⥤ DD}

/-- Counit-compatible comparisons compose: for `θ₁` at `RW' L'` and `θ₂` at `L'`, the comparison
`θ₁ ≫ R₀ θ₂ : U_C (RW (RW' L')) ≅ R₀ (R₀' (U_E L'))` is counit compatible for the composite
adjunctions and the composite comparison. -/
lemma counitCompat_comp {adjW : T ⊣ RW} {adj₀ : T₀ ⊣ R₀} {adjW' : T' ⊣ RW'}
    {adj₀' : T₀' ⊣ R₀'}
    {κcomp : (T ⋙ T') ⋙ UE ≅ UC ⋙ (T₀ ⋙ T₀')}
    (hκ : ∀ M, κcomp.hom.app M = κ'.hom.app (T.obj M) ≫ T₀'.map (κ.hom.app M))
    (L' : WE) (θ₁ : UC.obj (RW.obj (RW'.obj L')) ≅ R₀.obj (UD.obj (RW'.obj L')))
    (hθ₁ : CounitCompat κ adjW adj₀ (RW'.obj L') θ₁)
    (θ₂ : UD.obj (RW'.obj L') ≅ R₀'.obj (UE.obj L')) (hθ₂ : CounitCompat κ' adjW' adj₀' L' θ₂) :
    CounitCompat κcomp (adjW.comp adjW') (adj₀.comp adj₀') L' (θ₁ ≪≫ R₀.mapIso θ₂) := by
  have hθ₁' : κ.hom.app (RW.obj (RW'.obj L')) ≫ T₀.map θ₁.hom ≫
      adj₀.counit.app (UD.obj (RW'.obj L')) = UD.map (adjW.counit.app (RW'.obj L')) := hθ₁
  have hθ₂' : κ'.hom.app (RW'.obj L') ≫ T₀'.map θ₂.hom ≫ adj₀'.counit.app (UE.obj L') =
      UE.map (adjW'.counit.app L') := hθ₂
  have hnat₀ : T₀.map (R₀.map θ₂.hom) ≫ adj₀.counit.app (R₀'.obj (UE.obj L')) =
      adj₀.counit.app (UD.obj (RW'.obj L')) ≫ θ₂.hom := adj₀.counit.naturality θ₂.hom
  have hn₀ : T₀'.map (T₀.map (R₀.map θ₂.hom)) ≫
      T₀'.map (adj₀.counit.app (R₀'.obj (UE.obj L'))) =
      T₀'.map (adj₀.counit.app (UD.obj (RW'.obj L'))) ≫ T₀'.map θ₂.hom := by
    simp only [← Functor.map_comp, hnat₀]
  have h1 : T₀'.map (κ.hom.app (RW.obj (RW'.obj L'))) ≫ T₀'.map (T₀.map θ₁.hom) ≫
      T₀'.map (adj₀.counit.app (UD.obj (RW'.obj L'))) =
      T₀'.map (UD.map (adjW.counit.app (RW'.obj L'))) := by
    simp only [← Functor.map_comp, hθ₁']
  have hnκ : κ'.hom.app (T.obj (RW.obj (RW'.obj L'))) ≫
      T₀'.map (UD.map (adjW.counit.app (RW'.obj L'))) =
      UE.map (T'.map (adjW.counit.app (RW'.obj L'))) ≫ κ'.hom.app (RW'.obj L') :=
    (κ'.hom.naturality (adjW.counit.app (RW'.obj L'))).symm
  unfold CounitCompat
  rw [hκ, Adjunction.comp_counit_app, Adjunction.comp_counit_app]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn₀, reassoc_of% h1, reassoc_of% hnκ, hθ₂']

end Comp

section CompDatum

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
  {G : C ⥤ C} {H : D ⥤ D} {K : E ⥤ E} (e₁ : L₁ ⋙ H ≅ G ⋙ L₁) (e₂ : L₂ ⋙ K ≅ H ⋙ L₂)

/-- **The right Weil datum of a composite adjunction** is the transport along `R₁` (through the
right adjoint exchange of `e₁`) of the right Weil datum of `adj₂`: by uniqueness of the
counit-equivariant datum. -/
lemma Adjunction.rightWeilDatum_comp {ecomp : (L₁ ⋙ L₂) ⋙ K ≅ G ⋙ (L₁ ⋙ L₂)}
    (he : ∀ c, ecomp.hom.app c = e₂.hom.app (L₁.obj c) ≫ L₂.map (e₁.hom.app c)) {d : E}
    (ψ : K.obj d ⟶ d) :
    rightWeilDatum (adj₁.comp adj₂) ecomp ψ =
      (Adjunction.rightAdjointExchange adj₁ adj₁ e₁).app (R₂.obj d) ≫
        R₁.map (rightWeilDatum adj₂ e₂ ψ) := by
  symm
  apply (adj₁.comp adj₂).eq_rightWeilDatum_of_isWeilEquivariant_counit ecomp ψ
  have hA := Adjunction.hom_app_comp_map_rightAdjointExchange_app_comp_counit adj₁ adj₁ e₁
    (R₂.obj d)
  have hB : L₁.map (R₁.map (rightWeilDatum adj₂ e₂ ψ)) ≫ adj₁.counit.app (R₂.obj d) =
      adj₁.counit.app (H.obj (R₂.obj d)) ≫ rightWeilDatum adj₂ e₂ ψ :=
    adj₁.counit.naturality _
  have hC : K.map (L₂.map (adj₁.counit.app (R₂.obj d))) ≫ e₂.hom.app (R₂.obj d) =
      e₂.hom.app (L₁.obj (R₁.obj (R₂.obj d))) ≫ L₂.map (H.map (adj₁.counit.app (R₂.obj d))) :=
    e₂.hom.naturality _
  have hD : K.map (adj₂.counit.app d) ≫ ψ =
      e₂.hom.app (R₂.obj d) ≫ L₂.map (rightWeilDatum adj₂ e₂ ψ) ≫ adj₂.counit.app d := by
    have h := adj₂.isWeilEquivariant_counit e₂ ψ
    unfold IsWeilEquivariant leftWeilDatum at h
    rw [h, Category.assoc]
  have h1 : L₂.map (L₁.map (R₁.map (rightWeilDatum adj₂ e₂ ψ))) ≫
      L₂.map (adj₁.counit.app (R₂.obj d)) =
      L₂.map (adj₁.counit.app (H.obj (R₂.obj d))) ≫ L₂.map (rightWeilDatum adj₂ e₂ ψ) := by
    simp only [← Functor.map_comp, hB]
  have h2 : L₂.map (e₁.hom.app (R₁.obj (R₂.obj d))) ≫
      L₂.map (L₁.map ((Adjunction.rightAdjointExchange adj₁ adj₁ e₁).app (R₂.obj d))) ≫
      L₂.map (adj₁.counit.app (H.obj (R₂.obj d))) =
      L₂.map (H.map (adj₁.counit.app (R₂.obj d))) := by
    simp only [← Functor.map_comp, hA]
  unfold IsWeilEquivariant leftWeilDatum
  rw [Adjunction.comp_counit_app, he]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, ← reassoc_of% hC, hD]

end CompDatum

section Unique'

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) {L₂ : E ⥤ D} {R₂ : D ⥤ E} (adj₂ : L₂ ⊣ R₂)

/-- A natural transformation `τ : R₁ ⋙ G ⟶ H ⋙ R₂` is determined by the unit equation
`G η₁ ≫ τ_{L₁ c} = η₂ ≫ R₂ (e⁻¹)`: on `d`, `τ_d = G η₁ ≫ τ_{L₁ R₁ d} ≫ R₂ (H ε₁)`. -/
lemma app_eq_of_unit {G : C ⥤ E} {H : D ⥤ D} (τ : R₁ ⋙ G ⟶ H ⋙ R₂) (d : D) :
    τ.app d = G.map (adj₁.unit.app (R₁.obj d)) ≫ τ.app (L₁.obj (R₁.obj d)) ≫
      R₂.map (H.map (adj₁.counit.app d)) := by
  have hn : G.map (R₁.map (adj₁.counit.app d)) ≫ τ.app d =
      τ.app (L₁.obj (R₁.obj d)) ≫ R₂.map (H.map (adj₁.counit.app d)) := τ.naturality _
  have ht : adj₁.unit.app (R₁.obj d) ≫ R₁.map (adj₁.counit.app d) = 𝟙 _ :=
    adj₁.right_triangle_components d
  rw [← hn, ← Functor.map_comp_assoc, ht, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Uniqueness of the right adjoint exchange**: a natural transformation `R₁ ⋙ G ⟶ H ⋙ R₂`
satisfying the unit equation of
`CategoryTheory.Adjunction.map_unit_app_comp_rightAdjointExchange_app` is the right adjoint
exchange. -/
lemma Adjunction.rightAdjointExchange_eq_of_unit {G : C ⥤ E} {H : D ⥤ D}
    (e : L₁ ⋙ H ≅ G ⋙ L₂) {τ : R₁ ⋙ G ⟶ H ⋙ R₂}
    (hτ : ∀ c, G.map (adj₁.unit.app c) ≫ τ.app (L₁.obj c) =
      adj₂.unit.app (G.obj c) ≫ R₂.map (e.inv.app c)) :
    τ = Adjunction.rightAdjointExchange adj₁ adj₂ e := by
  ext d
  rw [app_eq_of_unit adj₁ τ d,
    app_eq_of_unit adj₁ (Adjunction.rightAdjointExchange adj₁ adj₂ e) d,
    reassoc_of% (hτ (R₁.obj d)),
    reassoc_of% (Adjunction.map_unit_app_comp_rightAdjointExchange_app adj₁ adj₂ e (R₁.obj d))]

end Unique'

section Lift'

variable {C D : Type*} [Category* C] [Category* D] {P : ObjectProperty C} {Q : ObjectProperty D}
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (hL : ∀ X, P X → Q (L.obj X))
  (hR : ∀ Y, Q Y → P (R.obj Y)) {G : C ⥤ C} {H : D ⥤ D} (e : L ⋙ H ≅ G ⋙ L)
  (hG : ∀ X, P X → P (G.obj X)) (hH : ∀ Y, Q Y → Q (H.obj Y))

/-- **The right Weil datum of a restricted adjunction** is the right Weil datum of the adjunction:
by uniqueness, for an exchange `eP` on the full subcategories lifting `e`. -/
lemma Adjunction.rightWeilDatum_liftFullSubcategory_hom
    {eP : P.liftFullSubcategory Q L hL ⋙ Q.liftFullSubcategory Q H hH ≅
      P.liftFullSubcategory P G hG ⋙ P.liftFullSubcategory Q L hL}
    (heP : ∀ X, (eP.hom.app X).hom = e.hom.app X.obj) {d : Q.FullSubcategory}
    (ψ : H.obj d.obj ⟶ d.obj) :
    (rightWeilDatum (ObjectProperty.liftFullSubcategoryAdjunction adj hL hR) eP
      (ObjectProperty.homMk (X := (Q.liftFullSubcategory Q H hH).obj d) (Y := d) ψ)).hom =
      rightWeilDatum adj e ψ := by
  have h := (ObjectProperty.liftFullSubcategoryAdjunction adj hL hR).isWeilEquivariant_counit eP
    (ObjectProperty.homMk (X := (Q.liftFullSubcategory Q H hH).obj d) (Y := d) ψ)
  unfold IsWeilEquivariant leftWeilDatum at h
  have h' : H.map (adj.counit.app d.obj) ≫ ψ =
      (e.hom.app ((Q.liftFullSubcategory P R hR).obj d).obj ≫
        L.map (rightWeilDatum (ObjectProperty.liftFullSubcategoryAdjunction adj hL hR) eP
          (ObjectProperty.homMk (X := (Q.liftFullSubcategory Q H hH).obj d) (Y := d) ψ)).hom) ≫
        adj.counit.app d.obj := by
    rw [← heP]
    exact congrArg InducedCategory.Hom.hom h
  apply adj.eq_rightWeilDatum_of_isWeilEquivariant_counit e ψ
  unfold IsWeilEquivariant leftWeilDatum
  exact h'

end Lift'

section Trace

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {G : C ⥤ C} {H : D ⥤ D} (e : L ⋙ H ≅ G ⋙ L)

/-- The *trace* of an orientation `o : R Y ≅ T`: `L T ──L o⁻¹──▶ L R Y ──ε──▶ Y`. -/
def Adjunction.orientationTrace {Y : D} {T : C} (o : R.obj Y ≅ T) : L.obj T ⟶ Y :=
  L.map o.inv ≫ adj.counit.app Y

/-- The counit is equivariant for the conjugate `G o ≫ τ ≫ o⁻¹` of a datum `τ` on `T` if and
only if the trace of `o` is equivariant for `τ` (the *trace square*). -/
lemma Adjunction.isWeilEquivariant_counit_conj_iff_trace {Y : D} {T : C} (o : R.obj Y ≅ T)
    (ψ : H.obj Y ⟶ Y) (τ : G.obj T ⟶ T) :
    IsWeilEquivariant H (leftWeilDatum e (G.map o.hom ≫ τ ≫ o.inv)) ψ (adj.counit.app Y) ↔
      IsWeilEquivariant H (leftWeilDatum e τ) ψ (adj.orientationTrace o) := by
  have hn : H.map (L.map o.hom) ≫ e.hom.app T = e.hom.app (R.obj Y) ≫ L.map (G.map o.hom) :=
    e.hom.naturality o.hom
  unfold IsWeilEquivariant leftWeilDatum Adjunction.orientationTrace
  constructor
  · intro h
    simp only [Functor.map_comp, Category.assoc] at h ⊢
    rw [h, ← reassoc_of% hn, ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · intro h
    simp only [Functor.map_comp, Category.assoc] at h ⊢
    rw [← reassoc_of% hn, ← h, ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The trace square**: an orientation `o : R Y ≅ T` is equivariant for the right Weil datum
of `ψ` and a datum `τ` on `T` if and only if its trace `L T ⟶ Y` is equivariant for the
transport of `τ` and `ψ`. -/
lemma Adjunction.isWeilEquivariant_rightWeilDatum_iff_trace {Y : D} {T : C} (o : R.obj Y ≅ T)
    (ψ : H.obj Y ⟶ Y) (τ : G.obj T ⟶ T) :
    IsWeilEquivariant G (rightWeilDatum adj e ψ) τ o.hom ↔
      IsWeilEquivariant H (leftWeilDatum e τ) ψ (adj.orientationTrace o) := by
  rw [← adj.isWeilEquivariant_counit_conj_iff_trace e o ψ τ]
  constructor
  · intro h
    have hv : G.map o.hom ≫ τ ≫ o.inv = rightWeilDatum adj e ψ := by
      unfold IsWeilEquivariant at h
      rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hv]
    exact adj.isWeilEquivariant_counit e ψ
  · intro h
    have hv := adj.eq_rightWeilDatum_of_isWeilEquivariant_counit e ψ h
    unfold IsWeilEquivariant
    rw [← hv, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Trace

section LiftExchange

variable {C D : Type*} [Category* C] [Category* D] {P : ObjectProperty C} {Q : ObjectProperty D}
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (hL : ∀ X, P X → Q (L.obj X))
  (hR : ∀ Y, Q Y → P (R.obj Y)) {G : C ⥤ C} {H : D ⥤ D} (e : L ⋙ H ≅ G ⋙ L)
  (hG : ∀ X, P X → P (G.obj X)) (hH : ∀ Y, Q Y → Q (H.obj Y))

/-- **The right adjoint exchange of a restricted adjunction** is the restriction of the right
adjoint exchange, by uniqueness. -/
lemma Adjunction.rightAdjointExchange_liftFullSubcategory_app_hom
    {eP : P.liftFullSubcategory Q L hL ⋙ Q.liftFullSubcategory Q H hH ≅
      P.liftFullSubcategory P G hG ⋙ P.liftFullSubcategory Q L hL}
    (heP : ∀ X, (eP.inv.app X).hom = e.inv.app X.obj) (Y : Q.FullSubcategory) :
    ((Adjunction.rightAdjointExchange (ObjectProperty.liftFullSubcategoryAdjunction adj hL hR)
      (ObjectProperty.liftFullSubcategoryAdjunction adj hL hR) eP).app Y).hom =
      (Adjunction.rightAdjointExchange adj adj e).app Y.obj := by
  let τ : Q.liftFullSubcategory P R hR ⋙ P.liftFullSubcategory P G hG ⟶
      Q.liftFullSubcategory Q H hH ⋙ Q.liftFullSubcategory P R hR :=
    { app := fun Y ↦ P.homMk ((Adjunction.rightAdjointExchange adj adj e).app Y.obj)
      naturality := fun _ _ f ↦
        P.hom_ext ((Adjunction.rightAdjointExchange adj adj e).naturality f.hom) }
  have hτ : τ = Adjunction.rightAdjointExchange
      (ObjectProperty.liftFullSubcategoryAdjunction adj hL hR)
      (ObjectProperty.liftFullSubcategoryAdjunction adj hL hR) eP := by
    apply Adjunction.rightAdjointExchange_eq_of_unit
    intro c
    apply P.hom_ext
    have h' : G.map (adj.unit.app c.obj) ≫
        (Adjunction.rightAdjointExchange adj adj e).app (L.obj c.obj) =
        adj.unit.app (G.obj c.obj) ≫ R.map (eP.inv.app c).hom := by
      rw [heP]
      exact Adjunction.map_unit_app_comp_rightAdjointExchange_app adj adj e c.obj
    exact h'
  rw [← hτ]
  rfl

end LiftExchange

end CategoryTheory
