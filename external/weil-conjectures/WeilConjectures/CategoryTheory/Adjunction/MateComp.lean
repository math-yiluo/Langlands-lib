/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Adjoints of composites through mates and conjugates

Formal facts about adjoint morphisms along adjunctions, used to compare adjoints through mates of
exchange transformations (`CategoryTheory.Adjunction.homEquiv_comp_mateEquiv`), through conjugates
of composition isomorphisms (`CategoryTheory.Adjunction.homEquiv_homEquiv_comp_hom_app`,
`CategoryTheory.Adjunction.map_map_conjugateIsoEquiv_comp_counit`), together with some
naturality bookkeeping for composite functors.
-/

@[expose] public section

namespace CategoryTheory


/-- The exceptional adjoint of a map through a mate: for an exchange `E = mate(Ξ)` of
`Ξ : G ⋙ L₂ ⟶ L₁ ⋙ H` along `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, the `L₂ ⊣ R₂`-adjoint of
`L₂ η ≫ Ξ ≫ H φ♭ ≫ ψ` is `η ≫ G φ ≫ E ≫ R₂ ψ`:
```
L₂ A ──L₂ η──▶ L₂ G A' ──Ξ──▶ H L₁ A' ──H φ♭──▶ H M ──ψ──▶ N
  ⇕ adjoint                                               ⇕
  A ──η──▶ G A' ──G φ──▶ G R₁ M ──E──▶ R₂ H M ──R₂ ψ──▶ R₂ N
```
-/
lemma Adjunction.homEquiv_comp_mateEquiv {CC CD CP CQ : Type*} [Category CC] [Category CD]
    [Category CP] [Category CQ] {L₁ : CC ⥤ CP} {R₁ : CP ⥤ CC} {L₂ : CD ⥤ CQ} {R₂ : CQ ⥤ CD}
    {G : CC ⥤ CD} {H : CP ⥤ CQ} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (Ξ : G ⋙ L₂ ⟶ L₁ ⋙ H)
    {A : CD} {A' : CC} {M : CP} {N : CQ} (η : A ⟶ G.obj A') (φ : A' ⟶ R₁.obj M)
    (ψ : H.obj M ⟶ N) :
    adj₂.homEquiv _ _ (L₂.map η ≫ Ξ.app A' ≫ H.map ((adj₁.homEquiv _ _).symm φ) ≫ ψ) =
      η ≫ G.map φ ≫ (mateEquiv adj₁ adj₂ Ξ).app M ≫ R₂.map ψ := by
  rw [← Equiv.eq_symm_apply, Adjunction.homEquiv_counit]
  have hc := mateEquiv_counit adj₁ adj₂ Ξ M
  have hn := Ξ.naturality φ
  have hε := adj₂.counit.naturality ψ
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hc hn hε
  simp only [Functor.map_comp, Category.assoc, Adjunction.homEquiv_counit]
  rw [hε, reassoc_of% hc, reassoc_of% hn]

/-- Assembly of the transport along `g` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 3) from the adjunction description of
`T ≫ ζ` and the exchange of the supports. -/
lemma Adjunction.homEquiv_comp_mateEquiv_of_eq {CC CD CP CQ : Type*} [Category CC]
    [Category CD] [Category CP] [Category CQ] {L₁ : CC ⥤ CP} {R₁ : CP ⥤ CC} {L₂ : CD ⥤ CQ}
    {R₂ : CQ ⥤ CD} {G : CC ⥤ CD} {H : CP ⥤ CQ} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (Ξ : G ⋙ L₂ ⟶ L₁ ⋙ H) {A : CD} {A' Z : CC} {M' M : CP} {N : CQ}
    (η : A ⟶ G.obj A') (κ : L₁.obj A' ⟶ M') (δ : M' ⟶ M) (ψ : H.obj M ⟶ N) (T : A' ⟶ Z)
    (ζ : Z ⟶ R₁.obj M) (hc : adj₁.homEquiv _ _ (κ ≫ δ) = T ≫ ζ) (rhs : G.obj Z ⟶ R₂.obj N)
    (E : R₁ ⋙ G ⟶ H ⋙ R₂) (hE : E = mateEquiv adj₁ adj₂ Ξ)
    (h : G.map ζ ≫ E.app M ≫ R₂.map ψ = rhs) :
    adj₂.homEquiv _ _ (L₂.map η ≫ Ξ.app A' ≫ H.map κ ≫ H.map δ ≫ ψ) =
      η ≫ G.map T ≫ rhs := by
  have hκ : κ ≫ δ = (adj₁.homEquiv _ _).symm (T ≫ ζ) := by rw [← hc, Equiv.symm_apply_apply]
  subst hE
  rw [← H.map_comp_assoc, hκ, Adjunction.homEquiv_comp_mateEquiv, G.map_comp, Category.assoc]
  exact congrArg (fun t ↦ η ≫ G.map T ≫ t) h

/-- The points `𝟙 ⟶ Rp_* 𝟙` (units followed by the unit comparisons of the pullbacks) compose:
for adjunctions `Lp ⊣ Rp`, `Lq ⊣ Rq`, `Lpq ⊣ Rpq` with `Lpq ≅ Lq ⋙ Lp` and the conjugate
`Rp ⋙ Rq ≅ Rpq`, compatible unit comparisons give `s_q ≫ Rq s_p = s_{pq} ≫ (Rp ⋙ Rq ≅ Rpq)⁻¹`. -/
lemma Adjunction.unit_map_comp_unit_map {CA CB CC : Type*} [Category CA] [Category CB]
    [Category CC] {Lp : CB ⥤ CA} {Rp : CA ⥤ CB} {Lq : CC ⥤ CB} {Rq : CB ⥤ CC} {Lpq : CC ⥤ CA}
    {Rpq : CA ⥤ CC} (ap : Lp ⊣ Rp) (aq : Lq ⊣ Rq) (apq : Lpq ⊣ Rpq) (cU : Lpq ≅ Lq ⋙ Lp)
    (cR : Rp ⋙ Rq ≅ Rpq) (hcR : cR.inv = conjugateEquiv apq (aq.comp ap) cU.inv) {oC : CC}
    {oB : CB} {oA : CA} (eq : Lq.obj oC ⟶ oB) (ep : Lp.obj oB ⟶ oA) (epq : Lpq.obj oC ⟶ oA)
    (hε : cU.hom.app oC ≫ Lp.map eq ≫ ep = epq) :
    (aq.unit.app oC ≫ Rq.map eq) ≫ Rq.map (ap.unit.app oB ≫ Rp.map ep) =
      (apq.unit.app oC ≫ Rpq.map epq) ≫ cR.inv.app oA := by
  have hU := unit_conjugateEquiv apq (aq.comp ap) cU.inv oC
  rw [← hcR] at hU
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_unit_app] at hU
  have hη := ap.unit.naturality eq
  have hn := cR.inv.naturality epq
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hη hn
  rw [Category.assoc, Category.assoc, hn, reassoc_of% hU, ← hε]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  congr 2
  rw [Functor.map_comp, ← reassoc_of% hη]


/-- The adjoint for a composite adjunction through the conjugate composition isomorphism: for
`Lpq ≅ Lq ⋙ Lp` and its conjugate `Rp ⋙ Rq ≅ Rpq`, `(φ♯)♯ ≫ (Rp ⋙ Rq ≅ Rpq) = (c ≫ φ)♯`. -/
lemma Adjunction.homEquiv_homEquiv_comp_hom_app {CA CB CC : Type*} [Category CA] [Category CB]
    [Category CC] {Lp : CB ⥤ CA} {Rp : CA ⥤ CB} {Lq : CC ⥤ CB} {Rq : CB ⥤ CC} {Lpq : CC ⥤ CA}
    {Rpq : CA ⥤ CC} (ap : Lp ⊣ Rp) (aq : Lq ⊣ Rq) (apq : Lpq ⊣ Rpq) (cU : Lpq ≅ Lq ⋙ Lp)
    (cR : Rp ⋙ Rq ≅ Rpq) (hcR : cR.inv = conjugateEquiv apq (aq.comp ap) cU.inv) {oC : CC}
    {oA : CA} (φ : Lp.obj (Lq.obj oC) ⟶ oA) :
    aq.homEquiv _ _ (ap.homEquiv _ _ φ) ≫ cR.hom.app oA =
      apq.homEquiv _ _ (cU.hom.app oC ≫ φ) := by
  have h := Adjunction.unit_map_comp_unit_map ap aq apq cU cR hcR (𝟙 _) φ (cU.hom.app oC ≫ φ)
    (by simp)
  rw [← cancel_mono (cR.inv.app oA)]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  simpa [Adjunction.homEquiv_unit] using h


/-- Moving maps into and out of an adjoint:
`d ≫ (x₁ ≫ x₂)♯ ≫ R e ≫ t = (L d ≫ x₁ ≫ x₂ ≫ e)♯ ≫ t`. -/
lemma Adjunction.comp_homEquiv_comp_map {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {P Q : C} {M M' N : D} {T : C} (d : P ⟶ Q) (x₁ : L.obj Q ⟶ M')
    (x₂ : M' ⟶ M) (e : M ⟶ N) (t : R.obj N ⟶ T) :
    d ≫ adj.homEquiv _ _ (x₁ ≫ x₂) ≫ R.map e ≫ t =
      adj.homEquiv _ _ (L.map d ≫ x₁ ≫ x₂ ≫ e) ≫ t := by
  rw [Adjunction.homEquiv_naturality_left]
  simp [Adjunction.homEquiv_naturality_right]

/-- `Adjunction.homEquiv_naturality_right`, followed by a morphism. -/
lemma Adjunction.homEquiv_comp_map_comp {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {P : C} {M N : D} {T : C} (x : L.obj P ⟶ M) (e : M ⟶ N)
    (t : R.obj N ⟶ T) :
    adj.homEquiv _ _ x ≫ R.map e ≫ t = adj.homEquiv _ _ (x ≫ e) ≫ t := by
  rw [Adjunction.homEquiv_naturality_right, Category.assoc]


/-- The counit of a composite adjunction through the conjugate composition isomorphisms:
```
Lp La Rap N ⟶ Lp La Ra Rp N ⟶ Lp Rp N ⟶ N
     ‖                                  ‖
Lp La Rap N ⟶ Lap Rap N ─────────────▶ N
```
for `Rap ≅ Rp ⋙ Ra` the conjugate of `Lap ≅ La ⋙ Lp`. -/
lemma Adjunction.map_map_conjugateIsoEquiv_comp_counit {CA CB CC : Type*} [Category CA]
    [Category CB] [Category CC] {La : CA ⥤ CB} {Ra : CB ⥤ CA} {Lp : CB ⥤ CC} {Rp : CC ⥤ CB}
    {Lap : CA ⥤ CC} {Rap : CC ⥤ CA} (Aa : La ⊣ Ra) (Ap : Lp ⊣ Rp) (Aap : Lap ⊣ Rap)
    (c : Lap ≅ La ⋙ Lp) (N : CC) :
    Lp.map (La.map ((conjugateIsoEquiv Aap (Aa.comp Ap) c.symm).hom.app N) ≫
        Aa.counit.app (Rp.obj N)) ≫ Ap.counit.app N =
      c.inv.app (Rap.obj N) ≫ Aap.counit.app N := by
  have h := conjugateEquiv_counit Aap (Aa.comp Ap) c.inv N
  simp only [Functor.comp_map, Adjunction.comp_counit_app, Functor.comp_obj] at h
  rw [Functor.map_comp, Category.assoc]
  exact h


lemma NatTrans.naturality_comp_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ E} (α : F₁ ⋙ G₁ ⟶ F₂ ⋙ G₂) {X Y : C} (x : X ⟶ Y) {Z : E}
    (h : G₂.obj (F₂.obj Y) ⟶ Z) :
    G₁.map (F₁.map x) ≫ α.app Y ≫ h = α.app X ≫ G₂.map (F₂.map x) ≫ h := by
  simpa using α.naturality_assoc x h

@[reassoc]
lemma Functor.map_map_hom_app_comp_map_map_inv_app {B C D E : Type*} [Category B] [Category C]
    [Category D] [Category E] (F : D ⥤ E) (G : C ⥤ D) {H H' : B ⥤ C} (e : H ≅ H') (X : B) :
    F.map (G.map (e.hom.app X)) ≫ F.map (G.map (e.inv.app X)) = 𝟙 _ := by
  rw [← F.map_comp, ← G.map_comp, Iso.hom_inv_id_app, G.map_id, F.map_id]

@[reassoc]
lemma Iso.hom_app_comp_map_comp_inv_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (φ : X ⟶ Y) : e.hom.app X ≫ G.map φ ≫ e.inv.app Y = F.map φ := by
  rw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]

@[reassoc]
lemma Functor.map_hom_app_comp_map_map_comp_map_inv_app {C D E : Type*} [Category C] [Category D]
    [Category E] (K : D ⥤ E) {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (φ : X ⟶ Y) :
    K.map (e.hom.app X) ≫ K.map (G.map φ) ≫ K.map (e.inv.app Y) = K.map (F.map φ) := by
  rw [← K.map_comp, ← K.map_comp, Iso.hom_app_comp_map_comp_inv_app]

@[reassoc]
lemma NatTrans.app_comp_map_map {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (α : F ⟶ G ⋙ H) {X Y : C} (x : X ⟶ Y) :
    α.app X ≫ H.map (G.map x) = F.map x ≫ α.app Y :=
  (α.naturality x).symm

@[reassoc]
lemma NatTrans.map_map_comp_app {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (α : G ⋙ H ⟶ F) {X Y : C} (x : X ⟶ Y) :
    H.map (G.map x) ≫ α.app Y = α.app X ≫ F.map x :=
  α.naturality x

@[reassoc]
lemma Functor.map_app_comp_map_map {B C D : Type*} [Category B] [Category C] [Category D]
    (K : C ⥤ D) {F G : B ⥤ C} (α : F ⟶ G) {X Y : B} (x : X ⟶ Y) :
    K.map (α.app X) ≫ K.map (G.map x) = K.map (F.map x) ≫ K.map (α.app Y) := by
  rw [← K.map_comp, ← K.map_comp, α.naturality]

@[reassoc]
lemma Iso.hom_app_comp_map₃_comp_inv_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {X Y Z W : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) :
    e.hom.app X ≫ G.map a ≫ G.map b ≫ G.map c ≫ e.inv.app W = F.map a ≫ F.map b ≫ F.map c := by
  rw [← G.map_comp_assoc, ← G.map_comp_assoc, Iso.hom_app_comp_map_comp_inv_app, F.map_comp,
    F.map_comp, Category.assoc]

end CategoryTheory
