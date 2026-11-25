/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatible

/-!
# Units, counits and exchange morphisms compatible with commutation squares

Let `adj : L ⊣ R` and `adj' : L' ⊣ R'` be adjunctions on two "levels" related by functors
`T₁` and `T₂`, a commutation square `ιL : L ⋙ T₂ ≅ T₁ ⋙ L'` of the left adjoints and a
commutation square `ιR : R ⋙ T₁ ≅ T₂ ⋙ R'` of the right adjoints which is the mate of the inverse
of `ιL` (`CategoryTheory.Adjunction.IsMateSquare`). Then the units and the counits of the two
adjunctions are compatible with these commutation squares
(`CategoryTheory.NatTrans.SquareCompatible.unit`,
`CategoryTheory.NatTrans.SquareCompatible.counit`),
hence so are the exchange morphisms `CategoryTheory.Adjunction.exchangeRight` and
`CategoryTheory.Adjunction.exchangeLeft` of compatible commutation isomorphisms, and the
conjugates of compatible transformations of left adjoints.
-/

@[expose] public section

namespace CategoryTheory

section IsMate

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'} {T₁ : A ⥤ A'} {T₂ : B ⥤ B'}

/-- The commutation square `ιR : R ⋙ T₁ ≅ T₂ ⋙ R'` of the right adjoints is the mate of the
inverse of the commutation square `ιL : L ⋙ T₂ ≅ T₁ ⋙ L'` of the left adjoints, for the
adjunctions `adj : L ⊣ R` and `adj' : L' ⊣ R'`. -/
def Adjunction.IsMateSquare (adj : L ⊣ R) (adj' : L' ⊣ R') (ιL : L ⋙ T₂ ≅ T₁ ⋙ L')
    (ιR : R ⋙ T₁ ≅ T₂ ⋙ R') : Prop :=
  ∀ K, ιR.hom.app K = adj'.unit.app (T₁.obj (R.obj K)) ≫ R'.map (ιL.inv.app (R.obj K)) ≫
    R'.map (T₂.map (adj.counit.app K))

lemma Adjunction.isMateSquare_iff (adj : L ⊣ R) (adj' : L' ⊣ R') (ιL : L ⋙ T₂ ≅ T₁ ⋙ L')
    (ιR : R ⋙ T₁ ≅ T₂ ⋙ R') :
    adj.IsMateSquare adj' ιL ιR ↔ mateEquiv adj adj' (TwoSquare.mk _ _ _ _ ιL.inv) = ιR.hom := by
  constructor
  · intro h
    ext K
    rw [h K]
    simp
  · intro h K
    rw [← h]
    simp

end IsMate

namespace NatTrans.SquareCompatible

section Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'} {T₁ : A ⥤ A'} {T₂ : B ⥤ B'}
  {adj : L ⊣ R} {adj' : L' ⊣ R'} {ιL : L ⋙ T₂ ≅ T₁ ⋙ L'} {ιR : R ⋙ T₁ ≅ T₂ ⋙ R'}

/-- The units of adjunctions are compatible with commutation squares of the left adjoints and
their mates. -/
lemma unit (h : adj.IsMateSquare adj' ιL ιR) :
    SquareCompatible (Functor.idSquareIso T₁) (Functor.pasteSquareIso ιL ιR) adj.unit
      adj'.unit := by
  intro K
  simp only [Functor.id_obj, Functor.comp_obj, Functor.pasteSquareIso_hom_app,
    Functor.idSquareIso_hom_app, Category.id_comp]
  rw [h (L.obj K), Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  have h₁ := ιL.inv.naturality (adj.unit.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at h₁
  rw [← adj'.unit_naturality_assoc, ← Functor.map_comp, reassoc_of% h₁, ← T₂.map_comp_assoc,
    adj.left_triangle_components, T₂.map_id, Category.id_comp, Iso.inv_hom_id_app]
  simp

/-- The counits of adjunctions are compatible with commutation squares of the left adjoints and
their mates. -/
lemma counit (h : adj.IsMateSquare adj' ιL ιR) :
    SquareCompatible (Functor.pasteSquareIso ιR ιL) (Functor.idSquareIso T₂) adj.counit
      adj'.counit := by
  intro K
  simp only [Functor.id_obj, Functor.comp_obj, Functor.pasteSquareIso_hom_app,
    Functor.idSquareIso_hom_app, Category.comp_id]
  rw [h K]
  simp only [Functor.map_comp, Category.assoc]
  rw [adj'.counit_naturality, adj'.counit_naturality_assoc, adj'.left_triangle_components_assoc]
  simp

end Adjunction

section Exchange

/-- `Functor.squareTransport` of compatible commutation isomorphisms is compatible with the
pasted commutation squares. -/
lemma squareTransport {C₁ C₂ C₃ C₃' C₄ C₅ D₁ D₂ D₃ D₃' D₄ D₅ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] [Category* C₃'] [Category* C₄] [Category* C₅]
    [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₃'] [Category* D₄]
    [Category* D₅] {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₃' : C₃' ⥤ D₃'}
    {T₄ : C₄ ⥤ D₄} {T₅ : C₅ ⥤ D₅}
    {G₁ : C₂ ⥤ C₃} {G₂ : C₃ ⥤ C₄} {G₃ : C₂ ⥤ C₃'} {G₄ : C₃' ⥤ C₄} {R : C₁ ⥤ C₂} {R' : C₄ ⥤ C₅}
    {H₁ : D₂ ⥤ D₃} {H₂ : D₃ ⥤ D₄} {H₃ : D₂ ⥤ D₃'} {H₄ : D₃' ⥤ D₄}
    {Q : D₁ ⥤ D₂} {Q' : D₄ ⥤ D₅}
    (ιG₁ : G₁ ⋙ T₃ ≅ T₂ ⋙ H₁) (ιG₂ : G₂ ⋙ T₄ ≅ T₃ ⋙ H₂) (ιG₃ : G₃ ⋙ T₃' ≅ T₂ ⋙ H₃)
    (ιG₄ : G₄ ⋙ T₄ ≅ T₃' ⋙ H₄) (ιR : R ⋙ T₂ ≅ T₁ ⋙ Q) (ιR' : R' ⋙ T₅ ≅ T₄ ⋙ Q')
    {θ : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄} {θ' : H₁ ⋙ H₂ ≅ H₃ ⋙ H₄}
    (h : SquareCompatible (Functor.pasteSquareIso ιG₁ ιG₂) (Functor.pasteSquareIso ιG₃ ιG₄)
      θ.hom θ'.hom) :
    SquareCompatible
      (Functor.pasteSquareIso (Functor.pasteSquareIso ιR ιG₁) (Functor.pasteSquareIso ιG₂ ιR'))
      (Functor.pasteSquareIso (Functor.pasteSquareIso ιR ιG₃) (Functor.pasteSquareIso ιG₄ ιR'))
      (Functor.squareTransport R R' θ).hom (Functor.squareTransport Q Q' θ').hom := by
  intro K
  have hθ := h (R.obj K)
  simp only [Functor.comp_obj, Functor.pasteSquareIso_hom_app] at hθ
  have h₁ := ιR'.hom.naturality (θ.hom.app (R.obj K))
  have h₂ := θ'.hom.naturality (ιR.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  simp only [Functor.comp_obj, Functor.squareTransport_hom_app, Functor.pasteSquareIso_hom_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  have key : T₄.map (θ.hom.app (R.obj K)) ≫ ιG₄.hom.app (G₃.obj (R.obj K)) ≫
      H₄.map (ιG₃.hom.app (R.obj K)) ≫ H₄.map (H₃.map (ιR.hom.app K)) =
      ιG₂.hom.app (G₁.obj (R.obj K)) ≫ H₂.map (ιG₁.hom.app (R.obj K)) ≫
        H₂.map (H₁.map (ιR.hom.app K)) ≫ θ'.hom.app (Q.obj (T₁.obj K)) := by
    rw [reassoc_of% hθ, h₂]
  rw [reassoc_of% h₁, ← Q'.map_comp, ← Q'.map_comp, ← Q'.map_comp, key]
  simp

variable {A B A' B' Aₜ Bₜ A'ₜ B'ₜ : Type*} [Category* A] [Category* B] [Category* A']
  [Category* B'] [Category* Aₜ] [Category* Bₜ] [Category* A'ₜ] [Category* B'ₜ]
  {TA : A ⥤ Aₜ} {TB : B ⥤ Bₜ} {TA' : A' ⥤ A'ₜ} {TB' : B' ⥤ B'ₜ}

/-- The exchange morphism `Rf ⋙ G ⟶ G' ⋙ Rf'` of a commutation isomorphism `θ` of left adjoints
is compatible with the commutation squares, if `θ` is. -/
lemma exchangeRight {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'} {G : B ⥤ B'}
    {G' : A ⥤ A'} {af : Lf ⊣ Rf} {af' : Lf' ⊣ Rf'} {θ : G ⋙ Lf' ≅ Lf ⋙ G'}
    {Lfₜ : Bₜ ⥤ Aₜ} {Rfₜ : Aₜ ⥤ Bₜ} {Lf'ₜ : B'ₜ ⥤ A'ₜ} {Rf'ₜ : A'ₜ ⥤ B'ₜ} {Gₜ : Bₜ ⥤ B'ₜ}
    {G'ₜ : Aₜ ⥤ A'ₜ} {afₜ : Lfₜ ⊣ Rfₜ} {af'ₜ : Lf'ₜ ⊣ Rf'ₜ} {θₜ : Gₜ ⋙ Lf'ₜ ≅ Lfₜ ⋙ G'ₜ}
    {ιLf : Lf ⋙ TA ≅ TB ⋙ Lfₜ} {ιRf : Rf ⋙ TB ≅ TA ⋙ Rfₜ} {ιLf' : Lf' ⋙ TA' ≅ TB' ⋙ Lf'ₜ}
    {ιRf' : Rf' ⋙ TB' ≅ TA' ⋙ Rf'ₜ} {ιG : G ⋙ TB' ≅ TB ⋙ Gₜ} {ιG' : G' ⋙ TA' ≅ TA ⋙ G'ₜ}
    (hf : af.IsMateSquare afₜ ιLf ιRf) (hf' : af'.IsMateSquare af'ₜ ιLf' ιRf')
    (hθ : SquareCompatible (Functor.pasteSquareIso ιG ιLf') (Functor.pasteSquareIso ιLf ιG')
      θ.hom θₜ.hom) :
    SquareCompatible (Functor.pasteSquareIso ιRf ιG) (Functor.pasteSquareIso ιG' ιRf')
      (Adjunction.exchangeRight af af' θ) (Adjunction.exchangeRight afₜ af'ₜ θₜ) :=
  (((rightUnitor_inv _).comp (whiskerLeft _ (unit hf'))).comp
    ((squareTransport _ _ _ _ _ _ hθ).comp ((whiskerRight _ (counit hf)).comp
      (leftUnitor_hom _))))

/-- The exchange morphism `H ⋙ jS' ⟶ jS ⋙ H'` of a commutation isomorphism `θ` of right
adjoints is compatible with the commutation squares, if `θ` is. -/
lemma exchangeLeft {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'} {jU' : B' ⥤ A'} {H : A ⥤ A'}
    {H' : B ⥤ B'} {aj : jS ⊣ jU} {aj' : jS' ⊣ jU'} {θ : jU ⋙ H ≅ H' ⋙ jU'}
    {jSₜ : Aₜ ⥤ Bₜ} {jUₜ : Bₜ ⥤ Aₜ} {jS'ₜ : A'ₜ ⥤ B'ₜ} {jU'ₜ : B'ₜ ⥤ A'ₜ} {Hₜ : Aₜ ⥤ A'ₜ}
    {H'ₜ : Bₜ ⥤ B'ₜ} {ajₜ : jSₜ ⊣ jUₜ} {aj'ₜ : jS'ₜ ⊣ jU'ₜ} {θₜ : jUₜ ⋙ Hₜ ≅ H'ₜ ⋙ jU'ₜ}
    {ιjS : jS ⋙ TB ≅ TA ⋙ jSₜ} {ιjU : jU ⋙ TA ≅ TB ⋙ jUₜ} {ιjS' : jS' ⋙ TB' ≅ TA' ⋙ jS'ₜ}
    {ιjU' : jU' ⋙ TA' ≅ TB' ⋙ jU'ₜ} {ιH : H ⋙ TA' ≅ TA ⋙ Hₜ} {ιH' : H' ⋙ TB' ≅ TB ⋙ H'ₜ}
    (hj : aj.IsMateSquare ajₜ ιjS ιjU) (hj' : aj'.IsMateSquare aj'ₜ ιjS' ιjU')
    (hθ : SquareCompatible (Functor.pasteSquareIso ιjU ιH) (Functor.pasteSquareIso ιH' ιjU')
      θ.hom θₜ.hom) :
    SquareCompatible (Functor.pasteSquareIso ιH ιjS') (Functor.pasteSquareIso ιjS ιH')
      (Adjunction.exchangeLeft aj aj' θ) (Adjunction.exchangeLeft ajₜ aj'ₜ θₜ) :=
  (((leftUnitor_inv _).comp (whiskerRight _ (unit hj))).comp
    ((squareTransport _ _ _ _ _ _ hθ).comp ((whiskerLeft _ (counit hj')).comp
      (rightUnitor_hom _))))

end Exchange

section Conjugate

variable {A B Aₜ Bₜ : Type*} [Category* A] [Category* B] [Category* Aₜ] [Category* Bₜ]
  {TA : A ⥤ Aₜ} {TB : B ⥤ Bₜ}

lemma _root_.CategoryTheory.conjugateEquiv_eq_comp {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) :
    conjugateEquiv adj₁ adj₂ α = (Functor.rightUnitor R₁).inv ≫
      Functor.whiskerLeft R₁ adj₂.unit ≫ Functor.whiskerLeft R₁ (Functor.whiskerRight α R₂) ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight adj₁.counit R₂ ≫
      (Functor.leftUnitor R₂).hom := by
  ext K
  simp [conjugateEquiv_apply_app]

/-- The conjugate of a transformation of left adjoints compatible with commutation squares is
compatible with the mated commutation squares of the right adjoints. -/
lemma conjugateEquiv {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {adj₁ : L₁ ⊣ R₁} {adj₂ : L₂ ⊣ R₂}
    {L₁ₜ L₂ₜ : Aₜ ⥤ Bₜ} {R₁ₜ R₂ₜ : Bₜ ⥤ Aₜ} {adj₁ₜ : L₁ₜ ⊣ R₁ₜ} {adj₂ₜ : L₂ₜ ⊣ R₂ₜ}
    {ιL₁ : L₁ ⋙ TB ≅ TA ⋙ L₁ₜ} {ιL₂ : L₂ ⋙ TB ≅ TA ⋙ L₂ₜ} {ιR₁ : R₁ ⋙ TA ≅ TB ⋙ R₁ₜ}
    {ιR₂ : R₂ ⋙ TA ≅ TB ⋙ R₂ₜ} (h₁ : adj₁.IsMateSquare adj₁ₜ ιL₁ ιR₁)
    (h₂ : adj₂.IsMateSquare adj₂ₜ ιL₂ ιR₂) {α : L₂ ⟶ L₁} {αₜ : L₂ₜ ⟶ L₁ₜ}
    (hα : SquareCompatible ιL₂ ιL₁ α αₜ) :
    SquareCompatible ιR₁ ιR₂ (CategoryTheory.conjugateEquiv adj₁ adj₂ α)
      (CategoryTheory.conjugateEquiv adj₁ₜ adj₂ₜ αₜ) := by
  rw [conjugateEquiv_eq_comp, conjugateEquiv_eq_comp]
  exact (rightUnitor_inv _).comp ((whiskerLeft _ (unit h₂)).comp
    ((whiskerLeft _ (whiskerRight _ hα)).comp ((associator_inv _ _ _).comp
      ((whiskerRight _ (counit h₁)).comp (leftUnitor_hom _)))))

lemma _root_.CategoryTheory.conjugateEquiv_symm_eq_comp {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (β : R₁ ⟶ R₂) :
    (CategoryTheory.conjugateEquiv adj₁ adj₂).symm β = (Functor.leftUnitor L₂).inv ≫
      Functor.whiskerRight adj₁.unit L₂ ≫ Functor.whiskerRight (Functor.whiskerLeft L₁ β) L₂ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft L₁ adj₂.counit ≫
      (Functor.rightUnitor L₁).hom := by
  ext K
  simp [conjugateEquiv_symm_apply_app]

/-- The inverse conjugate of a transformation of right adjoints compatible with commutation
squares is compatible with the commutation squares of the left adjoints. -/
lemma conjugateEquiv_symm {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {adj₁ : L₁ ⊣ R₁} {adj₂ : L₂ ⊣ R₂}
    {L₁ₜ L₂ₜ : Aₜ ⥤ Bₜ} {R₁ₜ R₂ₜ : Bₜ ⥤ Aₜ} {adj₁ₜ : L₁ₜ ⊣ R₁ₜ} {adj₂ₜ : L₂ₜ ⊣ R₂ₜ}
    {ιL₁ : L₁ ⋙ TB ≅ TA ⋙ L₁ₜ} {ιL₂ : L₂ ⋙ TB ≅ TA ⋙ L₂ₜ} {ιR₁ : R₁ ⋙ TA ≅ TB ⋙ R₁ₜ}
    {ιR₂ : R₂ ⋙ TA ≅ TB ⋙ R₂ₜ} (h₁ : adj₁.IsMateSquare adj₁ₜ ιL₁ ιR₁)
    (h₂ : adj₂.IsMateSquare adj₂ₜ ιL₂ ιR₂) {β : R₁ ⟶ R₂} {βₜ : R₁ₜ ⟶ R₂ₜ}
    (hβ : SquareCompatible ιR₁ ιR₂ β βₜ) :
    SquareCompatible ιL₂ ιL₁ ((CategoryTheory.conjugateEquiv adj₁ adj₂).symm β)
      ((CategoryTheory.conjugateEquiv adj₁ₜ adj₂ₜ).symm βₜ) := by
  rw [conjugateEquiv_symm_eq_comp, conjugateEquiv_symm_eq_comp]
  exact (leftUnitor_inv _).comp ((whiskerRight _ (unit h₁)).comp
    ((whiskerRight _ (whiskerLeft _ hβ)).comp ((associator_hom _ _ _).comp
      ((whiskerLeft _ (counit h₂)).comp (rightUnitor_hom _)))))

end Conjugate

end NatTrans.SquareCompatible

section OfUnit

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'} {T₁ : A ⥤ A'} {T₂ : B ⥤ B'}
  {adj : L ⊣ R} {adj' : L' ⊣ R'} {ιL : L ⋙ T₂ ≅ T₁ ⋙ L'} {ιR : R ⋙ T₁ ≅ T₂ ⋙ R'}

/-- A commutation square of the right adjoints such that the units are compatible with the
commutation squares is the mate of the inverse of the commutation square of the left
adjoints. -/
lemma Adjunction.IsMateSquare.of_unit
    (h : NatTrans.SquareCompatible (Functor.idSquareIso T₁) (Functor.pasteSquareIso ιL ιR)
      adj.unit adj'.unit) :
    adj.IsMateSquare adj' ιL ιR := by
  intro K
  have hK := h (R.obj K)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.pasteSquareIso_hom_app,
    Functor.idSquareIso_hom_app, Category.id_comp] at hK
  have hn := ιR.hom.naturality (adj.counit.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← hK, Category.assoc, Category.assoc, ← R'.map_comp_assoc, Iso.hom_inv_id_app]
  erw [R'.map_id, Category.id_comp]
  rw [← hn, ← T₁.map_comp_assoc, adj.right_triangle_components, T₁.map_id, Category.id_comp]
  rfl

end OfUnit

section IsMateComp

variable {A B C Aₜ Bₜ Cₜ : Type*} [Category* A] [Category* B] [Category* C] [Category* Aₜ]
  [Category* Bₜ] [Category* Cₜ] {TA : A ⥤ Aₜ} {TB : B ⥤ Bₜ} {TC : C ⥤ Cₜ}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₁ₜ : Aₜ ⥤ Bₜ} {R₁ₜ : Bₜ ⥤ Aₜ}
  {L₂ₜ : Bₜ ⥤ Cₜ} {R₂ₜ : Cₜ ⥤ Bₜ} {adj₁ : L₁ ⊣ R₁} {adj₂ : L₂ ⊣ R₂} {adj₁ₜ : L₁ₜ ⊣ R₁ₜ}
  {adj₂ₜ : L₂ₜ ⊣ R₂ₜ} {ιL₁ : L₁ ⋙ TB ≅ TA ⋙ L₁ₜ} {ιL₂ : L₂ ⋙ TC ≅ TB ⋙ L₂ₜ}
  {ιR₁ : R₁ ⋙ TA ≅ TB ⋙ R₁ₜ} {ιR₂ : R₂ ⋙ TB ≅ TC ⋙ R₂ₜ}

/-- Mated commutation squares of composable adjunctions paste to mated commutation squares of
the composite adjunctions. -/
lemma Adjunction.IsMateSquare.comp (h₁ : adj₁.IsMateSquare adj₁ₜ ιL₁ ιR₁)
    (h₂ : adj₂.IsMateSquare adj₂ₜ ιL₂ ιR₂) :
    (adj₁.comp adj₂).IsMateSquare (adj₁ₜ.comp adj₂ₜ) (Functor.pasteSquareIso ιL₁ ιL₂)
      (Functor.pasteSquareIso ιR₂ ιR₁) := by
  rw [Adjunction.isMateSquare_iff] at h₁ h₂ ⊢
  have := mateEquiv_hcomp adj₁ adj₁ₜ adj₂ adj₂ₜ (TwoSquare.mk _ _ _ _ ιL₁.inv)
    (TwoSquare.mk _ _ _ _ ιL₂.inv)
  rw [h₁, h₂] at this
  convert this using 2
  · ext K
    simp [TwoSquare.vComp]
  · ext K
    simp [TwoSquare.hComp]

end IsMateComp

section ConjugateComp

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₂ ⥤ C₄} {R₂ : C₄ ⥤ C₂} {L₃ : C₁ ⥤ C₃} {R₃ : C₃ ⥤ C₁}
  {L₄ : C₃ ⥤ C₄} {R₄ : C₄ ⥤ C₃}

/-- The conjugate of a transformation `L₃ ⋙ L₄ ⟶ L₁ ⋙ L₂` along composite adjunctions of a
square of adjunctions is obtained by taking mates twice, first along `L₁ ⊣ R₁` and `L₄ ⊣ R₄`,
then along `L₂ ⊣ R₂` and `L₃ ⊣ R₃`. -/
theorem conjugateEquiv_comp_eq_mateEquiv_mateEquiv (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : L₃ ⊣ R₃)
    (b₂ : L₄ ⊣ R₄) (α : L₃ ⋙ L₄ ⟶ L₁ ⋙ L₂) :
    conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) α = mateEquiv a₂ b₁ (mateEquiv a₁ b₂ α) := by
  ext K
  simp only [conjugateEquiv_apply_app, Adjunction.comp_unit_app, Adjunction.comp_counit_app,
    mateEquiv_apply, Functor.comp_obj, Functor.comp_map, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc, Functor.id_obj]

end ConjugateComp

section MateWhisker

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G G' : C ⥤ E} {H H' : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate of a 2-square precomposed with a transformation of its top side. -/
lemma mateEquiv_whiskerRight_comp (β : G' ⟶ G) (α : TwoSquare G L₁ L₂ H) :
    mateEquiv adj₁ adj₂ (Functor.whiskerRight β L₂ ≫ α) =
      Functor.whiskerLeft R₁ β ≫ (mateEquiv adj₁ adj₂ α) := by
  ext K
  simp only [mateEquiv_apply, Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  simp

/-- The mate of a 2-square postcomposed with a transformation of its bottom side. -/
lemma mateEquiv_comp_whiskerLeft (α : TwoSquare G L₁ L₂ H) (γ : H ⟶ H') :
    mateEquiv adj₁ adj₂ (α ≫ Functor.whiskerLeft L₁ γ) =
      (mateEquiv adj₁ adj₂ α) ≫ Functor.whiskerRight γ R₂ := by
  ext K
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerRight_app]
  simp [← Functor.map_comp]

/-- Mates for adjunctions whose right adjoints are replaced by isomorphic functors. -/
lemma mateEquiv_ofNatIsoRight {R₁' : D ⥤ C} {R₂' : F ⥤ E} (e₁ : R₁ ≅ R₁') (e₂ : R₂ ≅ R₂')
    (α : TwoSquare G L₁ L₂ H) :
    mateEquiv (adj₁.ofNatIsoRight e₁) (adj₂.ofNatIsoRight e₂) α =
      Functor.whiskerRight e₁.inv G ≫ (mateEquiv adj₁ adj₂ α) ≫
        Functor.whiskerLeft H e₂.hom := by
  ext K
  simp only [Functor.comp_obj, mateEquiv_apply, Adjunction.ofNatIsoRight_unit,
    Functor.whiskerLeft_comp, Functor.whiskerLeft_twice, Adjunction.ofNatIsoRight_counit,
    Functor.whiskerRight_comp, Functor.whiskerRight_twice, Category.assoc, Iso.inv_hom_id_assoc,
    NatTrans.comp_app, Functor.id_obj, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    NatTrans.naturality, NatTrans.naturality_assoc]
  have hα := α.naturality (e₁.inv.app K)
  simp only [Functor.comp_map] at hα
  rw [← adj₂.unit_naturality_assoc, ← e₂.hom.naturality_assoc]
  have hα' := congrArg R₂'.map hα
  simp only [Functor.map_comp] at hα'
  rw [e₂.hom.naturality_assoc, e₂.hom.naturality_assoc, reassoc_of% hα']

/-- The inverse mate for adjunctions whose right adjoints are replaced by isomorphic
functors. -/
lemma mateEquiv_symm_ofNatIsoRight {R₁' : D ⥤ C} {R₂' : F ⥤ E} (e₁ : R₁ ≅ R₁')
    (e₂ : R₂ ≅ R₂') (β : TwoSquare R₁' H G R₂') :
    (mateEquiv (adj₁.ofNatIsoRight e₁) (adj₂.ofNatIsoRight e₂)).symm β =
      (mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _
        (Functor.whiskerRight e₁.hom G ≫ β ≫ Functor.whiskerLeft H e₂.inv)) := by
  rw [Equiv.symm_apply_eq]
  ext d
  rw [mateEquiv_ofNatIsoRight, Equiv.apply_symm_apply]
  simp [TwoSquare.mk, ← Functor.map_comp_assoc]

end MateWhisker

section OfMate

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {T : A ⥤ A'} {T' : B ⥤ B'} {Res : A' ⥤ A} {Res' : B' ⥤ B} (adjT : T ⊣ Res)
  (adjT' : T' ⊣ Res')
  {F G : A ⥤ B} {F' G' : A' ⥤ B'} {ιF : F ⋙ T' ≅ T ⋙ F'} {ιG : G ⋙ T' ≅ T ⋙ G'}

/-- Compatibility with commutation squares can be checked on the mates of the commutation
squares, along adjunctions `T ⊣ Res` and `T' ⊣ Res'`. -/
lemma NatTrans.SquareCompatible.of_mateEquiv {α : F ⟶ G} {α' : F' ⟶ G'}
    (h : Functor.whiskerLeft Res α ≫ (mateEquiv adjT adjT' (TwoSquare.mk _ _ _ _ ιG.hom)) =
      (mateEquiv adjT adjT' (TwoSquare.mk _ _ _ _ ιF.hom)) ≫
        Functor.whiskerRight α' Res') :
    SquareCompatible ιF ιG α α' := by
  have h' : Functor.whiskerRight α T' ≫ ιG.hom = ιF.hom ≫ Functor.whiskerLeft T α' := by
    apply (mateEquiv adjT adjT').injective
    rw [mateEquiv_whiskerRight_comp adjT adjT' α (TwoSquare.mk _ _ _ _ ιG.hom),
      mateEquiv_comp_whiskerLeft adjT adjT' (TwoSquare.mk _ _ _ _ ιF.hom) α']
    exact h
  intro K
  simpa using NatTrans.congr_app h' K

end OfMate

section PasteHComp

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category* A₁] [Category* A₂] [Category* A₃]
  [Category* B₁] [Category* B₂] [Category* B₃]
  {F₁ : A₁ ⥤ A₂} {F₂ : A₂ ⥤ A₃} {F₁' : B₁ ⥤ B₂} {F₂' : B₂ ⥤ B₃}
  {T₁ : A₁ ⥤ B₁} {T₂ : A₂ ⥤ B₂} {T₃ : A₃ ⥤ B₃}

/-- The pasted commutation square is the horizontal composite of the two 2-squares. -/
lemma Functor.pasteSquareIso_hom_eq_hComp (ι₁ : F₁ ⋙ T₂ ≅ T₁ ⋙ F₁')
    (ι₂ : F₂ ⋙ T₃ ≅ T₂ ⋙ F₂') :
    (Functor.pasteSquareIso ι₁ ι₂).hom =
      (TwoSquare.hComp (TwoSquare.mk _ _ _ _ ι₁.hom) (TwoSquare.mk _ _ _ _ ι₂.hom)) := by
  ext K
  simp [TwoSquare.hComp]

end PasteHComp

section OfMatePaste

variable {A B C A' B' C' : Type*} [Category* A] [Category* B] [Category* C] [Category* A']
  [Category* B'] [Category* C'] {TA : A ⥤ A'} {TB : B ⥤ B'} {TC : C ⥤ C'} {RA : A' ⥤ A}
  {RB : B' ⥤ B} {RC : C' ⥤ C} (adjA : TA ⊣ RA) (adjB : TB ⊣ RB) (adjC : TC ⊣ RC)
  {F : A ⥤ C} {G₁ : A ⥤ B} {G₂ : B ⥤ C} {F' : A' ⥤ C'} {G₁' : A' ⥤ B'} {G₂' : B' ⥤ C'}

/-- A transformation `F ⟶ G₁ ⋙ G₂` is compatible with a commutation square of `F` and the pasted
commutation squares of `G₁` and `G₂` if the mates of the commutation squares along
`T ⊣ R` are compatible with it. -/
lemma NatTrans.SquareCompatible.of_mateEquiv_paste (ιF : F ⋙ TC ≅ TA ⋙ F')
    (ι₁ : G₁ ⋙ TB ≅ TA ⋙ G₁') (ι₂ : G₂ ⋙ TC ≅ TB ⋙ G₂') {α : F ⟶ G₁ ⋙ G₂}
    {α' : F' ⟶ G₁' ⋙ G₂'} {τF : RA ⋙ F ⟶ F' ⋙ RC} {τ₁ : RA ⋙ G₁ ⟶ G₁' ⋙ RB}
    {τ₂ : RB ⋙ G₂ ⟶ G₂' ⋙ RC}
    (hF : mateEquiv adjA adjC (TwoSquare.mk _ _ _ _ ιF.hom) = τF)
    (h₁ : mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ ι₁.hom) = τ₁)
    (h₂ : mateEquiv adjB adjC (TwoSquare.mk _ _ _ _ ι₂.hom) = τ₂)
    (h : ∀ K, α.app (RA.obj K) ≫ G₂.map (τ₁.app K) ≫ τ₂.app (G₁'.obj K) =
      τF.app K ≫ RC.map (α'.app K)) :
    SquareCompatible ιF (Functor.pasteSquareIso ι₁ ι₂) α α' := by
  refine of_mateEquiv adjA adjC ?_
  rw [Functor.pasteSquareIso_hom_eq_hComp, mateEquiv_vcomp _ adjB, h₁, h₂, hF]
  ext K
  simpa [TwoSquare.vComp] using h K

end OfMatePaste

end CategoryTheory
