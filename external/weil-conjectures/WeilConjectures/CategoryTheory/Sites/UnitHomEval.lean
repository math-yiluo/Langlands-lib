/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections

/-!
# Morphisms out of the unit of abelian sheaves and sections over a terminal object

Let `J` be a Grothendieck topology on a category `C` with a terminal object `T`, and equip the
abelian sheaves on `C` with the monoidal structure `CategoryTheory.Sheaf.monoidalCategory`, whose
unit is the sheafification of the constant presheaf `ℤ`. A morphism `s : 𝟙_ ⟶ F` is determined by
the section `s(1) ∈ F(T)` (`CategoryTheory.Sheaf.unitHomEval`,
`CategoryTheory.Sheaf.unitHomEval_injective`): the composite `ℤ ⟶ 𝟙_ ⟶ F` of presheaves is
determined by the image of `1` over the terminal object, and `ℤ ⟶ 𝟙_` is the unit of the
sheafification adjunction.

For a sheaf of rings `S` and a natural family of ring homomorphisms `φ X : R →+* S(X)`, the global
section `CategoryTheory.Sheaf.ringHomΓSheafCompose J S φ hφ r` evaluates to `φ T r`
(`CategoryTheory.Sheaf.unitHomEval_ringHomΓSheafCompose`). Consequently, if `φ T` is bijective,
then so is `R →+* Γ S` (`CategoryTheory.Sheaf.ringHomΓSheafCompose_bijective`): the global sections
of the ring object underlying `S` are the sections of `S` over `T`.
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory MonoidalCategory MonObj Opposite Limits Functor.LaxMonoidal

namespace CategoryTheory.Sheaf

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J Ab.{w}]
  [(J.W (A := Ab.{w})).IsMonoidal] {T : C}

/-- A morphism of abelian presheaves out of the monoidal unit (the constant presheaf `ℤ`) is
determined by the image of `1` over a terminal object. -/
lemma natTrans_ext_of_isTerminal (hT : IsTerminal T) {P : Cᵒᵖ ⥤ Ab.{w}}
    {t s : 𝟙_ (Cᵒᵖ ⥤ Ab.{w}) ⟶ P}
    (h : t.app (op T) (ULift.up 1) = s.app (op T) (ULift.up 1)) : t = s := by
  have key (t : 𝟙_ (Cᵒᵖ ⥤ Ab.{w}) ⟶ P) (X : Cᵒᵖ) (n : ULift.{w} ℤ) :
      t.app X n = n.down • P.map (hT.from X.unop).op (t.app (op T) (ULift.up 1)) := by
    have hn : n = n.down • (ULift.up 1 : ULift.{w} ℤ) := by
      ext
      simp
    conv_lhs => rw [hn, map_zsmul]
    rw [← NatTrans.naturality_apply]
    rfl
  ext X n
  rw [key t, key s, h]

variable (T) in
/-- The value at the unit section over `T` of a morphism `s : 𝟙_ ⟶ F` of abelian sheaves: the
image of `1 ∈ ℤ` under the composite `ℤ ⟶ 𝟙_ ⟶ F` of presheaves, evaluated at `T`. -/
noncomputable def unitHomEval {F : Sheaf J Ab.{w}} (s : 𝟙_ (Sheaf J Ab.{w}) ⟶ F) :
    F.obj.obj (op T) :=
  (ε (sheafToPresheaf J Ab.{w}) ≫ s.hom).app (op T) (ULift.up 1)

variable (T) in
lemma unitHomEval_comp {F G : Sheaf J Ab.{w}} (s : 𝟙_ (Sheaf J Ab.{w}) ⟶ F) (f : F ⟶ G) :
    unitHomEval T (s ≫ f) = f.hom.app (op T) (unitHomEval T s) :=
  rfl

/-- The value at the unit section over any object `V` of a morphism `s : 𝟙_ ⟶ F` is the
restriction of its value over a terminal object. -/
lemma ε_comp_hom_app_eq (hT : IsTerminal T) {F : Sheaf J Ab.{w}} (s : 𝟙_ (Sheaf J Ab.{w}) ⟶ F)
    (V : C) :
    (ε (sheafToPresheaf J Ab.{w}) ≫ s.hom).app (op V) (ULift.up 1) =
      F.obj.map (hT.from V).op (unitHomEval T s) := by
  rw [unitHomEval, ← NatTrans.naturality_apply]
  rfl

/-- A morphism out of the unit of abelian sheaves is determined by its value at the unit
section over a terminal object. -/
lemma unitHomEval_injective (hT : IsTerminal T) (F : Sheaf J Ab.{w}) :
    Function.Injective (unitHomEval (J := J) T (F := F)) := by
  intro s t h
  have e (c : 𝟙_ (Sheaf J Ab.{w}) ⟶ F) :
      ((sheafificationAdjunction J Ab.{w}).homEquiv _ _).symm
        (ε (sheafToPresheaf J Ab.{w}) ≫ (sheafToPresheaf J Ab.{w}).map c) =
        Functor.OplaxMonoidal.η (presheafToSheaf J Ab.{w}) ≫ c := by
    rw [Adjunction.homEquiv_naturality_right_symm]
    congr 1
    exact Equiv.symm_apply_apply _ _
  have h' : ε (sheafToPresheaf J Ab.{w}) ≫ (sheafToPresheaf J Ab.{w}).map s =
      ε (sheafToPresheaf J Ab.{w}) ≫ (sheafToPresheaf J Ab.{w}).map t :=
    natTrans_ext_of_isTerminal hT h
  have h'' := congrArg ((sheafificationAdjunction J Ab.{w}).homEquiv _ _).symm h'
  rw [e, e] at h''
  exact (cancel_epi _).1 h''

variable [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})] (S : Sheaf J RingCat.{w})
  {R : Type*} [Ring R]

variable (T) in
/-- The global section `ringHomΓSheafCompose J S φ hφ r` takes the value `φ T r` at the unit
section over `T`. -/
lemma unitHomEval_ringHomΓSheafCompose (φ : ∀ X, R →+* S.obj.obj X)
    (hφ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R), S.obj.map f (φ X r) = φ Y r) (r : R) :
    unitHomEval T (ringHomΓSheafCompose J S φ hφ r).hom = φ (op T) r := by
  have h := congrArg (fun f : 𝟙_ (Cᵒᵖ ⥤ Ab.{w}) ⟶ S.obj ⋙ forget₂ RingCat.{w} Ab.{w} ↦
    f.app (op T) (ULift.up 1)) (ε_comp_ringHomΓSheafCompose_hom J S φ hφ r)
  refine h.trans ?_
  change ((1 : ℤ) : S.obj.obj (op T)) * φ (op T) r = φ (op T) r
  rw [Int.cast_one, _root_.one_mul]

/-- If `φ T : R →+* S(T)` is bijective for a terminal object `T`, then the ring homomorphism
`R →+* Γ S` given by the natural family `φ` is bijective. -/
lemma ringHomΓSheafCompose_bijective (hT : IsTerminal T) (φ : ∀ X, R →+* S.obj.obj X)
    (hφ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R), S.obj.map f (φ X r) = φ Y r)
    (hφT : Function.Bijective (φ (op T))) :
    Function.Bijective (ringHomΓSheafCompose J S φ hφ) := by
  refine ⟨fun r r' h ↦ hφT.1 ?_, fun s ↦ ?_⟩
  · rw [← unitHomEval_ringHomΓSheafCompose T S φ hφ, ← unitHomEval_ringHomΓSheafCompose T S φ hφ,
      h]
  · obtain ⟨r, hr⟩ := hφT.2 (unitHomEval T s.hom)
    refine ⟨r, Γ.ext ?_⟩
    exact unitHomEval_injective hT _ (by rw [unitHomEval_ringHomΓSheafCompose, hr])

section Pushforward

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D} [HasSheafify K Ab.{w}]
  [(K.W (A := Ab.{w})).IsMonoidal] (F : C ⥤ D) [F.IsContinuous J K] {T' : D}

omit [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})] in
/-- The value at the unit section over `T` of the image `ε ≫ F_* k` of a global section
`k : 𝟙_ ⟶ G` under the lax monoidal pushforward `F_*` is the restriction to `F T` of the value
of `k` at the unit section over a terminal object `T'`. -/
lemma unitHomEval_ε_comp_sheafPushforwardContinuous_map (hT' : IsTerminal T') {G : Sheaf K Ab.{w}}
    (k : 𝟙_ (Sheaf K Ab.{w}) ⟶ G) :
    unitHomEval T (ε (F.sheafPushforwardContinuous Ab.{w} J K) ≫
        (F.sheafPushforwardContinuous Ab.{w} J K).map k) =
      G.obj.map (hT'.from (F.obj T)).op (unitHomEval T' k) := by
  rw [← ε_comp_hom_app_eq hT' k (F.obj T)]
  change ((ε (sheafToPresheaf J Ab.{w})).app (op T) ≫
    (ε (F.sheafPushforwardContinuous Ab.{w} J K)).hom.app (op T) ≫ k.hom.app (op (F.obj T)))
      (ULift.up 1) = ((ε (sheafToPresheaf K Ab.{w})).app (op (F.obj T)) ≫
        k.hom.app (op (F.obj T))) (ULift.up 1)
  rw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  rfl

end Pushforward

end CategoryTheory.Sheaf
