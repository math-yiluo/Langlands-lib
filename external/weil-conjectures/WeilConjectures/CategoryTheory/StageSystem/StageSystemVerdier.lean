/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.StageSystemCommonStageCones
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated

/-! # The Verdier axioms for common-stage triangles

Source: blueprint `sec-proper-base-change/sk-thm-properbasechange`, Verdier axioms
(blueprint: thm-weil-pbc-verdier-axioms).
-/

@[expose] public section
set_option autoImplicit false

universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i, HasShift (C i) ℤ] [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] [∀ i, IsTriangulated (C i)]
  [Preadditive S.PairCategory] [HasZeroObject S.PairCategory]
  [HasShift S.PairCategory ℤ] [∀ n : ℤ, (shiftFunctor S.PairCategory n).Additive]
  [∀ i, (S.ι i).Additive] [∀ i, (S.ι i).CommShift ℤ]
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated]
  [∀ (i j : I) (h : i ≤ j), NatTrans.CommShift (S.transIso h).hom ℤ]

set_option linter.unusedSectionVars false in
section

open CategoryTheory.Category

private theorem commonStage_image_completion {i j : I}
    (τ₁ : Triangle (C i)) (τ₂ : Triangle (C j))
    (h₁ : τ₁ ∈ distTriang (C i)) (h₂ : τ₂ ∈ distTriang (C j))
    (a : (S.ι i).obj τ₁.obj₁ ⟶ (S.ι j).obj τ₂.obj₁)
    (b : (S.ι i).obj τ₁.obj₂ ⟶ (S.ι j).obj τ₂.obj₂)
    (comm : (S.ι i).map τ₁.mor₁ ≫ b = a ≫ (S.ι j).map τ₂.mor₁) :
    ∃ c : (S.ι i).obj τ₁.obj₃ ⟶ (S.ι j).obj τ₂.obj₃,
      (S.ι i).map τ₁.mor₂ ≫ c = b ≫ (S.ι j).map τ₂.mor₂ ∧
      ((S.ι i).map τ₁.mor₃ ≫ ((S.ι i).commShiftIso (1 : ℤ)).hom.app τ₁.obj₁) ≫
          a⟦(1 : ℤ)⟧' =
        c ≫ ((S.ι j).map τ₂.mor₃ ≫ ((S.ι j).commShiftIso (1 : ℤ)).hom.app τ₂.obj₁) := by
  obtain ⟨n, -, hX, hY, hX', hY', u, u', rfl, rfl⟩ :=
    PairCategory.exists_common_stage a b i
  change i ≤ n at hX hX'
  change j ≤ n at hY hY'
  change (S.T hX).obj τ₁.obj₁ ⟶ (S.T hY).obj τ₂.obj₁ at u
  change (S.T hX').obj τ₁.obj₂ ⟶ (S.T hY').obj τ₂.obj₂ at u'
  rw [ι_map_eq (i := i) hX, ι_map_eq (i := j) hY,
    PairCategory.mkHom_comp_mkHom, PairCategory.mkHom_comp_mkHom,
    PairCategory.mkHom_eq_mkHom_iff] at comm
  obtain ⟨q, hq, e⟩ := comm
  rw [← tr_injective, tr_comp, tr_comp, tr_map, tr_map] at e
  have hiq : i ≤ q := hX.trans hq
  have hjq : j ≤ q := hY.trans hq
  let U₁ := (S.T hiq).mapTriangle.obj τ₁
  let U₂ := (S.T hjq).mapTriangle.obj τ₂
  have hd₁ : U₁ ∈ distTriang (C q) := (S.T hiq).map_distinguished _ h₁
  have hd₂ : U₂ ∈ distTriang (C q) := (S.T hjq).map_distinguished _ h₂
  obtain ⟨c, hc₂, hc₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism
    U₁ U₂ hd₁ hd₂ (S.tr hq u) (S.tr hq u') e
  let θ : U₁ ⟶ U₂ :=
    { hom₁ := S.tr hq u
      hom₂ := S.tr hq u'
      hom₃ := c
      comm₁ := e
      comm₂ := hc₂
      comm₃ := hc₃ }
  let e₁ : (S.ι q).mapTriangle.obj U₁ ≅ (S.ι i).mapTriangle.obj τ₁ :=
    (Functor.mapTriangleCompIso (S.T hiq) (S.ι q)).symm.app τ₁ ≪≫
      (Functor.mapTriangleIso (S.transIso hiq)).app τ₁
  let e₂ : (S.ι q).mapTriangle.obj U₂ ≅ (S.ι j).mapTriangle.obj τ₂ :=
    (Functor.mapTriangleCompIso (S.T hjq) (S.ι q)).symm.app τ₂ ≪≫
      (Functor.mapTriangleIso (S.transIso hjq)).app τ₂
  let φ := e₁.inv ≫ (S.ι q).mapTriangle.map θ ≫ e₂.hom
  have ha : φ.hom₁ = PairCategory.mkHom n hX hY u := by
    simp only [φ, comp_hom₁]
    simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, triangleCategory_comp,
      TriangleMorphism.comp_hom₁, Functor.mapTriangleIso_inv_app_hom₁,
      Functor.mapTriangleCompIso_hom_app_hom₁, Functor.mapTriangle_map_hom₁,
      Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapTriangleCompIso_inv_app_hom₁,
      Functor.mapTriangleIso_hom_app_hom₁, Category.assoc, e₁, θ, e₂]
    change (S.transIso hiq).inv.app τ₁.obj₁ ≫ 𝟙 _ ≫
      (S.ι q).map (S.tr hq u) ≫ 𝟙 _ ≫ (S.transIso hjq).hom.app τ₂.obj₁ =
        PairCategory.mkHom (X := ⟨i, τ₁.obj₁⟩) (Y := ⟨j, τ₂.obj₁⟩) n hX hY u
    simp only [id_comp]
    rw [transIso_inv_app, transIso_hom_app,
      ← PairCategory.mkHom_tr (X := ⟨i, τ₁.obj₁⟩) (Y := ⟨j, τ₂.obj₁⟩) hq u]
    exact (mkHom_eq_isoToStage (S := S) _ _ _).symm
  have hb : φ.hom₂ = PairCategory.mkHom n hX' hY' u' := by
    simp only [φ, comp_hom₂]
    simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, triangleCategory_comp,
      TriangleMorphism.comp_hom₂, Functor.mapTriangleIso_inv_app_hom₂,
      Functor.mapTriangleCompIso_hom_app_hom₂, Functor.mapTriangle_map_hom₂,
      Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapTriangleCompIso_inv_app_hom₂,
      Functor.mapTriangleIso_hom_app_hom₂, Category.assoc, e₁, θ, e₂]
    change (S.transIso hiq).inv.app τ₁.obj₂ ≫ 𝟙 _ ≫
      (S.ι q).map (S.tr hq u') ≫ 𝟙 _ ≫ (S.transIso hjq).hom.app τ₂.obj₂ =
        PairCategory.mkHom (X := ⟨i, τ₁.obj₂⟩) (Y := ⟨j, τ₂.obj₂⟩) n hX' hY' u'
    simp only [id_comp]
    rw [transIso_inv_app, transIso_hom_app,
      ← PairCategory.mkHom_tr (X := ⟨i, τ₁.obj₂⟩) (Y := ⟨j, τ₂.obj₂⟩) hq u']
    exact (mkHom_eq_isoToStage (S := S) _ _ _).symm
  refine ⟨φ.hom₃, ?_, ?_⟩
  · have hh := φ.comm₂
    change (S.ι i).map τ₁.mor₂ ≫ φ.hom₃ = φ.hom₂ ≫ (S.ι j).map τ₂.mor₂ at hh
    rw [hb] at hh
    exact hh
  · have hh := φ.comm₃
    change ((S.ι i).map τ₁.mor₃ ≫ _) ≫ (shiftFunctor _ (1 : ℤ)).map φ.hom₁ =
      φ.hom₃ ≫ ((S.ι j).map τ₂.mor₃ ≫ _) at hh
    rw [ha] at hh
    exact hh

/-- A commuting square between the first arrows of common-stage distinguished
triangles extends to a triangle morphism.
Source: the common-stage TR3 argument in the docstring of
`commonStage_verdier_existsUnique` and
`WeilConjectures/CategoryTheory/StageSystem/Pretriangulated.lean`, `exists_hom₃_ι`.
Proof: replace both triangles by isomorphic stage images. Represent the two
vertical maps at a common stage and extend again until the first square commutes,
using `mkHom_eq_mkHom_iff`. Apply the triangle morphism axiom to the images of the
stage triangles under the exact transitions. Map the third component into the
pair category and conjugate by the stage identifications. The second square
follows from functoriality. For the last square use that the identifications
`transIso` commute with shifts, so their induced maps of triangles commute with
the third arrows. Conjugate back along the initial triangle isomorphisms.
This uses coherence only for the identifications in the pair category and does
not require the associators to commute with shifts before applying the inclusions. -/
private theorem commonStage_complete_triangle_morphism
    (T₁ T₂ : Triangle S.PairCategory)
    (h₁ : S.CommonStageDistinguished T₁) (h₂ : S.CommonStageDistinguished T₂)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨i, τ₁, hτ₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨j, τ₂, hτ₂, ⟨e₂⟩⟩ := h₂
  exact Idempotents.Karoubi.exists_hom₃_of_retract (Retract.ofIso e₁) (Retract.ofIso e₂)
    (fun a b comm ↦ commonStage_image_completion S τ₁ τ₂ hτ₁ hτ₂ a b comm) a b comm

private theorem commonStage_nonempty_octahedron_rfl
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : D} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃}
    {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃) {v₁₂ : X₂ ⟶ Z₁₂}
    {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang D}
    {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧}
    {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang D}
    {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧}
    {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang D}
    (H : Triangulated.Octahedron comm h₁₂ h₂₃ h₁₃)
    (h₁₃' : Triangle.mk (u₁₂ ≫ u₂₃) v₁₃ w₁₃ ∈ distTriang D) :
    Nonempty (Triangulated.Octahedron rfl h₁₂ h₂₃ h₁₃') := by
  subst comm
  exact ⟨H⟩

private theorem commonStage_iso_closed (T₁ T₂ : Triangle S.PairCategory)
    (h₁ : S.CommonStageDistinguished T₁) (e : T₂ ≅ T₁) :
    S.CommonStageDistinguished T₂ := by
  obtain ⟨i, U, hU, ⟨e'⟩⟩ := h₁
  exact ⟨i, U, hU, ⟨e ≪≫ e'⟩⟩

private theorem commonStage_contractible (X : S.PairCategory) :
    S.CommonStageDistinguished (contractibleTriangle X) := by
  have hz := (S.ι X.stage).map_isZero (isZero_zero (C X.stage))
  refine ⟨X.stage, contractibleTriangle X.obj,
    Pretriangulated.contractible_distinguished _,
    ⟨Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((isZero_zero _).iso hz) ?_ ?_ ?_⟩⟩
  · change 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ (S.ι X.stage).map (𝟙 X.obj)
    rw [Functor.map_id]
    rfl
  · exact hz.eq_of_tgt _ _
  · exact (isZero_zero _).eq_of_src _ _

private theorem commonStage_cocone {X Y : S.PairCategory} (f : X ⟶ Y) :
    ∃ (Z : S.PairCategory) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      S.CommonStageDistinguished (Triangle.mk f g h) := by
  obtain ⟨n, -, hX, hY, u, rfl⟩ := PairCategory.exists_le_mkHom_eq f X.stage
  obtain ⟨Z, v, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle u
  refine ⟨(S.ι n).obj Z, (S.isoToStage Y hY).hom ≫ (S.ι n).map v,
    (S.ι n).map w ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app _ ≫
      (shiftFunctor S.PairCategory (1 : ℤ)).map (S.isoToStage X hX).inv,
    n, Triangle.mk u v w, hT, ⟨?_⟩⟩
  exact Triangle.isoMk _ _ (S.isoToStage X hX) (S.isoToStage Y hY) (Iso.refl _)
    (by simp [Functor.mapTriangle, mkHom_eq_isoToStage])
    (by simp [Functor.mapTriangle]) (by simp [Functor.mapTriangle])

private theorem commonStage_rotate (T : Triangle S.PairCategory) :
    S.CommonStageDistinguished T ↔ S.CommonStageDistinguished T.rotate := by
  constructor
  · rintro ⟨i, U, hU, ⟨e⟩⟩
    exact ⟨i, U.rotate, rot_of_distTriang _ hU,
      ⟨(rotate _).mapIso e ≪≫ (S.ι i).mapTriangleRotateIso.app U⟩⟩
  · rintro ⟨i, U, hU, ⟨e⟩⟩
    exact ⟨i, U.invRotate, inv_rot_of_distTriang _ hU,
      ⟨(rotCompInvRot (C := S.PairCategory)).app T ≪≫ (invRotate _).mapIso e ≪≫
        (S.ι i).mapTriangleInvRotateIso.app U⟩⟩

private theorem pretriangulated_eq_of_distinguished
    (t₁ t₂ : Pretriangulated S.PairCategory)
    (h : t₁.distinguishedTriangles = t₂.distinguishedTriangles) : t₁ = t₂ := by
  cases t₁
  cases t₂
  dsimp only at h
  cases h
  rfl

end

set_option linter.unusedVariables false in
/-- Common-stage triangles satisfy TR1--TR4; stage inclusions and transition
identifications are exact. The distinguished set uniquely fixes the pretriangulation.
Source: blueprint Verdier axioms (blueprint: thm-weil-pbc-verdier-axioms).
Proof: move every finite collection of objects and arrows to a common stage using
StageSystem.PairCategory.exists_common_stage. Equalities hold after one further
extension by mkHom_eq_mkHom_iff. At that stage choose cone and identity triangles;
apply signed rotation and the completion of a commutative square. Exact transitions
and the coherent shift comparisons preserve these operations. Isomorphism closure
is in the definition. This proves TR1--TR3. Move the composable arrows and their
three cone triangles to one stage, enlarge to descend all commuting equations,
and apply its octahedral axiom. Its image gives TR4. The image of every stage
triangle is distinguished by definition; transIso commutes with shifts by the
specified stage coherence, so these are exact natural isomorphisms. Finally a
Pretriangulated structure has only its distinguished set as non-propositional data,
so the displayed criterion proves uniqueness. -/
theorem commonStage_verdier_existsUnique :
    ∃! t : Pretriangulated S.PairCategory,
      (fun [triInst : Pretriangulated S.PairCategory] ↦
        (∀ T : Triangle S.PairCategory,
          T ∈ distTriang S.PairCategory ↔ S.CommonStageDistinguished T) ∧
        IsTriangulated S.PairCategory ∧ ∀ i : I, (S.ι i).IsTriangulated)
        (triInst := t) := by
  let t : Pretriangulated S.PairCategory :=
    { distinguishedTriangles := S.CommonStageDistinguished
      isomorphic_distinguished := fun T₁ h₁ T₂ e ↦ commonStage_iso_closed S T₁ T₂ h₁ e
      contractible_distinguished := commonStage_contractible S
      distinguished_cocone_triangle := commonStage_cocone S
      rotate_distinguished_triangle := commonStage_rotate S
      complete_distinguished_triangle_morphism := commonStage_complete_triangle_morphism S }
  have hi (i : I) : (S.ι i).IsTriangulated :=
    ⟨fun U hU ↦ ⟨i, U, hU, ⟨Iso.refl _⟩⟩⟩
  have ht : IsTriangulated S.PairCategory :=
    IsTriangulated.mk' fun X₁ X₂ X₃ u₁₂ u₂₃ ↦ by
      obtain ⟨n, -, hX₁, hX₂, hX₂', hX₃, a, b, rfl, rfl⟩ :=
        PairCategory.exists_common_stage u₁₂ u₂₃ X₁.stage
      obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := Pretriangulated.distinguished_cocone_triangle a
      obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := Pretriangulated.distinguished_cocone_triangle b
      obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := Pretriangulated.distinguished_cocone_triangle (a ≫ b)
      have H := (Triangulated.someOctahedron rfl h₁₂ h₂₃ h₁₃).map (S.ι n)
      have h₁₃' : Triangle.mk ((S.ι n).map a ≫ (S.ι n).map b) ((S.ι n).map v₁₃)
          ((S.ι n).map w₁₃ ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app _) ∈
            distTriang S.PairCategory := by
        have hd : Triangle.mk ((S.ι n).map (a ≫ b)) ((S.ι n).map v₁₃)
            ((S.ι n).map w₁₃ ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app _) ∈
              distTriang S.PairCategory := (S.ι n).map_distinguished _ h₁₃
        rw [Functor.map_comp] at hd
        exact hd
      have ho : Nonempty (Triangulated.Octahedron rfl
          ((S.ι n).map_distinguished _ h₁₂) ((S.ι n).map_distinguished _ h₂₃) h₁₃') := by
        exact commonStage_nonempty_octahedron_rfl _ H h₁₃'
      exact ⟨_, _, _, _, _, _, (S.ι n).map a, (S.ι n).map b,
        S.isoToStage X₁ hX₁, S.isoToStage X₂ hX₂, S.isoToStage X₃ hX₃,
        by simp [mkHom_eq_isoToStage],
        by simp [mkHom_eq_isoToStage],
        _, _, (S.ι n).map_distinguished _ h₁₂, _, _, (S.ι n).map_distinguished _ h₂₃,
        _, _, h₁₃', ho⟩
  refine ⟨t, ⟨fun _ ↦ Iff.rfl, ht, hi⟩, ?_⟩
  intro t' ht'
  apply pretriangulated_eq_of_distinguished S t' t
  exact Set.ext (fun T ↦ ht'.1 T)

end CategoryTheory.StageSystem
