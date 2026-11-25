/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import WeilConjectures.CategoryTheory.StageSystem.Shift
public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated

/-!
# The pair category of a system of pretriangulated categories

Let `S` be a stage system of pretriangulated categories `C i` whose transition functors are
triangulated (they commute with the shift and preserve distinguished triangles) and whose
associators are compatible with the shifts. The pair category `S.PairCategory` carries the shift
of `CategoryTheory.StageSystem.PairCategory.hasShift`, and a triangle of `S.PairCategory` is
*distinguished* if it is isomorphic to the image under a stage inclusion `ι i` of a distinguished
triangle of the stage `i`.

These data make the pair category pretriangulated; the stage inclusions `ι i` are triangulated
functors and the identifications `T_{j/i} ⋙ ι j ≅ ι i` commute with the shifts. The proofs of the
axioms reduce, by transport to a common stage, to the corresponding axioms at a finite stage.

The *common-stage cone triangle* `CategoryTheory.StageSystem.PairCategory.coneTriangle` of a
representative `u` at a stage `n` of a morphism `f` and of a distinguished triangle on `u` is
distinguished, and the cone triangles of two representatives of the same morphism are isomorphic
by an isomorphism whose first two components are identities.

## Main definitions

- `CategoryTheory.StageSystem.PairCategory.distinguishedTriangles`.
- `CategoryTheory.StageSystem.PairCategory.pretriangulated`.
- `CategoryTheory.StageSystem.PairCategory.coneTriangle`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject

namespace StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i, HasShift (C i) ℤ] [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] {S : StageSystem C}
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ] [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated]
  [∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ]

namespace PairCategory

instance (n : ℤ) : (shiftFunctor S.PairCategory n).Additive :=
  inferInstanceAs (S.shiftMorphism ℤ n).functor.Additive

instance [Nonempty I] : HasZeroObject S.PairCategory := hasZeroObject

variable (S) in
/-- The distinguished triangles of the pair category: the triangles which are isomorphic to the
image under a stage inclusion `ι i` of a distinguished triangle of the stage `i`. -/
def distinguishedTriangles : Set (Triangle S.PairCategory) :=
  fun T ↦ ∃ (i : I) (τ : Triangle (C i)), τ ∈ distTriang (C i) ∧
    Nonempty (T ≅ (S.ι i).mapTriangle.obj τ)

omit [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated] in
lemma isomorphic_distinguished (T₁ : Triangle S.PairCategory)
    (h₁ : T₁ ∈ distinguishedTriangles S) (T₂ : Triangle S.PairCategory) (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles S := by
  obtain ⟨i, τ, hτ, ⟨e'⟩⟩ := h₁
  exact ⟨i, τ, hτ, ⟨e ≪≫ e'⟩⟩

omit [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated] in
lemma mapTriangle_mem_distinguishedTriangles {i : I} (τ : Triangle (C i))
    (hτ : τ ∈ distTriang (C i)) : (S.ι i).mapTriangle.obj τ ∈ distinguishedTriangles S :=
  ⟨i, τ, hτ, ⟨Iso.refl _⟩⟩

/-- A triangle whose first morphism is isomorphic to the first morphism of a triangle `τ` can be
completed to a triangle isomorphic to `τ`. -/
def triangleOfArrowIso {D : Type*} [Category* D] [HasShift D ℤ] (τ : Triangle D) {X Y : D}
    (f : X ⟶ Y) (e₁ : τ.obj₁ ≅ X) (e₂ : τ.obj₂ ≅ Y) (comm : τ.mor₁ ≫ e₂.hom = e₁.hom ≫ f) :
    τ ≅ Triangle.mk f (e₂.inv ≫ τ.mor₂) (τ.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') :=
  Triangle.isoMk _ _ e₁ e₂ (Iso.refl _) comm (by simp) (by simp)

lemma contractible_distinguished [Nonempty I] (X : S.PairCategory) :
    contractibleTriangle X ∈ distinguishedTriangles S := by
  refine ⟨X.stage, contractibleTriangle X.obj, Pretriangulated.contractible_distinguished _,
    ⟨Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((isZero_zero _).iso (isZero_ι_obj (isZero_zero _))) ?_ ?_ ?_⟩⟩
  · exact ((comp_id _).trans ((S.ι X.stage).map_id X.obj).symm).trans (id_comp _).symm
  · exact (isZero_ι_obj (isZero_zero _)).eq_of_tgt _ _
  · exact (isZero_zero _).eq_of_src _ _

variable (S) in
/-- The *common-stage cone triangle*: for a morphism of the pair category represented by
`u : T x ⟶ T y` at a stage `n` and a triangle `u, v, w` of the stage `n`, the triangle
`X ⟶ Y ⟶ (n, Z) ⟶ X⟦1⟧` of the pair category with first arrow represented by `u`, second arrow
represented by `v` and third arrow represented by `w` followed by the shift comparison. -/
noncomputable def coneTriangle {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n)
    (hY : Y.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY) {Z : C n} (v : Y.toStage hY ⟶ Z)
    (w : Z ⟶ (X.toStage hX)⟦(1 : ℤ)⟧) : Triangle S.PairCategory :=
  Triangle.mk (mkHom n hX hY u) ((S.isoToStage Y hY).hom ≫ (S.ι n).map v)
    (((S.ι n).map w ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app (X.toStage hX)) ≫
      (S.isoToStage X hX).inv⟦(1 : ℤ)⟧')

omit [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated] in
/-- The common-stage cone triangle of a distinguished triangle of a stage is distinguished. -/
lemma coneTriangle_mem_distinguishedTriangles {X Y : S.PairCategory} {n : I}
    (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY) {Z : C n}
    (v : Y.toStage hY ⟶ Z) (w : Z ⟶ (X.toStage hX)⟦(1 : ℤ)⟧)
    (h : Triangle.mk u v w ∈ distTriang (C n)) :
    coneTriangle S hX hY u v w ∈ distinguishedTriangles S := by
  have comm : (S.ι n).map u ≫ (S.isoToStage Y hY).inv =
      (S.isoToStage X hX).inv ≫ mkHom n hX hY u := by
    simp [mkHom_eq_isoToStage]
  exact ⟨n, _, h, ⟨(triangleOfArrowIso ((S.ι n).mapTriangle.obj (Triangle.mk u v w))
    (mkHom n hX hY u) (S.isoToStage X hX).symm (S.isoToStage Y hY).symm comm).symm⟩⟩

omit [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated] in
lemma distinguished_cocone_triangle {X Y : S.PairCategory} (f : X ⟶ Y) :
    ∃ (Z : S.PairCategory) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles S := by
  obtain ⟨n, -, hX, hY, u, rfl⟩ := exists_le_mkHom_eq f X.stage
  obtain ⟨Z, v, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle u
  exact ⟨_, _, _, coneTriangle_mem_distinguishedTriangles hX hY u v w hT⟩

lemma rotate_distinguished_triangle (T : Triangle S.PairCategory) :
    T ∈ distinguishedTriangles S ↔ T.rotate ∈ distinguishedTriangles S := by
  constructor
  · rintro ⟨i, τ, hτ, ⟨e⟩⟩
    exact ⟨i, τ.rotate, rot_of_distTriang _ hτ,
      ⟨(rotate _).mapIso e ≪≫ (S.ι i).mapTriangleRotateIso.app τ⟩⟩
  · rintro ⟨i, τ, hτ, ⟨e⟩⟩
    exact ⟨i, τ.invRotate, inv_rot_of_distTriang _ hτ,
      ⟨(rotCompInvRot (C := S.PairCategory)).app T ≪≫ (invRotate _).mapIso e ≪≫
        (S.ι i).mapTriangleInvRotateIso.app τ⟩⟩

/-- The morphism axiom for images of distinguished triangles of two stages: after transport to a
common stage where the given square commutes, it follows from the morphism axiom there. -/
lemma exists_hom₃_ι {i j : I} (τ₁ : Triangle (C i)) (τ₂ : Triangle (C j))
    (h₁ : τ₁ ∈ distTriang (C i)) (h₂ : τ₂ ∈ distTriang (C j))
    (a : (S.ι i).obj τ₁.obj₁ ⟶ (S.ι j).obj τ₂.obj₁) (b : (S.ι i).obj τ₁.obj₂ ⟶ (S.ι j).obj τ₂.obj₂)
    (comm : (S.ι i).map τ₁.mor₁ ≫ b = a ≫ (S.ι j).map τ₂.mor₁) :
    ∃ c : (S.ι i).obj τ₁.obj₃ ⟶ (S.ι j).obj τ₂.obj₃,
      (S.ι i).map τ₁.mor₂ ≫ c = b ≫ (S.ι j).map τ₂.mor₂ ∧
      ((S.ι i).map τ₁.mor₃ ≫ ((S.ι i).commShiftIso (1 : ℤ)).hom.app τ₁.obj₁) ≫ a⟦(1 : ℤ)⟧' =
        c ≫ ((S.ι j).map τ₂.mor₃ ≫ ((S.ι j).commShiftIso (1 : ℤ)).hom.app τ₂.obj₁) := by
  obtain ⟨m, hi, hj⟩ := exists_ge_ge i j
  obtain ⟨n, -, hX, hY, hX', hY', u, u', rfl, rfl⟩ := exists_common_stage (X := ⟨i, τ₁.obj₁⟩)
    (Y := ⟨j, τ₂.obj₁⟩) (X' := ⟨i, τ₁.obj₂⟩) (Y' := ⟨j, τ₂.obj₂⟩) a b m
  rw [ι_map_eq (i := i) hX, ι_map_eq (i := j) hY, mkHom_comp_mkHom, mkHom_comp_mkHom,
    mkHom_eq_mkHom_iff] at comm
  obtain ⟨q, hq, e⟩ := comm
  rw [← tr_injective, tr_comp, tr_comp, tr_map, tr_map] at e
  have hiq : i ≤ q := hX.trans hq
  have hjq : j ≤ q := hY.trans hq
  have hd₁ : Triangle.mk ((S.T hiq).map τ₁.mor₁) ((S.T hiq).map τ₁.mor₂)
      ((S.T hiq).map τ₁.mor₃ ≫ ((S.T hiq).commShiftIso (1 : ℤ)).hom.app τ₁.obj₁) ∈
        distTriang (C q) := (S.T hiq).map_distinguished _ h₁
  have hd₂ : Triangle.mk ((S.T hjq).map τ₂.mor₁) ((S.T hjq).map τ₂.mor₂)
      ((S.T hjq).map τ₂.mor₃ ≫ ((S.T hjq).commShiftIso (1 : ℤ)).hom.app τ₂.obj₁) ∈
        distTriang (C q) := (S.T hjq).map_distinguished _ h₂
  obtain ⟨c, hc₂, hc₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism _ _ hd₁ hd₂
    (S.tr hq u) (S.tr hq u') e
  refine ⟨mkHom q (hX.trans hq) (hY.trans hq) c, ?_, ?_⟩
  · rw [← mkHom_tr hq u', ι_map_eq (i := i) (hX.trans hq), ι_map_eq (i := j) (hY.trans hq),
      mkHom_comp_mkHom, mkHom_comp_mkHom]
    exact congr_arg _ hc₂
  · rw [ι_commShiftIso_hom_app, ι_commShiftIso_hom_app]
    erw [comp_id, comp_id]
    rw [← mkHom_tr hq u, shiftFunctor_map_mkHom, ι_map_eq (i := i) (hX.trans hq),
      ι_map_eq (i := j) (hY.trans hq)]
    erw [mkHom_comp_mkHom, mkHom_comp_mkHom]
    congr 1
    have hc₃' : (S.T hiq).map τ₁.mor₃ ≫ ((S.T hiq).commShiftIso (1 : ℤ)).hom.app τ₁.obj₁ ≫
        (S.tr hq u)⟦(1 : ℤ)⟧' =
          c ≫ (S.T hjq).map τ₂.mor₃ ≫ ((S.T hjq).commShiftIso (1 : ℤ)).hom.app τ₂.obj₁ := by
      rw [← Category.assoc]
      exact hc₃
    have := hc₃' =≫ ((S.T hjq).commShiftIso (1 : ℤ)).inv.app τ₂.obj₁
    simp only [Category.assoc, Iso.hom_inv_id_app] at this
    exact this.trans (congr_arg (c ≫ ·) (comp_id _))

lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle S.PairCategory)
    (h₁ : T₁ ∈ distinguishedTriangles S) (h₂ : T₂ ∈ distinguishedTriangles S)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨i, τ₁, hτ₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨j, τ₂, hτ₂, ⟨e₂⟩⟩ := h₂
  exact Idempotents.Karoubi.exists_hom₃_of_retract (Retract.ofIso e₁) (Retract.ofIso e₂)
    (fun a b comm ↦ exists_hom₃_ι τ₁ τ₂ hτ₁ hτ₂ a b comm) a b comm

variable [Nonempty I]

/-- The axioms TR1–TR3: the pair category of a stage system of pretriangulated categories with
triangulated transition functors is pretriangulated, for the shift of
`CategoryTheory.StageSystem.PairCategory.hasShift` and the triangles isomorphic to images of
distinguished triangles of a single stage. -/
noncomputable instance pretriangulated : Pretriangulated S.PairCategory where
  distinguishedTriangles := distinguishedTriangles S
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

lemma mem_distTriang_iff (T : Triangle S.PairCategory) :
    T ∈ distTriang S.PairCategory ↔ ∃ (i : I) (τ : Triangle (C i)), τ ∈ distTriang (C i) ∧
      Nonempty (T ≅ (S.ι i).mapTriangle.obj τ) := Iff.rfl

omit [IsDirectedOrder I] [Nonempty I]
  [∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ] in
/-- The transport along `n ≤ p` of a distinguished triangle on a representative `u` at the stage
`n` is a distinguished triangle on the transported representative `u_p` (scalar extension of
cone triangles). -/
lemma tr_triangle_mem_distTriang {X Y : S.PairCategory} {n p : I} (hX : X.stage ≤ n)
    (hY : Y.stage ≤ n) (h : n ≤ p) (u : X.toStage hX ⟶ Y.toStage hY) {Z : C n}
    (v : Y.toStage hY ⟶ Z) (w : Z ⟶ (X.toStage hX)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v w ∈ distTriang (C n)) :
    Triangle.mk (S.tr h u) ((S.assoc hY h).inv.app Y.obj ≫ (S.T h).map v)
      ((S.T h).map w ≫ ((S.T h).commShiftIso (1 : ℤ)).hom.app (X.toStage hX) ≫
        ((S.assoc hX h).hom.app X.obj)⟦(1 : ℤ)⟧') ∈ distTriang (C p) := by
  have hd : Triangle.mk ((S.T h).map u) ((S.T h).map v)
      ((S.T h).map w ≫ ((S.T h).commShiftIso (1 : ℤ)).hom.app (X.toStage hX)) ∈
        distTriang (C p) := (S.T h).map_distinguished _ hT
  refine Pretriangulated.isomorphic_distinguished _ hd _
    (Triangle.isoMk _ _ ((S.assoc hX h).app X.obj).symm ((S.assoc hY h).app Y.obj).symm
      (Iso.refl _) ?_ ?_ ?_)
  · simp [tr]
  · simp
  · simp [← Functor.map_comp]

/-- Compatibility and independence of common-stage cones. Let `T` be a triangle of the pair category
whose first morphism is represented by `u` at a stage `n`, and let `u, v, w` be a distinguished
triangle of the stage `n`. Then `T` is distinguished if and only if it is isomorphic to the
common-stage cone triangle of `u, v, w` by an isomorphism whose first two components are identities.
In particular distinguishedness does not depend on the representative, the stage or the cone chosen.
-/
theorem mem_distTriang_iff_exists_iso_coneTriangle (T : Triangle S.PairCategory) {n : I}
    (hX : T.obj₁.stage ≤ n) (hY : T.obj₂.stage ≤ n) (u : T.obj₁.toStage hX ⟶ T.obj₂.toStage hY)
    (hu : T.mor₁ = mkHom n hX hY u) {Z : C n} (v : T.obj₂.toStage hY ⟶ Z)
    (w : Z ⟶ (T.obj₁.toStage hX)⟦(1 : ℤ)⟧) (hT : Triangle.mk u v w ∈ distTriang (C n)) :
    T ∈ distTriang S.PairCategory ↔ ∃ e : T ≅ coneTriangle S hX hY u v w,
      e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ := by
  constructor
  · intro h
    obtain ⟨e, h₁, h₂⟩ := exists_iso_of_arrow_iso _ _ h
      (coneTriangle_mem_distinguishedTriangles hX hY u v w hT)
      (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by simp [coneTriangle, hu]))
    exact ⟨e, h₁, h₂⟩
  · rintro ⟨e, -, -⟩
    exact isomorphic_distinguished _ (coneTriangle_mem_distinguishedTriangles hX hY u v w hT) _ e

/-- Two common-stage cone triangles of representatives of the same morphism are isomorphic by an
isomorphism whose first two components are identities. -/
lemma exists_iso_coneTriangle {X Y : S.PairCategory} {n n' : I} {hX : X.stage ≤ n}
    {hY : Y.stage ≤ n} {hX' : X.stage ≤ n'} {hY' : Y.stage ≤ n'}
    (u : X.toStage hX ⟶ Y.toStage hY) (u' : X.toStage hX' ⟶ Y.toStage hY')
    (hu : mkHom n hX hY u = mkHom n' hX' hY' u') {Z : C n} (v : Y.toStage hY ⟶ Z)
    (w : Z ⟶ (X.toStage hX)⟦(1 : ℤ)⟧) (hT : Triangle.mk u v w ∈ distTriang (C n)) {Z' : C n'}
    (v' : Y.toStage hY' ⟶ Z') (w' : Z' ⟶ (X.toStage hX')⟦(1 : ℤ)⟧)
    (hT' : Triangle.mk u' v' w' ∈ distTriang (C n')) :
    ∃ e : coneTriangle S hX hY u v w ≅ coneTriangle S hX' hY' u' v' w',
      e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ :=
  (mem_distTriang_iff_exists_iso_coneTriangle (coneTriangle S hX hY u v w) hX' hY' u'
    hu v' w' hT').1 (coneTriangle_mem_distinguishedTriangles hX hY u v w hT)

end PairCategory

open PairCategory

variable [Nonempty I]

/-- The stage inclusions are triangulated functors. -/
instance ι_isTriangulated (i : I) : (S.ι i).IsTriangulated where
  map_distinguished τ hτ := mapTriangle_mem_distinguishedTriangles τ hτ

end StageSystem

end CategoryTheory
