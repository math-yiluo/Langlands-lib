/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Exact augmentation of the sheafified free presheaf Čech nerve

Source: Stacks Project, Tag 01GC.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

private theorem locally_surjective_hom_ext
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {P Q : Cᵒᵖ ⥤ Type v} (f : P ⟶ Q) (hf : Presheaf.IsLocallySurjective J f)
    {T : Cᵒᵖ ⥤ Type v} (hT : Presheaf.IsSheaf J T)
    (g h : Q ⟶ T) (heq : f ≫ g = f ≫ h) : g = h := by
  have := hf
  ext X x
  apply (((isSheaf_iff_isSheaf_of_type J T).1 hT).isSeparated _
    (Presheaf.imageSieve_mem J f x)).ext
  rintro Y i ⟨y, hy⟩
  dsimp
  rw [← NatTrans.naturality_apply g i.op x,
    ← NatTrans.naturality_apply h i.op x, ← hy]
  exact ConcreteCategory.congr_hom (congr_app heq (Opposite.op Y)) y

private theorem free_sheaf_map_epi
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] {P Q : Cᵒᵖ ⥤ Type v}
    (f : P ⟶ Q) (hf : Presheaf.IsLocallySurjective J f) :
    Epi (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf J AddCommGrpCat).map f) := by
  let adj := (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).comp
    (sheafificationAdjunction J AddCommGrpCat)
  refine ⟨?_⟩
  intro T g h heq
  apply (adj.homEquiv Q T).injective
  refine locally_surjective_hom_ext f hf ?_ _ _ ?_
  · apply (isSheaf_iff_isSheaf_of_type _ _).2
    exact Presieve.isSheaf_iso J
      (Functor.isoWhiskerLeft T.obj AddCommGrpCat.coyonedaObjIsoForget) (T.property _)
  · simpa only [adj.homEquiv_naturality_left] using
      congrArg (adj.homEquiv P T) heq

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_zero
    {D E : Type*} [Category D] [Category E] [HasFiniteLimits D]
    [Preadditive E] [HasZeroObject E] (f : Arrow D) (F : D ⥤ E) :
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)).d 1 0 ≫
      F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom)) = 0 := by
  dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp [Fin.sum_univ_two, SimplicialObject.δ, Arrow.cechNerve, ← F.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem extraDegeneracy_exact
    {X : SimplicialObject.Augmented AddCommGrpCat.{v}}
    (ed : X.ExtraDegeneracy)
    (hz : ((AlgebraicTopology.alternatingFaceMapComplex _).obj X.left).d 1 0 ≫
      X.hom.app (Opposite.op (SimplexCategory.mk 0)) = 0) :
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj X.left).d 1 0)
      (X.hom.app (Opposite.op (SimplexCategory.mk 0))) hz).Exact := by
  have hc : ed.s 0 ≫
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj X.left).d 1 0 =
      𝟙 _ - X.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫ ed.s' := by
    dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    simp [Fin.sum_univ_two, ed.s₀_comp_δ₁, sub_eq_add_neg]
  apply (ShortComplex.ab_exact_iff _).2
  intro x hx
  change ↑(X.left.obj (Opposite.op (SimplexCategory.mk 0))) at x
  change X.hom.app (Opposite.op (SimplexCategory.mk 0)) x = 0 at hx
  refine ⟨ed.s 0 x, ?_⟩
  have h := ConcreteCategory.congr_hom hc x
  change ((AlgebraicTopology.alternatingFaceMapComplex _).obj X.left).d 1 0
    (ed.s 0 x) = x - ed.s' (X.hom.app (Opposite.op (SimplexCategory.mk 0)) x) at h
  simpa only [hx, map_zero, sub_zero] using h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def nerveMonoIso
    {D : Type u} [Category.{v} D] [HasFiniteLimits D]
    (f : Arrow D) {Z : D} (g : f.right ⟶ Z) [Mono g] :
    f.cechNerve ≅ (Arrow.mk (f.hom ≫ g)).cechNerve := by
  let h := f.hom ≫ g
  refine NatIso.ofComponents (fun n ↦ ?_) ?_
  · refine
      { hom := WidePullback.lift
          (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f.hom) ≫ g)
          (fun j ↦ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f.hom) j)
          (by intro j; simp)
        inv := WidePullback.lift
          (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ h) 0 ≫ f.hom)
          (fun j ↦ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ h) j)
          (by intro j; apply (cancel_mono g).1; simp [h, Category.assoc])
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply WidePullback.hom_ext
      · intro j; simp [h, Category.assoc]
      · simp [h, Category.assoc]
    · apply WidePullback.hom_ext <;> simp [Category.assoc, h]
  · intro n m α
    apply WidePullback.hom_ext <;> simp [Arrow.cechNerve, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
private noncomputable def nerveMapIso
    {D E : Type*} [Category D] [Category E] [HasFiniteLimits D] [HasFiniteLimits E]
    (F : D ⥤ E) [PreservesFiniteLimits F] (f : Arrow D) :
    f.cechNerve ⋙ F ≅ (Arrow.mk (F.map f.hom)).cechNerve := by
  let L (n : SimplexCategoryᵒᵖ) :=
    WidePullbackShape.wideCospan f.right (fun _ : Fin (n.unop.len + 1) ↦ f.left)
      (fun _ ↦ f.hom)
  let R (n : SimplexCategoryᵒᵖ) :=
    WidePullbackShape.wideCospan (F.obj f.right)
      (fun _ : Fin (n.unop.len + 1) ↦ F.obj f.left) (fun _ ↦ F.map f.hom)
  let eD (n : SimplexCategoryᵒᵖ) : L n ⋙ F ≅ R n :=
    NatIso.ofComponents (fun j ↦ match j with
      | none => Iso.refl _
      | some _ => Iso.refl _)
      (by intro j k α; cases α with
          | id j =>
              change F.map ((L n).map (𝟙 j)) ≫ _ = _ ≫ (R n).map (𝟙 j)
              rw [(L n).map_id, (R n).map_id, F.map_id]
              simp
          | term j => simp [L, R])
  let e (n : SimplexCategoryᵒᵖ) : F.obj (limit (L n)) ≅ limit (R n) :=
    preservesLimitIso F (L n) ≪≫ HasLimit.isoOfNatIso (eD n)
  have hπ (n : SimplexCategoryᵒᵖ) (j : Fin (n.unop.len + 1)) :
      (e n).hom ≫ WidePullback.π (fun _ ↦ F.map f.hom) j =
        F.map (WidePullback.π (fun _ ↦ f.hom) j) := by
    change (e n).hom ≫ limit.π (R n) (some j) = F.map (limit.π (L n) (some j))
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    simp [eD]
  have hb (n : SimplexCategoryᵒᵖ) :
      (e n).hom ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ F.map f.hom) =
        F.map (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f.hom)) := by
    change (e n).hom ≫ limit.π (R n) none = F.map (limit.π (L n) none)
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    simp [eD]
  refine NatIso.ofComponents e ?_
  intro n m α
  apply WidePullback.hom_ext
  · intro j
    dsimp only [Arrow.mk, Functor.comp_map]
    rw [Category.assoc, hπ]
    simp only [← F.map_comp]
    simp [Arrow.cechNerve, Category.assoc, hπ]
  · dsimp only [Arrow.mk, Functor.comp_map]
    rw [Category.assoc, hb]
    simp only [← F.map_comp]
    simp [Arrow.cechNerve, Category.assoc, hb]


set_option backward.isDefEq.respectTransparency false in
private theorem nerveMapIso_base
    {D E : Type*} [Category D] [Category E] [HasFiniteLimits D] [HasFiniteLimits E]
    (F : D ⥤ E) [PreservesFiniteLimits F] (f : Arrow D) (n : ℕ) :
    (nerveMapIso F f).hom.app (Opposite.op (SimplexCategory.mk n)) ≫
      WidePullback.base (fun _ : Fin (n + 1) ↦ F.map f.hom) =
      F.map (WidePullback.base (fun _ : Fin (n + 1) ↦ f.hom)) := by
  dsimp [nerveMapIso]
  simp [Category.assoc, HasLimit.isoOfNatIso_hom_π, preservesLimitIso_hom_π]

set_option backward.isDefEq.respectTransparency false in
private theorem type_augmentation_exact (f : Arrow (Type v)) :
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj
        (f.cechNerve ⋙ AddCommGrpCat.free)).d 1 0)
      (AddCommGrpCat.free.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom)))
      (augmentation_zero f AddCommGrpCat.free)).Exact := by
  classical
  let I : Type v := Set.range f.hom
  let p : f.left ⟶ I := ↾fun a ↦ ⟨f.hom a, ⟨a, rfl⟩⟩
  let j : I ⟶ f.right := ↾fun b ↦ b.1
  have hj : Mono j := (mono_iff_injective _).2 Subtype.val_injective
  have hp : Function.Surjective p := by
    rintro ⟨b, a, rfl⟩
    exact ⟨a, rfl⟩
  obtain ⟨s, hs⟩ := hp.hasRightInverse
  let S : SplitEpi p := { section_ := ↾s, id := by ext b; exact congrArg Subtype.val (hs b) }
  let ed := (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk p) S).map
    AddCommGrpCat.free
  have hex := extraDegeneracy_exact ed (by
    dsimp only [AlgebraicTopology.alternatingFaceMapComplex]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    simp [Fin.sum_univ_two, SimplicialObject.δ, SimplicialObject.const])
  have hex' : (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj
        ((Arrow.mk p).cechNerve ⋙ AddCommGrpCat.free)).d 1 0)
      (AddCommGrpCat.free.map (WidePullback.base (fun _ : Fin 1 ↦ p)))
      (augmentation_zero (Arrow.mk p) AddCommGrpCat.free)).Exact := by
    simpa only [SimplicialObject.Augmented.whiskering,
      SimplicialObject.Augmented.whiskeringObj, SimplicialObject.Augmented.drop,
      SimplicialObject.Augmented.point, Comma.fst, Comma.snd,
      SimplicialObject.whiskering, Functor.whiskeringRight_obj_obj,
      Arrow.augmentedCechNerve, Arrow.mk, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.constComp_hom_app, Category.comp_id] using hex
  let e := nerveMonoIso (Arrow.mk p) j
  change (Arrow.mk p).cechNerve ≅ f.cechNerve at e
  have hb : e.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫
      WidePullback.base (fun _ : Fin 1 ↦ f.hom) =
      WidePullback.base (fun _ : Fin 1 ↦ p) ≫ j := by
    change e.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫
      WidePullback.base (fun _ : Fin 1 ↦ p ≫ j) = _
    simp [e, nerveMonoIso]
  let eFree := (SimplicialObject.whiskering _ _).obj AddCommGrpCat.free |>.mapIso e
  let eP := (AlgebraicTopology.alternatingFaceMapComplex _).mapIso eFree
  let φ : ShortComplex.mk _ _ (augmentation_zero (Arrow.mk p) AddCommGrpCat.free) ⟶
      ShortComplex.mk _ _ (augmentation_zero f AddCommGrpCat.free) :=
    { τ₁ := eP.hom.f 1
      τ₂ := eP.hom.f 0
      τ₃ := AddCommGrpCat.free.map j
      comm₁₂ := eP.hom.comm 1 0
      comm₂₃ := by
        dsimp [eP, eFree, SimplicialObject.whiskering,
          Functor.whiskeringRight, Functor.whiskerRight]
        simp only [← AddCommGrpCat.free.map_comp]
        change AddCommGrpCat.free.map (e.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫
          WidePullback.base (fun _ : Fin 1 ↦ f.hom)) = _
        exact congrArg AddCommGrpCat.free.map hb }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex'

set_option backward.isDefEq.respectTransparency false in
private theorem presheaf_augmentation_exact
    {C : Type u} [Category.{v} C] (f : Arrow (Cᵒᵖ ⥤ Type v)) :
    let F := (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free
    (ShortComplex.mk
      (((AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)).d 1 0)
      (F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom)))
      (augmentation_zero f F)).Exact := by
  let F := (Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat).obj AddCommGrpCat.free
  let P := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  let S := ShortComplex.mk (P.d 1 0)
    (F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom))) (augmentation_zero f F)
  let E := fun X ↦ (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj X
  have hjoint : JointlyFaithful E := ⟨by
    intro P Q α β h
    apply NatTrans.ext
    funext X
    exact h X⟩
  apply hjoint.jointlyReflectsIsomorphisms.exact_iff S |>.2
  intro X
  let V := (evaluation Cᵒᵖ (Type v)).obj X
  let q := Arrow.mk (f.hom.app X)
  let eN := nerveMapIso V f
  let eFree := (SimplicialObject.whiskering _ _).obj AddCommGrpCat.free |>.mapIso eN
  let eP := (AlgebraicTopology.alternatingFaceMapComplex _).mapIso eFree
  let φ : S.map (E X) ⟶
      ShortComplex.mk _ _ (augmentation_zero q AddCommGrpCat.free) :=
    { τ₁ := eP.hom.f 1
      τ₂ := eP.hom.f 0
      τ₃ := 𝟙 _
      comm₁₂ := by
        have hd : (E X).map (P.d 1 0) =
            ((AlgebraicTopology.alternatingFaceMapComplex _).obj
              ((f.cechNerve ⋙ V) ⋙ AddCommGrpCat.free)).d 1 0 := by
          simp only [P, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
            AlgebraicTopology.AlternatingFaceMapComplex.objD,
            Functor.map_sum, Functor.map_zsmul]
          rfl
        change eP.hom.f 1 ≫ _ = (E X).map (P.d 1 0) ≫ eP.hom.f 0
        rw [hd]
        exact eP.hom.comm 1 0
      comm₂₃ := by
        dsimp [S, F, E, eP, eFree, SimplicialObject.whiskering,
          Functor.whiskeringRight, Functor.whiskerRight]
        simp only [Category.comp_id, ← AddCommGrpCat.free.map_comp]
        exact congrArg AddCommGrpCat.free.map (nerveMapIso_base V f 0) }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (type_augmentation_exact q)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical free Čech augmentation is exact and epic for a locally
surjective presheaf map.
Source: Stacks Project, Tag 01GC, degree-zero part.
(blueprint: lem-sc-presheaf-cech-sheaf-augmentation-exact)

Proof: the augmentation sends each vertex to its image. Both faces of an edge
have the same image, so its composite with the first differential is zero.
Objectwise the free nerve resolves the free abelian group on the image of the
map, by `AlgebraicTopology.setCechNerve_free_resolution`. Sheafification is exact.
For the image inclusion, free abelianization is injective. A finite sum of target
generators lifts locally: lift each generator using local surjectivity and take
a common covering refinement for their finitely many covers. Thus the free image
inclusion is a local bijection, and its sheafification is an isomorphism. Hence
the augmentation is epic with kernel the first differential's image. Empty
fibres cause no problem: only the image is used before sheafification.
-/
theorem presheafCechSheaf_augmentation_exact
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] (f : Arrow (Cᵒᵖ ⥤ Type v))
    (hf : Presheaf.IsLocallySurjective J f.hom) :
  let F := (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J AddCommGrpCat
  let A := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  let ε := F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom))
  ∃ hz : A.d 1 0 ≫ ε = 0,
    (ShortComplex.mk (A.d 1 0) ε hz).Exact ∧ Epi ε := by
  dsimp only
  let F := (Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat).obj AddCommGrpCat.free
  let G := presheafToSheaf J AddCommGrpCat.{v}
  let P := (AlgebraicTopology.alternatingFaceMapComplex _).obj (f.cechNerve ⋙ F)
  let hz := augmentation_zero f (F ⋙ G)
  refine ⟨hz, ?_, ?_⟩
  · have hex := (presheaf_augmentation_exact f).map G
    have hd : G.map (P.d 1 0) =
        ((AlgebraicTopology.alternatingFaceMapComplex _).obj
          (f.cechNerve ⋙ (F ⋙ G))).d 1 0 := by
      simp only [P, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        AlgebraicTopology.AlternatingFaceMapComplex.objD,
        Functor.map_sum, Functor.map_zsmul]
      rfl
    change (ShortComplex.mk (G.map (P.d 1 0))
      (G.map (F.map (WidePullback.base (fun _ : Fin 1 ↦ f.hom)))) _).Exact at hex
    simpa only [hd, P, F, G, AlgebraicTopology.alternatingFaceMapComplex_obj_X,
      Functor.comp_obj, Functor.comp_map] using hex
  · have := hf
    let π := WidePullback.π (fun _ : Fin 1 ↦ f.hom) 0
    have hπ : Presheaf.IsLocallySurjective J π := by
      apply Presheaf.isLocallySurjective_of_surjective
      intro X x
      let s : f.left ⟶ f.cechNerve.obj (Opposite.op (SimplexCategory.mk 0)) :=
        WidePullback.lift f.hom (fun _ : Fin 1 ↦ 𝟙 f.left) (by simp)
      refine ⟨s.app X x, ?_⟩
      have h : s ≫ π = 𝟙 f.left := by simp [s, π]
      exact ConcreteCategory.congr_hom (congr_app h X) x
    have hb : π ≫ f.hom = WidePullback.base (fun _ : Fin 1 ↦ f.hom) := by
      simp [π]
    have hbase : Presheaf.IsLocallySurjective J
        (WidePullback.base (fun _ : Fin 1 ↦ f.hom)) := by
      rw [← hb]
      infer_instance
    exact free_sheaf_map_epi _ hbase

end CategoryTheory.Sheaf
