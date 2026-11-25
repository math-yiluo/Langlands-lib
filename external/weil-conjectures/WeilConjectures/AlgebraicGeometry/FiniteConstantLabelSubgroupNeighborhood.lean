/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections

/-! # Closure of finite label sections on an etale neighborhood

The finite-section covering argument for constant abelian neighborhoods.
Source: the explicit finite-operation refinement in
`lem-weil-pbc-finite-constant-abelian-neighborhood`, steps 1--3;
Stacks Project Tag 03RU supplies the finite local constancy definitions.
The proof uses the already proved finite-section and injectivity lemmas in
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections`.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem finite_label_sections_cover
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J (Type (u + 1))] [J.WEqualsLocallyBijective (Type (u + 1))]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
    (F : Sheaf J AddCommGrpCat.{u + 1}) (S : Type (u + 1)) [Finite S]
    (e : (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F ≅
      (constantSheaf J (Type (u + 1))).obj S) (T : C) :
    ∃ R ∈ J T, ∀ (W : C) (g : W ⟶ T), R g → (⊥ : Sieve W) ∉ J W →
      let β := toSheafify J ((Functor.const Cᵒᵖ).obj S) ≫ e.inv.hom
      let t : S → F.obj.obj (op W) := fun s ↦ β.app (op W) s
      Function.Injective t ∧ (∃ s, t s = 0) ∧
        (∀ a b, ∃ c, t c = t a + t b) ∧ (∀ a, ∃ b, t b = -t a) := by
  classical
  let β := toSheafify J ((Functor.const Cᵒᵖ).obj S) ≫ e.inv.hom
  let t : ∀ W : C, S → F.obj.obj (op W) := fun W s ↦ β.app (op W) s
  let z : Unit ⊕ (S × S) ⊕ S → F.obj.obj (op T) :=
    Sum.elim (fun _ ↦ 0) (Sum.elim (fun ab ↦ t T ab.1 + t T ab.2) (fun a ↦ -t T a))
  obtain ⟨R, hR, hl⟩ := J.exists_mem_forall_exists_toSheafify_const_app_eq S
    (fun i ↦ e.hom.hom.app (op T) (z i))
  refine ⟨R, hR, fun W g hg hW ↦ ?_⟩
  have hnat (a : S) : t W a = F.obj.map g.op (t T a) :=
    ConcreteCategory.congr_hom (β.naturality g.op) a
  have hz (i : Unit ⊕ (S × S) ⊕ S) : ∃ a, t W a = F.obj.map g.op (z i) := by
    obtain ⟨a, ha⟩ := hl g hg i
    refine ⟨a, ?_⟩
    have hea := congrArg (fun y ↦ e.inv.hom.app (op W) y) ha
    have hn := ConcreteCategory.congr_hom (e.inv.hom.naturality g.op)
      (e.hom.hom.app (op T) (z i))
    have hid := Iso.hom_inv_id_app_apply ((sheafToPresheaf J (Type (u + 1))).mapIso e)
      (op T) (z i)
    change e.inv.hom.app (op T) (e.hom.hom.app (op T) (z i)) = z i at hid
    simp only [ConcreteCategory.comp_apply, hid] at hn
    exact hea.trans hn
  have hi : Function.Injective (t W) := by
    intro a b hab
    apply J.toSheafify_const_app_injective S hW
    have hh := congrArg (fun y ↦ e.hom.hom.app (op W) y) hab
    have hid (s : S) := Iso.inv_hom_id_app_apply
      ((sheafToPresheaf J (Type (u + 1))).mapIso e) (op W)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj S)).app (op W) s)
    change ∀ s : S, e.hom.hom.app (op W) (t W s) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj S)).app (op W) s at hid
    simpa only [hid] using hh
  refine ⟨hi, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hz (Sum.inl ())
    exact ⟨a, by simpa [z, t, β] using ha⟩
  · intro a b
    obtain ⟨c, hc⟩ := hz (Sum.inr (Sum.inl (a, b)))
    change t W c = F.obj.map g.op (t T a + t T b) at hc
    rw [map_add, ← hnat a, ← hnat b] at hc
    exact ⟨c, hc⟩
  · intro a
    obtain ⟨b, hb⟩ := hz (Sum.inr (Sum.inr a))
    change t W b = F.obj.map g.op (-t T a) at hb
    rw [map_neg, ← hnat a] at hb
    exact ⟨b, hb⟩

set_option backward.isDefEq.respectTransparency false in
/-- Near a specified point, the finite set of constant label sections is an injective
set of sections closed under zero, addition and negation. No group structure on the
labels, or abelian presheaf transformation, is part of this conclusion.
Source: explicit finite-operation refinement of
`lem-weil-pbc-finite-constant-abelian-neighborhood`, steps 1--2; Stacks Project Tag 03RU
supplies the finite local constancy definitions.
(blueprint: lem-weil-pbc-finite-constant-label-subgroup-neighborhood).

Proof: view G over U on the localized etale site. Its finite set chart provides one
constant label section for every s in S. Form the zero section, each pairwise sum of
label sections, and each negative label section at the terminal object. Apply e to
these finitely many sections of G. They are sections of the constant set sheaf at S.
Each such section is locally the image of a label under the constant-presheaf
sheafification map. A finite intersection of their image covering sieves is covering
(the finite-section lemma in ConstantSheafSections). Choose a member of this cover
with a point above x. Restrict the chart to this member V, using the compatibility
of constant sheaves with localization, to get e'. The finitely many lifted labels
show closure under zero, sum and negation of its terminal label map t. The terminal
object is not covered by the empty sieve because V has a point above x. Local
injectivity of the constant-presheaf sheafification map, whose restriction maps are
identities, therefore makes the label map injective. Composing with the chart
isomorphism preserves that injectivity. No connectedness of V is needed. If S is
empty and x exists, local lifting of the zero section gives a contradiction, so the
assumed finite set chart excludes this edge case. -/
theorem finite_constant_label_subgroup_neighborhood {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : Y.Etale)
    (S : Type (u + 1)) [Finite S]
    (e : ((sheafCompose Y.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj S)
    (x : U.left) :
    ∃ (V : U.left.Etale) (v : V.left), V.hom v = x ∧
      ∃ e' : (constantSheaf
          (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
          (Type (u + 1))).obj S ≅
            (sheafCompose
              (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
                (G.over ((MorphismProperty.Over.map ⊤ U.prop).obj V)),
          let β := toSheafify
            (Y.smallEtaleTopology.over ((MorphismProperty.Over.map ⊤ U.prop).obj V))
            ((Functor.const
              (Over ((MorphismProperty.Over.map ⊤ U.prop).obj V))ᵒᵖ).obj
                S) ≫ e'.hom.hom
          let T := (G.over
            ((MorphismProperty.Over.map ⊤ U.prop).obj V)).obj.obj
              (op (Over.mk (𝟙 ((MorphismProperty.Over.map ⊤ U.prop).obj V))))
          let t : S → T := fun s ↦ β.app
            (op (Over.mk (𝟙 ((MorphismProperty.Over.map ⊤ U.prop).obj V)))) s
          Function.Injective t ∧ (∃ s, t s = 0) ∧
            (∀ a b, ∃ c, t c = t a + t b) ∧ (∀ a, ∃ b, t b = -t a) := by
  classical
  let J := Y.smallEtaleTopology
  let TU : Over U := Over.mk (𝟙 U)
  obtain ⟨R, hR, hl⟩ := finite_label_sections_cover (J.over U) (G.over U) S e TU
  have hRY : (Sieve.overEquiv TU R) ∈ J U := (J.mem_over_iff R).mp hR
  obtain ⟨𝒰, h𝒰, hp, hle⟩ := (mem_smallGrothendieckTopology U _).mp hRY
  let := h𝒰
  obtain ⟨i, v, hv⟩ := 𝒰.exists_eq x
  let B : Y.Etale := (𝒰.X i).asOverProp Y (hp i)
  let fB : B ⟶ U := (𝒰.f i).asOverProp Y
  have hfB : Sieve.overEquiv TU R fB := hle _ _ ⟨i⟩
  let V : U.left.Etale := 𝒰.etalePrecoverageToEtale i
  let A : Y.Etale := (MorphismProperty.Over.map ⊤ U.prop).obj V
  let fA : A ⟶ U := MorphismProperty.Over.homMk V.hom
  let k : A ⟶ B := MorphismProperty.Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ (𝒰.X i ↘ Y) = 𝒰.f i ≫ U.hom
    simp only [Category.id_comp]
    exact (HomIsOver.comp_over (f := 𝒰.f i) (S := Y)).symm)
  have hfac : k ≫ fB = fA := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 _ ≫ 𝒰.f i = 𝒰.f i
    exact Category.id_comp _
  have hfA : Sieve.overEquiv TU R fA := by
    rw [← hfac]
    exact (Sieve.overEquiv TU R).downward_closed hfB k
  have hR' : R (Over.homMk fA : Over.mk (fA ≫ 𝟙 U) ⟶ TU) :=
    (Sieve.overEquiv_iff R fA).mp hfA
  have hnon : (⊥ : Sieve A) ∉ J A := by
    intro hbot
    obtain ⟨𝒲, _, hpW, hleW⟩ := (mem_smallGrothendieckTopology A _).mp hbot
    obtain ⟨j, w, hw⟩ := 𝒲.exists_eq v
    exact hleW _ _ ⟨j⟩
  have hnon' : (⊥ : Sieve (Over.mk (fA ≫ 𝟙 U))) ∉
      (J.over U) (Over.mk (fA ≫ 𝟙 U)) := by
    intro hb
    apply hnon
    have hh := (J.mem_over_iff _).mp hb
    rw [(Sieve.overEquiv (Over.mk (fA ≫ 𝟙 U))).map_bot] at hh
    exact hh
  have hclosed := hl _ (Over.homMk fA) hR' hnon'
  let L := Over.map fA
  let c := (L.pushforwardContinuousSheafificationCompatibility (Type (u + 1))
    (J.over A) (J.over U)).app ((Functor.const (Over U)ᵒᵖ).obj S)
  let eS : (constantSheaf (J.over A) (Type (u + 1))).obj S ≅
      (sheafCompose (J.over A) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        (G.over A) :=
    c ≪≫ (J.overMapPullback (Type (u + 1)) fA).mapIso e.symm ≪≫
      Sheaf.pushforwardOverMapIso
        ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G) fA
  refine ⟨V, v, hv, eS, ?_⟩
  have hunit := L.toSheafify_pullbackSheafificationCompatibility
    (Type (u + 1)) (J.over A) (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S)
  have hlabel (s : S) :
      (toSheafify (J.over A) ((Functor.const (Over A)ᵒᵖ).obj S) ≫
        eS.hom.hom).app (op (Over.mk (𝟙 A))) s =
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S) ≫
        e.inv.hom).app (op (Over.mk (fA ≫ 𝟙 U))) s := by
    simp only [eS, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      NatTrans.comp_app, ConcreteCategory.comp_apply]
    change e.inv.hom.app (L.op.obj (op (Over.mk (𝟙 A))))
      ((toSheafify (J.over A) ((Functor.const (Over A)ᵒᵖ).obj S) ≫
        c.hom.hom).app (op (Over.mk (𝟙 A))) s) = _
    have hh := ConcreteCategory.congr_hom
      (NatTrans.congr_app hunit (op (Over.mk (𝟙 A)))) s
    change (toSheafify (J.over A) ((Functor.const (Over A)ᵒᵖ).obj S) ≫
      c.hom.hom).app (op (Over.mk (𝟙 A))) s =
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S)).app
        (L.op.obj (op (Over.mk (𝟙 A)))) s at hh
    refine (congrArg (fun z ↦ e.inv.hom.app
      (L.op.obj (op (Over.mk (𝟙 A)))) z) hh).trans ?_
    change e.inv.hom.app (op (Over.mk (𝟙 A ≫ fA)))
      ((toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S)).app
        (op (Over.mk (𝟙 A ≫ fA))) s) = _
    let φ : (A ⟶ U) → G.obj.obj (op A) := fun f ↦
      e.inv.hom.app (op (Over.mk f))
        ((toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S)).app
          (op (Over.mk f)) s)
    exact congrArg φ (show 𝟙 A ≫ fA = fA ≫ 𝟙 U by simp)
  let tnew : S → G.obj.obj (op A) := fun s ↦
    (toSheafify (J.over A) ((Functor.const (Over A)ᵒᵖ).obj S) ≫
      eS.hom.hom).app (op (Over.mk (𝟙 A))) s
  let told : S → G.obj.obj (op A) := fun s ↦
    (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj S) ≫
      e.inv.hom).app (op (Over.mk (fA ≫ 𝟙 U))) s
  change Function.Injective tnew ∧ (∃ s, tnew s = 0) ∧
    (∀ a b, ∃ d, tnew d = tnew a + tnew b) ∧ (∀ a, ∃ b, tnew b = -tnew a)
  have ht : tnew = told := funext hlabel
  rw [ht]
  exact hclosed

end AlgebraicGeometry.Scheme
