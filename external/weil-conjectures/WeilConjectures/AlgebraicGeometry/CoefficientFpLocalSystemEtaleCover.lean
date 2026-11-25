/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantEtaleSections
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Etale trivializing charts for coefficient-sized local systems

Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type w} [Category.{t} A]

/-- Isomorphisms between restrictions to a slice, with pullback restriction maps. -/
private def localIsom (F G : Sheaf J A) : Cᵒᵖ ⥤ Type (max u v t) where
  obj U := F.over U.unop ≅ G.over U.unop
  map f := ↾((J.overMapPullback A f.unop).mapIso)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Iso.ext
    have h := ConcreteCategory.congr_hom ((sheafHom F G).obj.map_id U) a.hom
    exact h
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Iso.ext
    have h := ConcreteCategory.congr_hom ((sheafHom F G).obj.map_comp f g) a.hom
    exact h

private def localIsomHom (F G : Sheaf J A) : localIsom F G ⟶ (sheafHom F G).obj where
  app _ := ↾fun a ↦ a.hom
  naturality {_ _} _ := rfl

private def localIsomInv (F G : Sheaf J A) : localIsom F G ⟶ (sheafHom G F).obj where
  app _ := ↾fun a ↦ a.inv
  naturality {_ _} _ := rfl

private theorem localIsom_isSheaf (F G : Sheaf J A) :
    Presheaf.IsSheaf J (localIsom F G) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  let H := (isSheaf_iff_isSheaf_of_type J _).1 (sheafHom F G).property
  let H' := (isSheaf_iff_isSheaf_of_type J _).1 (sheafHom G F).property
  let a := (H S hS).amalgamate (x.map (localIsomHom F G)) (hx.map _)
  let b := (H' S hS).amalgamate (x.map (localIsomInv F G)) (hx.map _)
  have ha (V : C) (f : V ⟶ U) (hf : S f) :
      (sheafHom F G).obj.map f.op a = (x f hf).hom :=
    (H S hS).valid_glue (hx.map _) f hf
  have hb (V : C) (f : V ⟶ U) (hf : S f) :
      (sheafHom G F).obj.map f.op b = (x f hf).inv :=
    (H' S hS).valid_glue (hx.map _) f hf
  change ∀ (V : C) (f : V ⟶ U) (hf : S f),
    (J.overMapPullback A f).map a = (x f hf).hom at ha
  change ∀ (V : C) (f : V ⟶ U) (hf : S f),
    (J.overMapPullback A f).map b = (x f hf).inv at hb
  have hab : a ≫ b = 𝟙 _ := by
    apply (((isSheaf_iff_isSheaf_of_type J _).1 (sheafHom F F).property).isSeparated
      S hS).ext
    intro V f hf
    change (J.overMapPullback A f).map (a ≫ b) = (J.overMapPullback A f).map (𝟙 _)
    rw [Functor.map_comp, Functor.map_id, ha V f hf, hb V f hf]
    exact (x f hf).hom_inv_id
  have hba : b ≫ a = 𝟙 _ := by
    apply (((isSheaf_iff_isSheaf_of_type J _).1 (sheafHom G G).property).isSeparated
      S hS).ext
    intro V f hf
    change (J.overMapPullback A f).map (b ≫ a) = (J.overMapPullback A f).map (𝟙 _)
    rw [Functor.map_comp, Functor.map_id, ha V f hf, hb V f hf]
    exact (x f hf).inv_hom_id
  let e : F.over U ≅ G.over U := ⟨a, b, hab, hba⟩
  refine ⟨e, ?_, ?_⟩
  · intro V f hf
    apply Iso.ext
    exact ha V f hf
  · intro e' he'
    apply Iso.ext
    apply (H.isSeparated S hS).ext
    intro V f hf
    have he := congrArg Iso.hom (he' f hf)
    exact he.trans (ha V f hf).symm

private lemma fixedLocalHom_map_app_id (F G : Sheaf J A) {U V : C} (f : V ⟶ U)
    (a : (sheafHom F G).obj.obj (op U)) :
    ((sheafHom F G).obj.map f.op a).hom.app (op (Over.mk (𝟙 V))) =
      a.hom.app (op (Over.mk f)) :=
  presheafHom_map_app_op_mk_id f a.hom

private def localIsomCongr {F F' G G' : Sheaf J A} (e : F ≅ F') (d : G ≅ G') :
    localIsom F G ≅ localIsom F' G' :=
  NatIso.ofComponents (fun U ↦
    { hom := ↾fun a ↦ ((J.overPullback A U.unop).mapIso e).symm ≪≫ a ≪≫
        (J.overPullback A U.unop).mapIso d
      inv := ↾fun a ↦ (J.overPullback A U.unop).mapIso e ≪≫ a ≪≫
        ((J.overPullback A U.unop).mapIso d).symm
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro a
        simp
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro a
        simp }) (by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro a
        apply Iso.ext
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext T
        rfl)

private noncomputable def localIsomOverEquiv (F G : Sheaf J A) {W : C} (V : Over W) :
    (F.over V.left ≅ G.over V.left) ≃ ((F.over W).over V ≅ (G.over W).over V) := by
  let e := Over.iteratedSliceEquiv V
  let Q := (Functor.whiskeringLeft (Over V)ᵒᵖ (Over V.left)ᵒᵖ A).obj e.functor.op
  letI : Q.Full := inferInstance
  letI : Q.Faithful := inferInstance
  exact (fullyFaithfulSheafToPresheaf (J.over V.left) A).isoEquiv.trans
    ((Functor.FullyFaithful.ofFullyFaithful Q).isoEquiv.trans
      ((fullyFaithfulSheafToPresheaf ((J.over W).over V) A).isoEquiv
        (X := (F.over W).over V) (Y := (G.over W).over V)).symm)

private noncomputable def localIsomOver (F G : Sheaf J A) (W : C) :
    (Over.forget W).op ⋙ localIsom F G ≅ localIsom (F.over W) (G.over W) :=
  NatIso.ofComponents (fun V ↦ (localIsomOverEquiv F G V.unop).toIso) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro a
    apply Iso.ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    rfl)

private def localIsomSheaf (F G : Sheaf J A) : Sheaf J (Type (max u v t)) :=
  ⟨localIsom F G, localIsom_isSheaf F G⟩

private noncomputable def localIsomSheafOver (F G : Sheaf J A) (U : C) :
    (localIsomSheaf F G).over U ≅ localIsomSheaf (F.over U) (G.over U) :=
  ObjectProperty.isoMk _ (localIsomOver F G U)

end CategoryTheory

namespace CategoryTheory

section ConstantHom

variable {B : Type u} [SmallCategory B] (J : GrothendieckTopology B)
  (Λ : Type u) [CommRing Λ]
  [HasWeakSheafify J (ModuleCat.{u} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{u} Λ))]

private noncomputable def fixedConstantHom (M N : ModuleCat.{u} Λ) :
    (Functor.const Bᵒᵖ).obj (M ⟶ N) ⟶
      (sheafHom ((constantSheaf J _).obj M) ((constantSheaf J _).obj N)).obj where
  app U := ↾fun a ↦ (J.overPullback _ U.unop).map ((constantSheaf J _).map a)
  naturality {_ _} _ := rfl

private theorem fixedConstantHom_ext (M N : ModuleCat.{u} Λ) (U : B)
    (a b : ((constantSheaf J _).obj M).over U ⟶
      ((constantSheaf J _).obj N).over U)
    (h : ∀ x : M,
      a.hom.app (op (Over.mk (𝟙 U))) ((toSheafify J ((Functor.const Bᵒᵖ).obj M)).app
        (op U) x) =
      b.hom.app (op (Over.mk (𝟙 U))) ((toSheafify J ((Functor.const Bᵒᵖ).obj M)).app
        (op U) x)) : a = b := by
  let FM := (constantSheaf J (ModuleCat.{u} Λ)).obj M
  let FN := (constantSheaf J (ModuleCat.{u} Λ)).obj N
  let η := toSheafify J ((Functor.const Bᵒᵖ).obj M)
  have hlocal (V : Over U) (x : M) :
      a.hom.app (op V) (η.app (op V.left) x) =
        b.hom.app (op V) (η.app (op V.left) x) := by
    have ha := NatTrans.naturality_apply a.hom
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)).op (η.app (op U) x)
    have hb := NatTrans.naturality_apply b.hom
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)).op (η.app (op U) x)
    have hn := NatTrans.naturality_apply η V.hom.op x
    change η.app (op V.left) x = FM.obj.map V.hom.op (η.app (op U) x) at hn
    change a.hom.app (op V) (FM.obj.map V.hom.op (η.app (op U) x)) =
      FN.obj.map V.hom.op (a.hom.app (op (Over.mk (𝟙 U))) (η.app (op U) x)) at ha
    change b.hom.app (op V) (FM.obj.map V.hom.op (η.app (op U) x)) =
      FN.obj.map V.hom.op (b.hom.app (op (Over.mk (𝟙 U))) (η.app (op U) x)) at hb
    rw [hn, ha, hb, h x]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  ext s
  apply FN.property.isSeparated _ _ (Presheaf.imageSieve_mem J η s)
  intro W f hf
  obtain ⟨x, hx⟩ := hf
  let V' : Over U := Over.mk (f ≫ V.unop.hom)
  have ha := NatTrans.naturality_apply a.hom
    (Over.homMk f : V' ⟶ V.unop).op s
  have hb := NatTrans.naturality_apply b.hom
    (Over.homMk f : V' ⟶ V.unop).op s
  change a.hom.app (op V') (FM.obj.map f.op s) = FN.obj.map f.op (a.hom.app V s) at ha
  change b.hom.app (op V') (FM.obj.map f.op s) = FN.obj.map f.op (b.hom.app V s) at hb
  change η.app (op W) x = FM.obj.map f.op s at hx
  change FN.obj.map f.op (a.hom.app V s) = FN.obj.map f.op (b.hom.app V s)
  rw [← ha, ← hb, ← hx]
  exact hlocal V' x

omit [J.HasSheafCompose (forget (ModuleCat.{u} Λ))] in
private theorem fixedConstantHom_injective (M N : ModuleCat.{u} Λ) [Module.Finite Λ M] :
    Presheaf.IsLocallyInjective J (fixedConstantHom J Λ M N) where
  equalizerSieve_mem {U} a b hab := by
    classical
    change M ⟶ N at a b
    let η := toSheafify J ((Functor.const Bᵒᵖ).obj N)
    have he (x : M) : η.app U (a x) = η.app U (b x) := by
      have h := congrArg (fun e ↦ e.hom.app (op (Over.mk (𝟙 U.unop)))
        ((toSheafify J ((Functor.const Bᵒᵖ).obj M)).app U x)) hab
      change ((constantSheaf J (ModuleCat.{u} Λ)).map a).hom.app U
          ((toSheafify J ((Functor.const Bᵒᵖ).obj M)).app U x) =
        ((constantSheaf J (ModuleCat.{u} Λ)).map b).hom.app U
          ((toSheafify J ((Functor.const Bᵒᵖ).obj M)).app U x) at h
      have ha := congr_app (toSheafify_naturality J ((Functor.const Bᵒᵖ).map a)) U
      have hb := congr_app (toSheafify_naturality J ((Functor.const Bᵒᵖ).map b)) U
      exact (ConcreteCategory.congr_hom ha x).trans
        (h.trans (ConcreteCategory.congr_hom hb x).symm)
    let S (x : M) : Sieve U.unop :=
      Presheaf.equalizerSieve (F := (Functor.const Bᵒᵖ).obj N) (X := U) (a x) (b x)
    have hS (x : M) : S x ∈ J U.unop :=
      Presheaf.equalizerSieve_mem J η (a x) (b x) (he x)
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Λ) (M := M)
    apply J.superset_covering _ (J.finset_inf_mem s S (fun m _ ↦ hS m))
    intro V f hf
    change a = b
    apply ModuleCat.hom_ext
    exact LinearMap.ext_on hs (fun x hx ↦ Finset.inf_le hx (f := S) f hf)

/-- Lift the images of finitely many generators, then recover a linear map. -/
private theorem fixedConstantHom_surjective (M N : ModuleCat.{u} Λ) [Module.Finite Λ M] :
    Presheaf.IsLocallySurjective J (fixedConstantHom J Λ M N) where
  imageSieve_mem {U} a := by
    classical
    let FM := (constantSheaf J (ModuleCat.{u} Λ)).obj M
    let FN := (constantSheaf J (ModuleCat.{u} Λ)).obj N
    let ηM := toSheafify J ((Functor.const Bᵒᵖ).obj M)
    let ηN := toSheafify J ((Functor.const Bᵒᵖ).obj N)
    let a₀ : M ⟶ FN.obj.obj (op U) := ηM.app (op U) ≫
      a.hom.app (op (Over.mk (𝟙 U)))
    let S (m : M) : Sieve U := Presheaf.imageSieve ηN (a₀ m)
    have hS (m : M) : S m ∈ J U := Presheaf.imageSieve_mem J ηN (a₀ m)
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Λ) (M := M)
    apply J.transitive (J.finset_inf_mem s S (fun m _ ↦ hS m))
    intro V f hf
    by_cases hV : (⊥ : Sieve V) ∈ J V
    · exact J.superset_covering bot_le hV
    have hinj := J.toSheafify_const_app_injective N hV
    let L : M →ₗ[Λ] FN.obj.obj (op V) := (FN.obj.map f.op).hom.comp a₀.hom
    let ιN := (ηN.app (op V)).hom
    have hle : LinearMap.range L ≤ LinearMap.range ιN := by
      rintro _ ⟨m, rfl⟩
      have hspan : Submodule.span Λ (s : Set M) ≤ (LinearMap.range ιN).comap L :=
        Submodule.span_le.mpr (fun x hx ↦ Finset.inf_le hx (f := S) f hf)
      exact hspan (by rw [hs]; trivial)
    let e := LinearEquiv.ofInjective ιN hinj
    let g : M ⟶ N := ModuleCat.ofHom (e.symm.toLinearMap.comp
      (L.codRestrict _ fun m ↦ hle (LinearMap.mem_range_self L m)))
    have hg (m : M) : ηN.app (op V) (g m) = FN.obj.map f.op (a₀ m) := by
      have h := congrArg Subtype.val
        (e.apply_symm_apply ⟨L m, hle (LinearMap.mem_range_self L m)⟩)
      exact h
    apply J.superset_covering _ (J.top_mem V)
    intro W k hk
    refine ⟨g, ?_⟩
    apply fixedConstantHom_ext J Λ M N W
    intro m
    rw [fixedLocalHom_map_app_id]
    change ((constantSheaf J (ModuleCat.{u} Λ)).map g).hom.app (op W)
        (ηM.app (op W) m) =
      a.hom.app (op (Over.mk (k ≫ f))) (ηM.app (op W) m)
    have hn := ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality J ((Functor.const Bᵒᵖ).map g)) (op W)) m
    change ηN.app (op W) (g m) =
      ((constantSheaf J (ModuleCat.{u} Λ)).map g).hom.app (op W)
        (ηM.app (op W) m) at hn
    rw [← hn]
    have hnN := NatTrans.naturality_apply ηN k.op (g m)
    change ηN.app (op W) (g m) = FN.obj.map k.op (ηN.app (op V) (g m)) at hnN
    rw [hnN, hg, ← ModuleCat.comp_apply, ← FN.obj.map_comp, ← op_comp]
    have ha := NatTrans.naturality_apply a.hom
      (Over.homMk (k ≫ f) : Over.mk (k ≫ f) ⟶ Over.mk (𝟙 U)).op
      (ηM.app (op U) m)
    have hnM := NatTrans.naturality_apply ηM (k ≫ f).op m
    change ηM.app (op W) m = FM.obj.map (k ≫ f).op (ηM.app (op U) m) at hnM
    change a.hom.app (op (Over.mk (k ≫ f)))
        (FM.obj.map (k ≫ f).op (ηM.app (op U) m)) =
      FN.obj.map (k ≫ f).op (a₀ m) at ha
    rw [hnM]
    exact ha.symm

private noncomputable def fixedConstantIsom (M N : ModuleCat.{u} Λ) :
    (Functor.const Bᵒᵖ).obj (M ≅ N) ⟶
      localIsom ((constantSheaf J _).obj M) ((constantSheaf J _).obj N) where
  app U := ↾fun a ↦ (J.overPullback _ U.unop).mapIso ((constantSheaf J _).mapIso a)
  naturality {_ _} _ := rfl

omit [J.HasSheafCompose (forget (ModuleCat.{u} Λ))] in
private theorem fixedConstantIsom_injective (M N : ModuleCat.{u} Λ) [Module.Finite Λ M] :
    Presheaf.IsLocallyInjective J (fixedConstantIsom J Λ M N) := by
  let hMN := fixedConstantHom_injective J Λ M N
  refine ⟨fun {U} a b hab ↦ ?_⟩
  have h := congrArg Iso.hom hab
  have hh := hMN.equalizerSieve_mem (X := U) a.hom b.hom h
  apply J.superset_covering _ hh
  intro V f hf
  change a = b
  apply Iso.ext
  exact hf

private theorem fixedConstantIsom_surjective (M N : ModuleCat.{u} Λ)
    [Module.Finite Λ M] [Module.Finite Λ N] :
    Presheaf.IsLocallySurjective J (fixedConstantIsom J Λ M N) where
  imageSieve_mem {U} e := by
    let sMN := fixedConstantHom_surjective J Λ M N
    let sNM := fixedConstantHom_surjective J Λ N M
    let iMM := fixedConstantHom_injective J Λ M M
    let iNN := fixedConstantHom_injective J Λ N N
    let FM := (constantSheaf J (ModuleCat.{u} Λ)).obj M
    let FN := (constantSheaf J (ModuleCat.{u} Λ)).obj N
    let a := e.hom
    let b := e.inv
    let S := Presheaf.imageSieve (fixedConstantHom J Λ M N) a ⊓
      Presheaf.imageSieve (fixedConstantHom J Λ N M) b
    have hS : S ∈ J U := J.intersection_covering
      (sMN.imageSieve_mem a) (sNM.imageSieve_mem b)
    apply J.transitive hS
    intro V f hf
    obtain ⟨g, hg⟩ := hf.1
    obtain ⟨h, hh⟩ := hf.2
    have hgh : (fixedConstantHom J Λ M M).app (op V) (g ≫ h) =
        (fixedConstantHom J Λ M M).app (op V) (𝟙 M) := by
      change (J.overPullback _ V).map ((constantSheaf J _).map (g ≫ h)) = _
      rw [Functor.map_comp, Functor.map_comp]
      change (fixedConstantHom J Λ M N).app (op V) g ≫
        (fixedConstantHom J Λ N M).app (op V) h = _
      rw [hg, hh]
      change (J.overMapPullback _ f).map e.hom ≫ (J.overMapPullback _ f).map e.inv = _
      rw [← Functor.map_comp, e.hom_inv_id, Functor.map_id]
      change 𝟙 _ = (J.overPullback _ V).map ((constantSheaf J _).map (𝟙 _))
      rw [Functor.map_id, Functor.map_id]
    have hhg : (fixedConstantHom J Λ N N).app (op V) (h ≫ g) =
        (fixedConstantHom J Λ N N).app (op V) (𝟙 N) := by
      change (J.overPullback _ V).map ((constantSheaf J _).map (h ≫ g)) = _
      rw [Functor.map_comp, Functor.map_comp]
      change (fixedConstantHom J Λ N M).app (op V) h ≫
        (fixedConstantHom J Λ M N).app (op V) g = _
      rw [hg, hh]
      change (J.overMapPullback _ f).map e.inv ≫ (J.overMapPullback _ f).map e.hom = _
      rw [← Functor.map_comp, e.inv_hom_id, Functor.map_id]
      change 𝟙 _ = (J.overPullback _ V).map ((constantSheaf J _).map (𝟙 _))
      rw [Functor.map_id, Functor.map_id]
    have heq₁ := iMM.equalizerSieve_mem (X := op V) (g ≫ h) (𝟙 M) hgh
    have heq₂ := iNN.equalizerSieve_mem (X := op V) (h ≫ g) (𝟙 N) hhg
    apply J.superset_covering _ (J.intersection_covering heq₁ heq₂)
    intro W k hk
    let i : M ≅ N := ⟨g, h, hk.1, hk.2⟩
    refine ⟨i, ?_⟩
    apply Iso.ext
    change (fixedConstantHom J Λ M N).app (op W) g = _
    have hg' := congrArg ((sheafHom FM FN).obj.map k.op) hg
    have hn := NatTrans.naturality_apply (fixedConstantHom J Λ M N) k.op g
    rw [← hn] at hg'
    exact hg'.trans (by
      change (sheafHom FM FN).obj.map k.op ((sheafHom FM FN).obj.map f.op a) = _
      rw [← Functor.map_comp_apply, ← op_comp]
      rfl)

/-- Constant finite-type module isomorphisms identify with their slice isomorphism sheaf. -/
private noncomputable def fixedConstantIsomIso (M N : ModuleCat.{u} Λ)
    [Module.Finite Λ M] [Module.Finite Λ N] :
    (constantSheaf J (Type u)).obj (M ≅ N) ≅
      ⟨localIsom ((constantSheaf J _).obj M) ((constantSheaf J _).obj N),
        localIsom_isSheaf _ _⟩ := by
  let I := localIsom ((constantSheaf J (ModuleCat.{u} Λ)).obj M)
    ((constantSheaf J (ModuleCat.{u} Λ)).obj N)
  let hI := localIsom_isSheaf ((constantSheaf J (ModuleCat.{u} Λ)).obj M)
    ((constantSheaf J (ModuleCat.{u} Λ)).obj N)
  let α := fixedConstantIsom J Λ M N
  let : Presheaf.IsLocallyInjective J α := fixedConstantIsom_injective J Λ M N
  let : Presheaf.IsLocallySurjective J α := fixedConstantIsom_surjective J Λ M N
  let c : (constantSheaf J (Type u)).obj (M ≅ N) ⟶ ⟨I, hI⟩ :=
    ⟨sheafifyLift J α hI⟩
  have hc : toSheafify J ((Functor.const Bᵒᵖ).obj (M ≅ N)) ≫ c.hom = α :=
    toSheafify_sheafifyLift J α hI
  let : Presheaf.IsLocallyInjective J c.hom := by
    apply (Presheaf.comp_isLocallyInjective_iff J
      (toSheafify J ((Functor.const Bᵒᵖ).obj (M ≅ N))) c.hom).mp
    rw [hc]
    infer_instance
  let : Presheaf.IsLocallySurjective J c.hom := by
    apply (Presheaf.comp_isLocallySurjective_iff J
      (toSheafify J ((Functor.const Bᵒᵖ).obj (M ≅ N))) c.hom).mp
    rw [hc]
    infer_instance
  let : IsIso c := (Sheaf.isLocallyBijective_iff_isIso c).mp ⟨inferInstance, inferInstance⟩
  exact asIso c

end ConstantHom
end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- A local system with finitely presented models has constant charts on objects
coming from the etale site. The images of these objects cover the pro-etale site.
The conclusion only concerns restrictions and covers, not comparison inverse image.

Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant
(auxiliary; not a blueprint node).

Proof: apply the hypothesis at the terminal object and index its covering sieve by
its arrows, obtaining a covering family U_i with finitely presented models M_i.
For each i construct the set sheaf H_i = Isom(F, constant M_i). On U_j, its slice
restriction is the Isom sheaf between constant M_j and constant M_i. Finite generation
of both models identifies this with the constant set of module isomorphisms.
For the Hom calculation, lift the images of finitely many generators to constants
on a common covering sieve. Away from an empty covering sieve, injectivity of the
constant-sheaf unit reconstructs a linear map; separatedness detects equality.
Lift both maps of an isomorphism and refine the sieve to impose the inverse laws.
These arguments are the private fixedConstantHom and fixedConstantIsom helpers,
generalized from ProEtaleUniformModelEtaleCover to arbitrary small-site universes.
Thus all H_i are locally constant. They are jointly locally inhabited, since H_j
has the displayed trivialization as a section on U_j. Apply the set-valued
coefficientLocallyConstant_etaleSections to this family. Each resulting section is
a slice isomorphism F to the restriction of constant M_i. The constant-sheaf
restriction isomorphism gives the requested chart, with the original finite
presentation proof. This avoids partitioning the base into model-type opens.
Different model types simply give empty local isomorphism sets. Empty covering
families and zero models are handled by the same constructions. -/
theorem coefficientFpLocalSystem_etaleCover (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (hF : ∀ V : Scheme.coefficientProEtaleSiteModel.{u, v} X,
      ∃ S : Sieve V, S ∈ Scheme.coefficientProEtaleModelTopology.{u, v} X V ∧
        ∀ (U : Scheme.coefficientProEtaleSiteModel.{u, v} X) (f : U ⟶ V), S f →
          ∃ M : ModuleCat.{max v (u + 1)} A, Module.FinitePresentation A M ∧
            Nonempty (F.over U ≅
              (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, v} X).over U)
                (ModuleCat.{max v (u + 1)} A)).obj M)) :
    ∃ (I : Type (max v (u + 1)))
      (V : I → Scheme.smallModelComparisonEtaleSite.{u, v} X),
      (Scheme.coefficientProEtaleModelTopology.{u, v} X).CoversTop
        (fun i ↦ (Scheme.smallModelComparisonInclusion.{u, v} X).obj (V i)) ∧
      ∀ i : I, ∃ M : ModuleCat.{max v (u + 1)} A,
        Module.FinitePresentation A M ∧
          Nonempty (F.over ((Scheme.smallModelComparisonInclusion.{u, v} X).obj (V i)) ≅
            (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, v} X).over
              ((Scheme.smallModelComparisonInclusion.{u, v} X).obj (V i)))
              (ModuleCat.{max v (u + 1)} A)).obj M) := by
  classical
  let J := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let C := Scheme.coefficientProEtaleSiteModel.{u, v} X
  let B := ModuleCat.{max v (u + 1)} A
  let T : C := AsSmall.up.obj (Scheme.ProEt.mk (𝟙 X))
  have hT : CategoryTheory.Limits.IsTerminal T :=
    (MorphismProperty.Over.mkIdTerminal _ _).isTerminalObj
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).functor
  obtain ⟨S, hS, hm⟩ := hF T
  let I := Σ U : C, {f : U ⟶ T // S f}
  let U : I → C := Sigma.fst
  have hc : J.CoversTop U := by
    rw [J.coversTop_iff_of_isTerminal T hT]
    apply J.superset_covering _ hS
    intro W f hf
    exact ⟨⟨W, f, hf⟩, ⟨𝟙 W⟩⟩
  have models (i : I) : ∃ M : B, Module.FinitePresentation A M ∧
      Nonempty (F.over (U i) ≅ (constantSheaf (J.over (U i)) B).obj M) :=
    hm i.1 i.2.1 i.2.2
  choose M hM e using models
  let K (i : I) := (constantSheaf J B).obj (M i)
  let H (i : I) := CategoryTheory.localIsomSheaf F (K i)
  have hlocal (i : I) : ∃ (L : Type (max v (u + 1))) (W : L → C),
      J.CoversTop W ∧ ∀ j, ∃ Q : Type (max v (u + 1)),
        Nonempty ((H i).over (W j) ≅ (constantSheaf (J.over (W j))
          (Type (max v (u + 1)))).obj Q) := by
    refine ⟨I, U, hc, fun j ↦ ⟨M j ≅ M i, ?_⟩⟩
    have : Module.FinitePresentation A (M i) := hM i
    have : Module.FinitePresentation A (M j) := hM j
    let d : (K i).over (U j) ≅ (constantSheaf (J.over (U j)) B).obj (M i) :=
      (constantSheafOverIso J B (U j) (M i)).symm
    let b : CategoryTheory.localIsomSheaf (F.over (U j)) ((K i).over (U j)) ≅
        CategoryTheory.localIsomSheaf
          ((constantSheaf (J.over (U j)) B).obj (M j))
          ((constantSheaf (J.over (U j)) B).obj (M i)) :=
      ObjectProperty.isoMk _ (CategoryTheory.localIsomCongr (e j).some d)
    exact ⟨CategoryTheory.localIsomSheafOver F (K i) (U j) ≪≫ b ≪≫
      (CategoryTheory.fixedConstantIsomIso (J.over (U j)) A (M j) (M i)).symm⟩
  have hsec : ∀ j : I, ∃ i : I, Nonempty ((H i).obj.obj (op (U j))) := by
    intro j
    exact ⟨j, ⟨(e j).some ≪≫ constantSheafOverIso J B (U j) (M j)⟩⟩
  obtain ⟨L, V, hV, hs⟩ := coefficientLocallyConstant_etaleSections X I H hlocal I U hc hsec
  refine ⟨L, V, hV, fun j ↦ ?_⟩
  obtain ⟨i, ⟨s⟩⟩ := hs j
  exact ⟨M i, hM i, ⟨s ≪≫ (constantSheafOverIso J B
    ((Scheme.smallModelComparisonInclusion.{u, v} X).obj (V j)) (M i)).symm⟩⟩

end AlgebraicGeometry.ProEtale
