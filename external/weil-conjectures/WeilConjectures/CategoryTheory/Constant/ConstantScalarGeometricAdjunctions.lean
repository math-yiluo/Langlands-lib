/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# Constant scalar restriction and geometric module adjunctions

Source: Stacks Project, Sites, Tag 00YV (6), and Categories, Tag 0B65;
normalized constant-scalar comparison (blueprint: lem-sfb-constant-scalar-geometric-adjunctions).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The induced geometric adjunction on fixed-ring module sheaves. The direct-image
comparison and generalized-element equation specify the transported addition and every
scalar endomorphism. The inverse image is its specified left adjoint; hence uniqueness
of left adjoints identifies it with the induced geometric inverse image.
Source: Stacks Project, Sites, Tag 00YV (6), proof by scalar endomorphisms
(blueprint: lem-sfb-constant-scalar-geometric-adjunctions). -/
structure FixedScalarGeometricAdjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (B : Type u) [CommRing B]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (a : L ⊣ V) (hL : PreservesFiniteLimits L) where
  /-- Induced inverse image of fixed-scalar module sheaves. -/
  inverse : Sheaf J (ModuleCat.{u} B) ⥤ Sheaf K (ModuleCat.{u} B)
  /-- Induced direct image of fixed-scalar module sheaves. -/
  direct : Sheaf K (ModuleCat.{u} B) ⥤ Sheaf J (ModuleCat.{u} B)
  /-- The specified module adjunction. -/
  adj : inverse ⊣ direct
  /-- Identification with the given direct image on underlying sheaves. -/
  underlying : direct ⋙ sheafCompose J (forget (ModuleCat.{u} B)) ≅
    sheafCompose K (forget (ModuleCat.{u} B)) ⋙ V
  /-- The direct-image action and addition under the given sheaf adjunction.
  This also determines zero and negation by the abelian group laws. -/
  linear : ∀ (N : Sheaf K (ModuleCat.{u} B)) (T : Sheaf J (Type u)) (b : B)
    (x y z : T ⟶ (sheafCompose J (forget (ModuleCat.{u} B))).obj (direct.obj N)),
    (∀ (U : Cᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((direct.obj N).obj.obj U) inferInstance
        (@SMul.smul B ((direct.obj N).obj.obj U) inferInstance b (x.hom.app U t))
        (y.hom.app U t)) →
    ∀ (U : Dᵒᵖ) (t : (L.obj T).obj.obj U),
      ((a.homEquiv T _).symm (z ≫ underlying.hom.app N)).hom.app U t =
        @Add.add (N.obj.obj U) inferInstance
          (@SMul.smul B (N.obj.obj U) inferInstance b
            (((a.homEquiv T _).symm (x ≫ underlying.hom.app N)).hom.app U t))
          (((a.homEquiv T _).symm (y ≫ underlying.hom.app N)).hom.app U t)

private def constantScalar
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B] (b : B) :
    (constantSheaf J (Type u)).obj PUnit.{u + 1} ⟶
      (sheafCompose J (forget RingCat.{u})).obj
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B)) :=
  (constantSheaf J (Type u)).map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ b)) ≫
    (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of B)

private theorem constantScalar_apply
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B] (b : B) (U : Cᵒᵖ)
    (t : ((constantSheaf J (Type u)).obj PUnit.{u + 1}).obj.obj U) :
    (constantScalar J B b).hom.app U t =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app U b := by
  let P := (Functor.const Cᵒᵖ).obj PUnit.{u + 1}
  let : IsIso (toSheafify J P) :=
    isIso_toSheafify J (Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)
  obtain ⟨x, hx⟩ := ((isIso_iff_bijective _).mp
    (inferInstance : IsIso ((toSheafify J P).app U))).2 t
  subst t
  have hn := congrArg (fun f ↦ f.app U x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map
      (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ b))))
  change _ = ((constantSheaf J (Type u)).map
    (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ b))).hom.app U
      ((toSheafify J P).app U x) at hn
  change ((constantCommuteCompose J (forget RingCat.{u})).inv.app
    (RingCat.of B)).hom.app U _ = _
  have hn' : ((constantSheaf J (Type u)).map
      (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ b))).hom.app U
        ((toSheafify J P).app U x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b := hn.symm
  apply Eq.trans (congrArg
    (fun z ↦ ((constantCommuteCompose J (forget RingCat.{u})).inv.app
      (RingCat.of B)).hom.app U z) hn')
  have hf := congrArg (fun f ↦ f.app U b)
    (sheafComposeIso_hom_fac J (forget RingCat.{u})
      ((Functor.const Cᵒᵖ).obj (RingCat.of B)))
  have hconst := toSheafify_naturality J
    ((Functor.compConstIso Cᵒᵖ (forget RingCat.{u})).hom.app (RingCat.of B))
  have hp := congrArg (fun f ↦ f.app U b) hconst
  dsimp at hp
  change ((sheafifyComposeIso J (forget RingCat.{u})
    ((Functor.const Cᵒᵖ).obj (RingCat.of B))).hom.app U)
      ((((presheafToSheaf J (Type u)).map
        ((Functor.compConstIso Cᵒᵖ (forget RingCat.{u})).hom.app
          (RingCat.of B))).hom.app U)
            ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b)) = _
  exact (congrArg (fun z ↦ ((sheafifyComposeIso J (forget RingCat.{u})
    ((Functor.const Cᵒᵖ).obj (RingCat.of B))).hom.app U) z) hp.symm).trans hf

private def toConstantUnit
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (T : Sheaf J (Type u)) : T ⟶ (constantSheaf J (Type u)).obj PUnit.{u + 1} where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (fun _ ↦
      (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{u + 1})).app U PUnit.unit)
      naturality := by
        intro U V f
        ext t
        exact congrArg (fun g ↦ g PUnit.unit)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{u + 1})).naturality f) }

private def scalarAdd
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {B : Type u} [CommRing B] (N : Sheaf J (ModuleCat.{u} B))
    (T : Sheaf J (Type u)) (b : B)
    (x y : T ⟶ (sheafCompose J (forget (ModuleCat.{u} B))).obj N) :
    T ⟶ (sheafCompose J (forget (ModuleCat.{u} B))).obj N where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (fun t ↦
        @Add.add (N.obj.obj U) inferInstance
          (@SMul.smul B (N.obj.obj U) inferInstance b (x.hom.app U t)) (y.hom.app U t))
      naturality := by
        intro U V f
        ext t
        change @Add.add (N.obj.obj V) inferInstance
          (@SMul.smul B (N.obj.obj V) inferInstance b (x.hom.app V (T.obj.map f t)))
          (y.hom.app V (T.obj.map f t)) = N.obj.map f
            (@Add.add (N.obj.obj U) inferInstance
              (@SMul.smul B (N.obj.obj U) inferInstance b (x.hom.app U t)) (y.hom.app U t))
        erw [map_add, map_smul]
        congr 1
        · exact congrArg (fun g ↦ @SMul.smul B (N.obj.obj V) inferInstance b (g t))
            (x.hom.naturality f)
        · exact congrArg (fun g ↦ g t) (y.hom.naturality f) }

-- Comparing the two bundled scalar actions unfolds restriction of scalars and sheaf composition.
private theorem scalarComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (B : Type u) [CommRing B]
    (r : RingedToposMorphism
      ((constantSheaf K RingCat.{u}).obj (RingCat.of B))
      ((constantSheaf J RingCat.{u}).obj (RingCat.of B)))
    (e₁ : r.inverse.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    (hn : ∀ b : B,
      r.inverse.map ((constantSheaf J (Type u)).map
        (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ b)) ≫
        (constantCommuteCompose J (forget RingCat.{u})).inv.app (RingCat.of B)) ≫
        r.ringMap =
      e₁.hom ≫ (constantSheaf K (Type u)).map
        (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ b)) ≫
        (constantCommuteCompose K (forget RingCat.{u})).inv.app (RingCat.of B))
    (q : FixedScalarGeometricAdjunction J K B r.inverse r.direct r.adj r.leftExact) :
    ∃ β : r.modules ⋙ constantRingModuleRestriction J B ≅
        constantRingModuleRestriction K B ⋙ q.direct,
      ∀ N, (sheafCompose J (forget (ModuleCat.{u} B))).map (β.hom.app N) ≫
        q.underlying.hom.app ((constantRingModuleRestriction K B).obj N) =
          r.underlying.hom.app N := by
  let U := sheafCompose J (forget (ModuleCat.{u} B))
  let S := constantRingModuleRestriction J B
  let H := constantRingModuleRestriction K B
  let θ (N) : U.obj (S.obj (r.modules.obj N)) ≅ U.obj (q.direct.obj (H.obj N)) :=
    r.underlying.app N ≪≫ (q.underlying.app (H.obj N)).symm
  have hop N (T : Sheaf J (Type u)) (b : B)
      (x y : T ⟶ U.obj (S.obj (r.modules.obj N))) :
      scalarAdd (S.obj (r.modules.obj N)) T b x y ≫ (θ N).hom =
        scalarAdd (q.direct.obj (H.obj N)) T b (x ≫ (θ N).hom) (y ≫ (θ N).hom) := by
    apply (cancel_mono (q.underlying.hom.app (H.obj N))).1
    apply (r.adj.homEquiv T _).symm.injective
    let a := toConstantUnit J T ≫ constantScalar J B b
    let z := scalarAdd (S.obj (r.modules.obj N)) T b x y
    have hz (V : Cᵒᵖ) (t : T.obj.obj V) :
        z.hom.app V t = @Add.add ((r.modules.obj N).val.obj V) inferInstance
          (@SMul.smul (((constantSheaf J RingCat.{u}).obj (RingCat.of B)).obj.obj V)
            ((r.modules.obj N).val.obj V) inferInstance
            (a.hom.app V t) (x.hom.app V t)) (y.hom.app V t) := by
      have hs : a.hom.app V t =
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B))).app V b :=
        constantScalar_apply J B b V _
      erw [hs]
      rfl
    have hr := r.module_linear N T a x y z hz
    have hq := q.linear (H.obj N) T b (x ≫ (θ N).hom) (y ≫ (θ N).hom)
      (scalarAdd (q.direct.obj (H.obj N)) T b (x ≫ (θ N).hom)
        (y ≫ (θ N).hom)) (fun _ _ ↦ rfl)
    have hc : r.inverse.map (toConstantUnit J T ≫ constantScalar J B b) ≫
        r.ringMap = r.inverse.map (toConstantUnit J T) ≫ e₁.hom ≫ constantScalar K B b := by
      erw [Functor.map_comp, Category.assoc]
      exact congrArg (fun z ↦ r.inverse.map (toConstantUnit J T) ≫ z) (hn b)
    ext V t
    have hr' := hr V t
    have hq' := hq V t
    erw [hc] at hr'
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply,
      constantScalar_apply] at hr'
    have hθ (w : T ⟶ U.obj (S.obj (r.modules.obj N))) :
        (w ≫ (θ N).hom) ≫ q.underlying.hom.app (H.obj N) =
          w ≫ r.underlying.hom.app N := by
      dsimp [θ]
      erw [Category.assoc, Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    erw [hθ x, hθ y] at hq'
    change _ = @Add.add ((H.obj N).obj.obj V) inferInstance
      (@SMul.smul B ((H.obj N).obj.obj V) inferInstance b _) _ at hr'
    erw [hθ]
    exact hr'.trans hq'.symm
  let g N V : (S.obj (r.modules.obj N)).obj.obj V →
      (q.direct.obj (H.obj N)).obj.obj V := (θ N).hom.hom.app V
  have hl N V (b : B) (x y : (S.obj (r.modules.obj N)).obj.obj V) :
      g N V (b • x + y) =
        b • g N V x + g N V y := by
    let A := U.obj (S.obj (r.modules.obj N))
    have h := hop N (MonoidalCategory.tensorObj A A) b (CartesianMonoidalCategory.fst A A)
      (CartesianMonoidalCategory.snd A A)
    exact congrArg (fun f ↦ f.hom.app V (x, y)) h
  have ha N V (x y : (S.obj (r.modules.obj N)).obj.obj V) :
      g N V (x + y) =
        g N V x + g N V y := by
    simpa using hl N V 1 x y
  have hz N V : g N V 0 = 0 := by
    have h := ha N V 0 0
    simpa using (add_left_cancel (a := g N V 0)
      (by simpa using h.symm :
        g N V 0 + g N V 0 =
          g N V 0 + 0))
  let f N : S.obj (r.modules.obj N) ⟶ q.direct.obj (H.obj N) :=
    { hom :=
      { app := fun V ↦ ConcreteCategory.ofHom (C := ModuleCat B)
          (show (S.obj (r.modules.obj N)).obj.obj V →ₗ[B]
              (q.direct.obj (H.obj N)).obj.obj V from
          { toFun := g N V
            map_add' := ha N V
            map_smul' := fun b x ↦ by simpa [hz] using hl N V b x 0 })
        naturality := by
          intro V W g
          ext x
          exact congrArg (fun g ↦ g x) ((θ N).hom.hom.naturality g) } }
  have hf N : U.map (f N) = (θ N).hom := rfl
  have hi N : IsIso (f N) := by
    have : IsIso (U.map (f N)) := by erw [hf]; infer_instance
    exact isIso_of_reflects_iso (f N) U
  let β : r.modules ⋙ S ≅ H ⋙ q.direct := NatIso.ofComponents
    (fun N ↦ asIso (f N)) (by
      intro N M g
      apply (Functor.map_injective U)
      simp only [Functor.map_comp]
      change U.map (S.map (r.modules.map g)) ≫ (θ M).hom =
        (θ N).hom ≫ U.map (q.direct.map (H.map g))
      dsimp [θ]
      have hr := r.underlying.hom.naturality g
      change U.map (S.map (r.modules.map g)) ≫ r.underlying.hom.app M =
        r.underlying.hom.app N ≫ _ at hr
      erw [← Category.assoc, hr]
      simp only [Category.assoc]
      have hq := q.underlying.inv.naturality (H.map g)
      change _ ≫ q.underlying.inv.app (H.obj M) =
        q.underlying.inv.app (H.obj N) ≫ U.map (q.direct.map (H.map g)) at hq
      erw [← hq]
      rfl)
  refine ⟨β, ?_⟩
  intro N
  change U.map (f N) ≫ _ = _
  erw [hf]
  change (r.underlying.hom.app N ≫ q.underlying.inv.app (H.obj N)) ≫
    q.underlying.hom.app (H.obj N) = _
  erw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- A right-adjoint comparison across fully faithful functors induces an invertible
left-adjoint mate when the target horizontal functor is essentially surjective.
The Hom, unit and counit equations specify the comparison.
Source: Stacks Project, Categories, Tag 0B65; Mathlib adjunction mate equations
(blueprint: lem-sfb-constant-scalar-geometric-adjunctions). -/
theorem adjunctionSquare
    {A A' D D' : Type*} [Category A] [Category A'] [Category D] [Category D']
    (F : A ⥤ A') (G : D ⥤ D') [F.Full] [F.Faithful]
    [G.Full] [G.Faithful] [G.EssSurj]
    {L : A ⥤ D} {R : D ⥤ A} {L' : A' ⥤ D'} {R' : D' ⥤ A'}
    (a : L ⊣ R) (b : L' ⊣ R') (β : R ⋙ F ≅ G ⋙ R') :
    ∃ α : L ⋙ G ≅ F ⋙ L',
      (∀ M N (f : L.obj M ⟶ N),
        b.homEquiv _ _ (α.inv.app M ≫ G.map f) =
          F.map (a.homEquiv M N f) ≫ β.hom.app N) ∧
      (∀ M, F.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫
        R'.map (α.hom.app M) = b.unit.app (F.obj M)) ∧
      (∀ N, G.map (a.counit.app N) = α.hom.app (R.obj N) ≫
        L'.map (β.hom.app N) ≫ b.counit.app (G.obj N)) := by
  let δ : F ⋙ L' ⟶ L ⋙ G := ((mateEquiv a b).symm β.hom)
  have hu (M : A) : F.map (a.unit.app M) ≫ β.hom.app (L.obj M) =
      b.unit.app (F.obj M) ≫ R'.map (δ.app M) :=
    unit_mateEquiv_symm a b β.hom M
  have he (M : A) (N : D) (f : L.obj M ⟶ N) :
      b.homEquiv _ _ (δ.app M ≫ G.map f) =
        F.map (a.homEquiv M N f) ≫ β.hom.app N := by
    erw [b.homEquiv_unit, R'.map_comp, ← Category.assoc, ← hu]
    have hn := β.hom.naturality f
    change F.map (R.map f) ≫ β.hom.app N =
      β.hom.app (L.obj M) ≫ R'.map (G.map f) at hn
    erw [Category.assoc, ← hn]
    erw [← Category.assoc, ← F.map_comp]
    congr 2
  have hi (M : A) : IsIso (δ.app M) := by
    apply isIso_of_coyoneda_map_bijective
    intro T
    let N := G.objPreimage T
    let e := G.objObjPreimageIso T
    have hb : Function.Bijective
        (fun f : G.obj (L.obj M) ⟶ G.obj N ↦ δ.app M ≫ f) := by
      have hbij : Function.Bijective (fun f : L.obj M ⟶ N ↦
          b.homEquiv _ _ (δ.app M ≫ G.map f)) := by
        erw [show (fun f : L.obj M ⟶ N ↦
          b.homEquiv _ _ (δ.app M ≫ G.map f)) =
            fun f ↦ F.map (a.homEquiv M N f) ≫ β.hom.app N from funext (he M N)]
        have hh := (Iso.homCongr (Iso.refl _) (β.app N)).bijective.comp
          ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.bijective.comp
            (a.homEquiv M N).bijective)
        change Function.Bijective (fun f : L.obj M ⟶ N ↦
          (𝟙 (F.obj M)) ≫ F.map (a.homEquiv M N f) ≫ β.hom.app N) at hh
        simpa only [Category.id_comp] using hh
      have ht := hbij.of_comp_left (b.homEquiv _ _).injective
      exact (Function.Bijective.of_comp_iff _
        (Functor.FullyFaithful.ofFullyFaithful G).homEquiv.bijective).1 ht
    constructor
    · intro x y h
      apply (cancel_mono e.inv).1
      apply hb.1
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ e.inv) h
    · intro f
      obtain ⟨g, hg⟩ := hb.2 (f ≫ e.inv)
      refine ⟨g ≫ e.hom, ?_⟩
      change δ.app M ≫ (g ≫ e.hom) = f
      change δ.app M ≫ g = f ≫ e.inv at hg
      erw [← Category.assoc, hg, Category.assoc, e.inv_hom_id, Category.comp_id]
  have : IsIso δ := NatIso.isIso_of_isIso_app δ
  let α := (asIso δ).symm
  refine ⟨α, he, ?_, ?_⟩
  · intro M
    erw [← Category.assoc, hu, Category.assoc, ← R'.map_comp]
    simp [α]
  · intro N
    have hc := mateEquiv_counit_symm a b β.hom N
    change L'.map (β.hom.app N) ≫ b.counit.app (G.obj N) =
      δ.app (R.obj N) ≫ G.map (a.counit.app N) at hc
    erw [hc, ← Category.assoc]
    simp [α]

end CategoryTheory
