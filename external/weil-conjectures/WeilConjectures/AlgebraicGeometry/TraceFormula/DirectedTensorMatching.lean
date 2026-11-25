/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-! # The matching module of a directed tensor descent datum

The module is constructed as a multiequalizer of pushforwards. Its construction
uses arbitrary transitions; their cocycle is needed only for local invertibility.
Source: Stacks Project, Sheaves, Tags 00AL, 00AM and 04TN; Constructions, Tag 01LI.
(blueprint: def-trf-directed-tensor-matching-module)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackSectionAdjunction

/-- The pushforward map adjoint to a transition on an open refinement.
The equality transport records the specified map of the smaller chart to the base. -/
def tensorMatchingTransition {A B X : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ X) (k : A ⟶ X) (h : f ≫ g = k)
    (M : B.Modules) (N : A.Modules) (t : (tensorPullback f).obj M ⟶ N) :
    (pushforward g).obj M ⟶ (pushforward k).obj N :=
  (pushforward g).map ((tensorPullbackSectionAdjunction f).homEquiv M N t) ≫
    (pushforwardComp f g).hom.app N ≫
    eqToHom (congrArg (fun a ↦ (pushforward a).obj N) h)

/-- Taking mates converts the tensor-pullback compatibility into the matching equation. -/
theorem tensorMatchingTransition_mate {A B X : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ X) (k : A ⟶ X) (h : f ≫ g = k)
    (L : X.Modules) (M : B.Modules) (N : A.Modules)
    (a : (tensorPullback g).obj L ⟶ M) (t : (tensorPullback f).obj M ⟶ N) :
    (tensorPullbackSectionAdjunction k).homEquiv L N
      (eqToHom (congrArg (fun b ↦ (tensorPullback b).obj L) h.symm) ≫
        (tensorPullbackSectionComp f g).hom.app L ≫ (tensorPullback f).map a ≫ t) =
      (tensorPullbackSectionAdjunction g).homEquiv L M a ≫
        tensorMatchingTransition f g k h M N t := by
  subst k
  dsimp only [eqToHom_refl, Category.id_comp, tensorPullbackSectionComp,
    tensorMatchingTransition, Category.comp_id]
  simp only [Category.id_comp, Category.comp_id]
  rw [(tensorPullbackSectionAdjunction (f ≫ g)).homEquiv_naturality_right
    (((tensorPullbackSectionAdjunction (f ≫ g)).leftAdjointUniq
      (((tensorPullbackSectionAdjunction g).comp (tensorPullbackSectionAdjunction f)).ofNatIsoRight
        (pushforwardComp f g))).hom.app L)
    ((tensorPullback f).map a ≫ t),
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [← Adjunction.homEquiv_unit, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  change (tensorPullbackSectionAdjunction g).homEquiv L _
      ((tensorPullbackSectionAdjunction f).homEquiv _ _ ((tensorPullback f).map a ≫ t)) ≫
        (pushforwardComp f g).hom.app N = _
  rw [(tensorPullbackSectionAdjunction f).homEquiv_naturality_left a t,
    (tensorPullbackSectionAdjunction g).homEquiv_naturality_right]
  simp only [Category.assoc]

/-- Composition of adjoint transitions agrees with the normalized tensor associator. -/
theorem tensorMatchingTransition_comp {A B C X : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (q : C ⟶ X)
    (M : C.Modules) (N : B.Modules) (O : A.Modules)
    (a : (tensorPullback g).obj M ⟶ N) (b : (tensorPullback f).obj N ⟶ O) :
    tensorMatchingTransition (f ≫ g) q ((f ≫ g) ≫ q) rfl M O
      (eqToHom (congrArg (fun z ↦ (tensorPullback z).obj M) (rfl : f ≫ g = f ≫ g)) ≫
        (tensorPullbackSectionComp f g).hom.app M ≫ (tensorPullback f).map a ≫ b) =
      tensorMatchingTransition g q (g ≫ q) rfl M N a ≫
        tensorMatchingTransition f (g ≫ q) ((f ≫ g) ≫ q)
          (Category.assoc f g q).symm N O b := by
  have hm := tensorMatchingTransition_mate f g (f ≫ g) rfl M N O a b
  dsimp only [tensorMatchingTransition]
  rw [hm]
  ext V x
  simp only [tensorMatchingTransition, Hom.comp_app, pushforward_map_app,
    pushforwardComp_hom_app_app, eqToHom_refl, Hom.id_app,
    ConcreteCategory.comp_apply]
  rfl

/-- The composition formula also allows all specified equality transports. -/
theorem tensorMatchingTransition_comp_of_eq {A B C X : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (q : C ⟶ X)
    (fg : A ⟶ C) (gq : B ⟶ X) (fq : A ⟶ X)
    (hfg : fg = f ≫ g) (hgq : g ≫ q = gq)
    (hfq : f ≫ gq = fq) (hfgq : fg ≫ q = fq)
    (M : C.Modules) (N : B.Modules) (O : A.Modules)
    (a : (tensorPullback g).obj M ⟶ N) (b : (tensorPullback f).obj N ⟶ O) :
    tensorMatchingTransition fg q fq hfgq M O
      (eqToHom (congrArg (fun z ↦ (tensorPullback z).obj M) hfg) ≫
        (tensorPullbackSectionComp f g).hom.app M ≫ (tensorPullback f).map a ≫ b) =
      tensorMatchingTransition g q gq hgq M N a ≫
        tensorMatchingTransition f gq fq hfq N O b := by
  -- Retain left association by eliminating hfgq, rather than the other equation for fq.
  -- This avoids comparing large tensor constructions over differently associated maps.
  cases hfg
  cases hgq
  cases hfgq
  exact tensorMatchingTransition_comp f g q M N O a b

private theorem iso_cocycle_hom {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (F : B ⥤ A) (G : C ⥤ B) (H : C ⥤ A) (d : H ≅ G ⋙ F)
    (M : C) (N : B) (O R : A) (hR : R = H.obj M)
    (a : G.obj M ≅ N) (b : F.obj N ≅ O) (c : R ≅ O)
    (hc : c = eqToIso hR ≪≫ d.app M ≪≫ F.mapIso a ≪≫ b) :
    c.hom = eqToHom hR ≫ d.hom.app M ≫ F.map a.hom ≫ b.hom := by
  have hhom := congrArg Iso.hom hc
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, eqToIso.hom] using hhom

/-- Equality of four abstract isomorphism factors can be checked on specified hom maps. -/
theorem tensorMatching_iso_four_eq_of_hom {A : Type*} [Category* A]
    {V W X Y Z : A} (a : V ≅ W) (b : W ≅ X) (c : X ≅ Y) (d : Y ≅ Z)
    (e : V ≅ Z) (ah : V ⟶ W) (bh : W ⟶ X) (ch : X ⟶ Y) (eh : V ⟶ Z)
    (ha : a.hom = ah) (hb : b.hom = bh) (hc : c.hom = ch) (he : e.hom = eh)
    (h : ah ≫ bh ≫ ch ≫ d.hom = eh) : a ≪≫ b ≪≫ c ≪≫ d = e := by
  apply Iso.ext
  change a.hom ≫ b.hom ≫ c.hom ≫ d.hom = e.hom
  rw [ha, hb, hc, he]
  exact h

/-- A functor sends an isomorphism's specified hom map to its mapped hom map. -/
theorem tensorMatching_mapIso_hom {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {M N : A} (a : M ≅ N) (ah : M ⟶ N) (ha : a.hom = ah) :
    (F.mapIso a).hom = F.map ah := by
  exact congrArg (fun f ↦ F.map f) ha

attribute [local irreducible] tensorPullbackSectionComp

private theorem tensorMatching_cocycle_hom {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (fg : A ⟶ C) (hfg : fg = f ≫ g)
    (M : C.Modules) (N : B.Modules) (O : A.Modules)
    (a : (tensorPullback g).obj M ≅ N) (b : (tensorPullback f).obj N ≅ O)
    (c : (tensorPullback fg).obj M ≅ O)
    (hc : c = eqToIso (congrArg (fun z ↦ (tensorPullback z).obj M) hfg) ≪≫
      (tensorPullbackSectionComp f g).app M ≪≫ (tensorPullback f).mapIso a ≪≫ b) :
    c.hom = eqToHom (congrArg (fun z ↦ (tensorPullback z).obj M) hfg) ≫
      (tensorPullbackSectionComp f g).hom.app M ≫ (tensorPullback f).map a.hom ≫ b.hom := by
  exact iso_cocycle_hom (tensorPullback f) (tensorPullback g) (tensorPullback (f ≫ g))
    (tensorPullbackSectionComp f g) M N O ((tensorPullback fg).obj M)
    (congrArg (fun z ↦ (tensorPullback z).obj M) hfg) a b c hc

/-- The same composition law, with the cocycle supplied as an equality of isomorphisms. -/
theorem tensorMatchingTransition_comp_of_iso {A B C X : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (q : C ⟶ X)
    (fg : A ⟶ C) (gq : B ⟶ X) (fq : A ⟶ X)
    (hfg : fg = f ≫ g) (hgq : g ≫ q = gq)
    (hfq : f ≫ gq = fq) (hfgq : fg ≫ q = fq)
    (M : C.Modules) (N : B.Modules) (O : A.Modules)
    (a : (tensorPullback g).obj M ≅ N) (b : (tensorPullback f).obj N ≅ O)
    (c : (tensorPullback fg).obj M ≅ O)
    (hc : c = eqToIso (congrArg (fun z ↦ (tensorPullback z).obj M) hfg) ≪≫
      (tensorPullbackSectionComp f g).app M ≪≫ (tensorPullback f).mapIso a ≪≫ b) :
    tensorMatchingTransition fg q fq hfgq M O c.hom =
      tensorMatchingTransition g q gq hgq M N a.hom ≫
        tensorMatchingTransition f gq fq hfq N O b.hom := by
  exact (congrArg (tensorMatchingTransition fg q fq hfgq M O)
    (tensorMatching_cocycle_hom f g fg hfg M N O a b c hc)).trans
      (tensorMatchingTransition_comp_of_eq f g q fg gq fq hfg hgq hfq hfgq M N O
        a.hom b.hom)

variable {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) [Category.{v} 𝒰.I₀]
  [𝒰.LocallyDirected]
  (M : ∀ i : 𝒰.I₀, (𝒰.X i).Modules)
  (t : ∀ {i j : 𝒰.I₀} (f : i ⟶ j), (tensorPullback (𝒰.trans f)).obj (M j) ≅ M i)

/-- A universe-small index for the matching equations, even if the hom universe is large. -/
def TensorMatchingIndex := {ij : 𝒰.I₀ × 𝒰.I₀ // Nonempty (ij.1 ⟶ ij.2)}

/-- Shape of the matching equations. -/
def tensorMatchingShape : MulticospanShape where
  L := 𝒰.I₀
  R := TensorMatchingIndex 𝒰
  fst a := a.val.1
  snd a := a.val.2

/-- The diagram equating a smaller chart's section with the restriction of a larger one. -/
def tensorMatchingDiagram : MulticospanIndex (tensorMatchingShape 𝒰) X.Modules where
  left i := (pushforward (𝒰.f i)).obj (M i)
  right a := (pushforward (𝒰.f a.val.1)).obj (M a.val.1)
  fst _ := 𝟙 _
  snd a := tensorMatchingTransition (𝒰.trans a.property.some) (𝒰.f a.val.2)
    (𝒰.f a.val.1) (𝒰.trans_map a.property.some) (M a.val.2) (M a.val.1)
    (t a.property.some).hom

/-- The actual module of matching sections, built by limits, without an existence theorem. -/
def tensorMatchingModule : X.Modules := multiequalizer (tensorMatchingDiagram 𝒰 M t)

/-- Projection of a matching family to a chart, before adjunction. -/
def tensorMatchingProjection (i : 𝒰.I₀) :
    tensorMatchingModule 𝒰 M t ⟶ (pushforward (𝒰.f i)).obj (M i) :=
  Multiequalizer.ι (tensorMatchingDiagram 𝒰 M t) i

/-- The canonical map from the tensor restriction of the matching module to a chart module. -/
def tensorMatchingChart (i : 𝒰.I₀) :
    (tensorPullback (𝒰.f i)).obj (tensorMatchingModule 𝒰 M t) ⟶ M i :=
  ((tensorPullbackSectionAdjunction (𝒰.f i)).homEquiv _ _).symm
    (tensorMatchingProjection 𝒰 M t i)

/-- Every transition preserves the canonical matching projections. -/
theorem tensorMatchingProjection_condition [Quiver.IsThin 𝒰.I₀]
    {i j : 𝒰.I₀} (f : i ⟶ j) :
    tensorMatchingProjection 𝒰 M t j ≫
        tensorMatchingTransition (𝒰.trans f) (𝒰.f j) (𝒰.f i) (𝒰.trans_map f)
          (M j) (M i) (t f).hom =
      tensorMatchingProjection 𝒰 M t i := by
  let a : TensorMatchingIndex 𝒰 := ⟨(i, j), ⟨f⟩⟩
  have h := Multiequalizer.condition (tensorMatchingDiagram 𝒰 M t) a
  change tensorMatchingProjection 𝒰 M t i ≫ 𝟙 _ =
    tensorMatchingProjection 𝒰 M t j ≫
      tensorMatchingTransition (𝒰.trans a.property.some) (𝒰.f j) (𝒰.f i)
        (𝒰.trans_map a.property.some) (M j) (M i) (t a.property.some).hom at h
  have hf : a.property.some = f := Subsingleton.elim _ _
  rw [hf, Category.comp_id] at h
  exact h.symm

end

end AlgebraicGeometry.Scheme.Modules
