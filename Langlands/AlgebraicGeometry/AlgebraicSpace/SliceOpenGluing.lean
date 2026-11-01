/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil

The lifted-Yoneda helpers and comparison proof adapt the retained Anthropic/NYLL source:
Copyright 2026 Anthropic, PBC. Released under Apache 2.0.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_LocalRepresentabilityULift.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Earlier Mathlib source:
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/AlgebraicGeometry/Sites/Representability.lean
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
Registered snapshot: external-lean-reuse-snapshots-2026-10-21,
n-yamaguchi-0729--ClassFieldTheory/source/Nyll/SchemeTheory/LocalGeometry/
LocalRepresentabilityULift.lean.
Slice-category adaptation: Worker 336.
-/
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Sites.LocallySurjective

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SliceOpenGluing

variable {S : Scheme.{u}}

abbrev openProperty (S : Scheme.{u}) : MorphismProperty (Over S) :=
  MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (Over.forget S)

theorem openProperty_le_monomorphisms :
    openProperty S ≤ MorphismProperty.monomorphisms (Over S) := by
  intro X Y f hf
  have : _root_.AlgebraicGeometry.IsOpenImmersion f.left := hf
  exact Over.mono_of_mono_left f

lemma relative_monomorphisms_le_monomorphisms :
    (MorphismProperty.monomorphisms (Over S)).relative (schemeYoneda S) ≤
      MorphismProperty.monomorphisms (Presheaf S) := by
  intro F G f hf
  suffices ∀ {X : Over S} {a b : (schemeYoneda S).obj X ⟶ F},
      a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_uliftYoneda (fun _ _ ↦ this (by simp only [Category.assoc, h]))⟩
  intro X a b h
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using (schemeYoneda S).congr_map this =≫ (hf.rep.fst (a ≫ f))
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property_snd (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)),
    Functor.relativelyRepresentable.lift_snd]

variable {F : Presheaf S} {U : Over S} {a : (schemeYoneda S).obj U ⟶ F}

lemma open_mono (ha : (openProperty S).relative (schemeYoneda S) a) : Mono a :=
  relative_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone openProperty_le_monomorphisms _ ha)

lemma fst_self_eq_snd (ha : (openProperty S).relative (schemeYoneda S) a) :
    ha.rep.fst' a = ha.rep.snd a := by
  have := open_mono ha
  apply (schemeYoneda S).map_injective
  rw [← cancel_mono a, (ha.rep.isPullback' a).w]

lemma fst_self_isIso (ha : (openProperty S).relative (schemeYoneda S) a) :
    IsIso (ha.rep.fst' a) := by
  have := open_mono ha
  have := (ha.rep.isPullback' a).isIso_fst_of_mono
  exact (ULiftYoneda.fullyFaithful (Over S)).isIso_of_isIso_map _

variable {I : Type u} {X : I → Over S}
  {f : ∀ i, (schemeYoneda S).obj (X i) ⟶ F}
  (hf : ∀ i, (openProperty S).relative (schemeYoneda S) (f i))

set_option backward.isDefEq.respectTransparency false in
open Functor.relativelyRepresentable in
/-- The actual overlap gluing datum in schemes over the fixed base. -/
def sliceData : CategoryTheory.GlueData (Over S) where
  J := I
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j := by
    have h := (hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip
    exact openProperty_le_monomorphisms _ h
  f_id i := fst_self_isIso (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by
    apply (hf i).rep.hom_ext' <;> simp [fst_self_eq_snd (hf i)]
  t' i j k := lift₃ _ _ _ (pullback₃.p₂ _ _ _) (pullback₃.p₃ _ _ _)
    (pullback₃.p₁ _ _ _) (by simp) (by simp)
  t_fac i j k := (hf j).rep.hom_ext' (by simp) (by simp)
  cocycle i j k := pullback₃.hom_ext (by simp) (by simp) (by simp)

/-- Forget the base for actual scheme gluing; the overlap maps remain open immersions. -/
def schemeData : Scheme.GlueData where
  toGlueData := (sliceData hf).mapGlueData (Over.forget S)
  f_open i j := (hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip

set_option backward.isDefEq.respectTransparency false in
/-- The structure map to the original base descends along the scheme gluing. -/
def structureMap : (schemeData hf).glued ⟶ S := by
  fapply Multicoequalizer.desc
  · exact fun i ↦ (X i).hom
  intro p
  change I × I at p
  rcases p with ⟨i, j⟩
  change ((sliceData hf).f i j).left ≫ (X i).hom =
    (((sliceData hf).t i j).left ≫ ((sliceData hf).f j i).left) ≫ (X j).hom
  calc
    _ = ((sliceData hf).V (i, j)).hom := Over.w _
    _ = ((sliceData hf).t i j).left ≫ ((sliceData hf).V (j, i)).hom :=
      (Over.w _).symm
    _ = ((sliceData hf).t i j).left ≫
        (((sliceData hf).f j i).left ≫ (X j).hom) :=
      congrArg (fun k ↦ ((sliceData hf).t i j).left ≫ k) (Over.w _).symm
    _ = _ := (Category.assoc _ _ _).symm

@[reassoc (attr := simp)]
lemma ι_structureMap (i : I) :
    (schemeData hf).ι i ≫ structureMap hf = (X i).hom :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- The glued scheme as an actual object over the original base. -/
def glued : Over S := Over.mk (structureMap hf)

/-- The original chart inclusions are compatible with the structure maps. -/
def toGlued (i : I) : X i ⟶ glued hf :=
  Over.homMk ((schemeData hf).ι i) (ι_structureMap hf i)

set_option backward.isDefEq.respectTransparency false in
/-- The chart and overlap maps as a pre-hypercover in the slice category. -/
def preOneHypercover : PreOneHypercover (glued hf) where
  I₀ := I
  X := X
  f := toGlued hf
  I₁ _ _ := PUnit
  Y i j _ := (sliceData hf).V (i, j)
  p₁ i j _ := (sliceData hf).f i j
  p₂ i j _ := (sliceData hf).t i j ≫ (sliceData hf).f j i
  w i j _ := by
    apply Over.OverMorphism.ext
    exact ((schemeData hf).glue_condition i j).symm

set_option backward.isDefEq.respectTransparency false in
/-- The open chart family is an actual hypercover for the slice fppf topology. -/
def oneHypercover : (fppfTopology S).OneHypercover (glued hf) where
  toPreOneHypercover := preOneHypercover hf
  mem₀ := by
    change Sieve.ofArrows X (toGlued hf) ∈ (Scheme.fppfTopology.over S) _
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage) _
        (schemeData hf).oneHypercover.mem₀
  mem₁ i j W p₁ p₂ fac := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_preOneHypercover_sieve₁]
    exact (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage) _
        ((schemeData hf).oneHypercover.mem₁ i j p₁.left p₂.left congr($(fac).left))

section Sections

variable {G : FppfSheaf S}
  (s : ∀ i : I, G.obj.obj (op (X i)))
  (h : ∀ i j : I, G.obj.map ((sliceData hf).f i j).op (s i) =
    G.obj.map (((sliceData hf).f j i).op ≫ ((sliceData hf).t i j).op) (s j))

/-- Glue compatible sections using the actual slice fppf hypercover. -/
def sheafValGluedMk : G.obj.obj (op (glued hf)) :=
  Multifork.IsLimit.sectionsEquiv ((oneHypercover hf).isLimitMultifork G)
    { val := s
      property := fun _ ↦ h _ _ }

@[simp]
lemma sheafValGluedMk_val (i : I) :
    G.obj.map (toGlued hf i).op (sheafValGluedMk hf s h) = s i :=
  Multifork.IsLimit.sectionsEquiv_apply_val ((oneHypercover hf).isLimitMultifork G) _ _

end Sections

section Comparison

variable {G : FppfSheaf S} {g : ∀ i : I, (schemeYoneda S).obj (X i) ⟶ G.obj}
  (hg : ∀ i, IsOpenImmersion (g i))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison obtained by gluing the sections supplied by the open charts. -/
def yonedaGluedToSheaf : (schemeSheaf S).obj (glued hg) ⟶ G where
  hom := uliftYonedaEquiv.symm
    (sheafValGluedMk hg (fun i ↦ uliftYonedaEquiv (g i)) (by
      intro i j
      change G.obj.map ((hg i).rep.fst' (g j)).op (uliftYonedaEquiv (g i)) =
        G.obj.map (((hg j).rep.fst' (g i)).op ≫
          ((hg i).rep.symmetry (hg j).rep).op) (uliftYonedaEquiv (g j))
      rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
      congr 1
      rw [← op_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op]
      erw [Functor.relativelyRepresentable.symmetry_fst,
        ((hg i).rep.isPullback' (g j)).w]))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma yoneda_toGlued_yonedaGluedToSheaf (i : I) :
    (schemeYoneda S).map (toGlued hg i) ≫ (yonedaGluedToSheaf hg).hom = g i := by
  apply uliftYonedaEquiv.injective
  have h := uliftYonedaEquiv_naturality (yonedaGluedToSheaf hg).hom (toGlued hg i).op
  erw [← h]
  simp only [yonedaGluedToSheaf]
  erw [Equiv.apply_symm_apply]
  exact sheafValGluedMk_val _ _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma yonedaGluedToSheaf_app_toGlued {i : I} :
    dsimp% (yonedaGluedToSheaf hg).hom.app (op (X i)) ⟨toGlued hg i⟩ =
      uliftYonedaEquiv (g i) := by
  exact (congrArg (fun a : ULift.{u + 1} (X i ⟶ glued hg) ↦
      (yonedaGluedToSheaf hg).hom.app (op (X i)) a)
    (uliftYonedaEquiv_uliftYoneda_map (toGlued hg i))).symm.trans
      ((uliftYonedaEquiv_comp ((schemeYoneda S).map (toGlued hg i))
        (yonedaGluedToSheaf hg).hom).symm.trans
          (congrArg uliftYonedaEquiv (yoneda_toGlued_yonedaGluedToSheaf hg i)))

@[simp]
lemma yonedaGluedToSheaf_app_comp {V U : Over S} (γ : V ⟶ U) (α : U ⟶ glued hg) :
    dsimp% (yonedaGluedToSheaf hg).hom.app (op V) ⟨γ ≫ α⟩ =
      G.obj.map γ.op ((yonedaGluedToSheaf hg).hom.app (op U) ⟨α⟩) :=
  ConcreteCategory.congr_hom ((yonedaGluedToSheaf hg).hom.naturality γ.op) ⟨α⟩

instance [CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc g)] :
    Sheaf.IsLocallySurjective (yonedaGluedToSheaf hg) :=
  CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ (schemeYoneda S).map (toGlued hg i)) ≫
      (yonedaGluedToSheaf hg).hom = Sigma.desc g by
        apply Sigma.hom_ext
        intro i
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun a : (schemeYoneda S).obj (X i) ⟶
              (schemeYoneda S).obj (glued hg) ↦ a ≫ (yonedaGluedToSheaf hg).hom)
            (Sigma.ι_comp_desc (fun i ↦ (schemeYoneda S).map (toGlued hg i)) i)).trans
              ((yoneda_toGlued_yonedaGluedToSheaf hg i).trans
                (Sigma.ι_comp_desc g i).symm)))

set_option backward.isDefEq.respectTransparency false in
/-- Chart maps that define the same sheaf section give the same map to the gluing. -/
lemma comp_toGlued_eq {U : Over S} {i j : I} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : (schemeYoneda S).map a ≫ g i = (schemeYoneda S).map b ≫ g j) :
    a ≫ toGlued hg i = b ≫ toGlued hg j := by
  rw [← (hg i).rep.lift'_fst a b h, Category.assoc]
  conv_rhs => rw [← (hg i).rep.lift'_snd a b h, Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  exact ((schemeData hg).glue_condition i j).symm.trans
    (by
      change ((hg i).rep.symmetry (hg j).rep).left ≫
        ((hg j).rep.fst' (g i)).left ≫ (schemeData hg).ι j =
        ((hg i).rep.snd (g j)).left ≫ (schemeData hg).ι j
      simpa only [Over.comp_left, Category.assoc] using
        congrArg (fun k ↦ k.left ≫ (schemeData hg).ι j)
          (Functor.relativelyRepresentable.symmetry_fst (hg i).rep (hg j).rep))

set_option backward.isDefEq.respectTransparency false in
instance : Sheaf.IsLocallyInjective (yonedaGluedToSheaf hg) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ ⟨α⟩ ⟨β⟩ h
    replace h : (yonedaGluedToSheaf hg).hom.app _ ⟨α⟩ =
        (yonedaGluedToSheaf hg).hom.app _ ⟨β⟩ := h
    have mem : Sieve.ofArrows X (toGlued hg) ∈ (fppfTopology S) (glued hg) :=
      (oneHypercover hg).mem₀
    refine GrothendieckTopology.superset_covering _ ?_
      ((fppfTopology S).intersection_covering ((fppfTopology S).pullback_stable α mem)
        ((fppfTopology S).pullback_stable β mem))
    rintro V (γ : _ ⟶ U) ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩
    change V ⟶ X i at a
    change V ⟶ X j at b
    change a ≫ toGlued hg i = γ ≫ α at fac₁
    change b ≫ toGlued hg j = γ ≫ β at fac₂
    change ULift.up (γ ≫ α) = ULift.up (γ ≫ β)
    replace h : (yonedaGluedToSheaf hg).hom.app _ ⟨γ ≫ α⟩ =
        (yonedaGluedToSheaf hg).hom.app _ ⟨γ ≫ β⟩ :=
      (yonedaGluedToSheaf_app_comp hg γ α).trans
        ((congrArg (fun t ↦ G.obj.map γ.op t) h).trans
          (yonedaGluedToSheaf_app_comp hg γ β).symm)
    rw [← fac₁, ← fac₂] at h ⊢
    apply congrArg ULift.up
    apply comp_toGlued_eq hg
    have hi := (yonedaGluedToSheaf_app_comp hg a (toGlued hg i)).trans
      (congrArg (fun t ↦ G.obj.map a.op t) (yonedaGluedToSheaf_app_toGlued hg (i := i)))
    have hj := (yonedaGluedToSheaf_app_comp hg b (toGlued hg j)).trans
      (congrArg (fun t ↦ G.obj.map b.op t) (yonedaGluedToSheaf_app_toGlued hg (i := j)))
    have hmap := hi.symm.trans (h.trans hj)
    apply uliftYonedaEquiv.injective
    have ha := uliftYonedaEquiv_naturality (X := op (X i)) (g i) a.op
    have hb := uliftYonedaEquiv_naturality (X := op (X j)) (g j) b.op
    exact ha.symm.trans (hmap.trans hb)

variable [CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc g)]

instance : IsIso (yonedaGluedToSheaf hg) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf hg)]
  constructor <;> infer_instance

/-- The actual scheme obtained by gluing represents the original fppf sheaf. -/
def yonedaIsoSheaf : (schemeSheaf S).obj (glued hg) ≅ G :=
  asIso (yonedaGluedToSheaf hg)

include hg in
/-- Open scheme charts that cover an fppf sheaf yield an actual scheme representer. -/
theorem exists_representation :
    ∃ V : Over S, Nonempty ((schemeYoneda S).obj V ≅ G.obj) :=
  ⟨glued hg, ⟨(sheafToPresheaf _ _).mapIso (yonedaIsoSheaf hg)⟩⟩

end Comparison

end Langlands.AlgebraicGeometry.AlgebraicSpace.SliceOpenGluing
