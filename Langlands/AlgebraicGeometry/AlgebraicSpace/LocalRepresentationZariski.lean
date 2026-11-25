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

Registered snapshot: external-lean-reuse-snapshots-2026-10-21,
n-yamaguchi-0729--ClassFieldTheory/source/Nyll/SchemeTheory/LocalGeometry/
LocalRepresentabilityULift.lean.
Slice-category adaptation: Langlands-lib.
-/
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties

/-! # Gluing local scheme representations of a Zariski sheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SliceOpenGluing.Zariski

variable {S : Scheme.{u}} {F : Presheaf S} {I : Type u} {X : I → Over S}
    {f : ∀ i, (schemeYoneda S).obj (X i) ⟶ F}
    (hf : ∀ i, (openProperty S).relative (schemeYoneda S) (f i))

/-- The existing actual open-scheme gluing is a hypercover already for the
big Zariski topology on the slice. -/
def oneHypercover : (Scheme.zariskiTopology.over S).OneHypercover (glued hf) where
  toPreOneHypercover := preOneHypercover hf
  mem₀ := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (schemeData hf).oneHypercover.mem₀
  mem₁ i j W p₁ p₂ fac := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_preOneHypercover_sieve₁]
    exact (schemeData hf).oneHypercover.mem₁ i j p₁.left p₂.left congr($(fac).left)

section Sections

variable {G : Sheaf (Scheme.zariskiTopology.over S) (Type (u + 1))}
  (s : ∀ i : I, G.obj.obj (op (X i)))
  (h : ∀ i j : I, G.obj.map ((sliceData hf).f i j).op (s i) =
    G.obj.map (((sliceData hf).f j i).op ≫ ((sliceData hf).t i j).op) (s j))

/-- Glue compatible sections using the actual slice Zariski hypercover. -/
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

variable {G : Sheaf (Scheme.zariskiTopology.over S) (Type (u + 1))} {g : ∀ i : I, (schemeYoneda S).obj (X i) ⟶ G.obj}
  (hg : ∀ i, IsOpenImmersion (g i))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison obtained by gluing the sections supplied by the open charts. -/
def yonedaGluedToSheaf : (GrothendieckTopology.uliftYoneda.{u + 1} (Scheme.zariskiTopology.over S)).obj (glued hg) ⟶ G where
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

instance [CategoryTheory.Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) (Sigma.desc g)] :
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
    have mem : Sieve.ofArrows X (toGlued hg) ∈ (Scheme.zariskiTopology.over S) (glued hg) :=
      (oneHypercover hg).mem₀
    refine GrothendieckTopology.superset_covering _ ?_
      ((Scheme.zariskiTopology.over S).intersection_covering ((Scheme.zariskiTopology.over S).pullback_stable α mem)
        ((Scheme.zariskiTopology.over S).pullback_stable β mem))
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

variable [CategoryTheory.Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) (Sigma.desc g)]

instance : IsIso (yonedaGluedToSheaf hg) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf hg)]
  constructor <;> infer_instance

/-- The actual scheme obtained by gluing represents the original Zariski sheaf. -/
def yonedaIsoSheaf : (GrothendieckTopology.uliftYoneda.{u + 1} (Scheme.zariskiTopology.over S)).obj (glued hg) ≅ G :=
  asIso (yonedaGluedToSheaf hg)

include hg in
/-- Open scheme charts that cover a Zariski sheaf yield an actual scheme representer. -/
theorem exists_representation :
    ∃ V : Over S, Nonempty ((schemeYoneda S).obj V ≅ G.obj) :=
  ⟨glued hg, ⟨(sheafToPresheaf _ _).mapIso (yonedaIsoSheaf hg)⟩⟩

end Comparison

end SliceOpenGluing.Zariski

namespace LocalRepresentation

variable {B : Scheme.{u}} {F : Presheaf B}

/-- The base open cover is covering in the big Zariski slice topology. -/
lemma baseCoverSieve_mem_zariski (𝒰 : Scheme.OpenCover.{u} B) :
    baseCoverSieve 𝒰 ∈ (Scheme.zariskiTopology.over B) (Over.mk (𝟙 B)) := by
  rw [GrothendieckTopology.mem_over_iff]
  change Sieve.overEquiv _ (Sieve.ofArrows _ _) ∈ Scheme.zariskiTopology _
  rw [Sieve.overEquiv_ofArrows]
  exact 𝒰.mem_grothendieckTopology

/-- Local representatives over a base open cover cover the original presheaf. -/
theorem charts_locallySurjective_zariski (𝒰 : Scheme.OpenCover.{u} B) (H : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅ (Over.map (𝒰.f i)).op ⋙ F) :
    CategoryTheory.Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over B)
      (Sigma.desc (fun i ↦ chart (𝒰.f i) (H i) (e i))) where
  imageSieve_mem {Z} x := by
    let q : Z ⟶ Over.mk (𝟙 B) := Over.homMk Z.hom (by simp)
    refine (Scheme.zariskiTopology.over B).superset_covering ?_
      ((Scheme.zariskiTopology.over B).pullback_stable q (baseCoverSieve_mem_zariski 𝒰))
    intro W k hk
    obtain ⟨i, α, _⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hk
    obtain ⟨t, ht⟩ := (chartToProduct_bijective (𝒰.f i) (H i) (e i) W).surjective
      (F.map k.op x, ⟨α⟩)
    refine ⟨(Sigma.ι (fun i ↦ (schemeYoneda B).obj ((Over.map (𝒰.f i)).obj (H i))) i).app
      (op W) t, ?_⟩
    have hι := congrArg (fun η ↦ η.app (op W) t)
      (Sigma.ι_comp_desc (fun i ↦ chart (𝒰.f i) (H i) (e i)) i)
    exact hι.trans (congrArg Prod.fst ht)

/-- A sheaf with scheme representatives over an open cover is represented by a scheme. -/
theorem exists_representation_zariski (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over B) F)
    (𝒰 : Scheme.OpenCover.{u} B) (H : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅ (Over.map (𝒰.f i)).op ⋙ F) :
    ∃ V : Over B, Nonempty ((schemeYoneda B).obj V ≅ F) := by
  let G : Sheaf (Scheme.zariskiTopology.over B) (Type (u + 1)) := ⟨F, hF⟩
  have := charts_locallySurjective_zariski 𝒰 H e
  exact SliceOpenGluing.Zariski.exists_representation (G := G)
    (fun i ↦ chart_isOpenImmersion (𝒰.f i) (H i) (e i))

end LocalRepresentation

end Langlands.AlgebraicGeometry.AlgebraicSpace
