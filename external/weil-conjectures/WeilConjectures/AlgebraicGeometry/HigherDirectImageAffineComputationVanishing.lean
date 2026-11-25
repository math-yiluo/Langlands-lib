/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawLocalClassVanishing
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageTransitionComp

/-! # Affine computation for eventual vanishing of higher direct images

Source: Stacks Project, Tags 09Z1, 03Q8 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- On an affine etale object, a section killed at the limit dies at a later stage.
Source: Stacks Project, Tag 09Z1, proof of lemma-relative-colimit; Tag 03Q8;
Tag 0EZM (blueprint: lem-sbc-higher-direct-image-affine-computation-vanishing).

Proof: Use the natural cohomology-presheaf comparison of Tag 03Q8 at each stage
and at the limit. Locally lift the section to cohomology representatives. Naturality
for the derived adjunction unit and coefficient maps identifies the canonical maps
with the displayed maps. Local injectivity of sheafification refines the cover so that the
limit representatives are zero. Refine by affine etale objects. For each member W,
base change the scheme cone along W -> S: its stages are qcqs since their structure
morphisms to affine W are qcqs, its transitions remain affine, and its cone remains
limiting. Exact inverse image preserves the coefficient colimit and degree-zero
complexes. Apply complex cohomology continuity with lower bound zero. Injectivity
of the colimit comparison and the filtered group colimit equality criterion kill
each representative at a later stage, hence also its sheafification image.
Quasi-compactness of the original affine object gives a finite subcover; directedness
moves all these witnesses to one stage. Naturality restricts its image to zero on
every member, and sheaf separatedness makes the section zero. For p = 0 use ordinary
sections; on the empty affine object separatedness gives zero immediately.
Only the cohomology-group colimit comparison on W is used; no colimit of higher images
is needed.
-/
theorem exists_higherDirectImage_affine_computation_eq_zero {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (V : S.Etale) [IsAffine V.left] (i : I)
    (y : ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (R+(((D.obj (op i)).hom)_*[AddCommGrpCat.{v + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (F i)))).obj.obj (op V))
    (hy : (abelianHigherDirectImageMap (c.π.app (op i)).left
      (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
      (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i)).hom.app (op V) y = 0) :
    ∃ (j : I) (f : i ⟶ j),
      (abelianHigherDirectImageMap (D.map f.op).left (D.obj (op i)).hom
        (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f)).hom.app
          (op V) y = 0 := by
  classical
  let K (a : I) := (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
    (R+(((D.obj (op a)).hom)_*[AddCommGrpCat.{v + 1}]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (F a)))
  let T {a b : I} (f : a ⟶ b) : K a ⟶ K b :=
    abelianHigherDirectImageMap (D.map f.op).left (D.obj (op a)).hom
      (D.obj (op b)).hom (Over.w (D.map f.op)) p (F a) (F b) (φ f)
  have hT {a b d : I} (f : a ⟶ b) (g : b ⟶ d) : T (f ≫ g) = T f ≫ T g :=
    abelianHigherDirectImage_transition_comp D F φ hφid hφcomp p f g
  let R : Sieve V :=
    { arrows := fun W q ↦ ∃ (j : I) (f : i ⟶ j),
        (T f).hom.app (op W) ((K i).obj.map q.op y) = 0
      downward_closed := by
        intro W Z q hq b
        obtain ⟨j, f, hf⟩ := hq
        refine ⟨j, f, ?_⟩
        rw [op_comp, (K i).obj.map_comp]
        change (T f).hom.app (op Z)
          ((K i).obj.map b.op ((K i).obj.map q.op y)) = 0
        rw [NatTrans.naturality_apply, hf, map_zero] }
  obtain ⟨e, he⟩ := exists_abelianHigherDirectImage_natural_comparison S p
  let P := abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)
  let τ := toSheafify S.smallEtaleTopology P ≫ (e (D.obj (op i)).hom (F i)).hom.hom
  have hR : R ∈ S.smallEtaleTopology V := by
    apply S.smallEtaleTopology.transitive
      (Presheaf.imageSieve_mem S.smallEtaleTopology τ y) R
    intro U q hq
    obtain ⟨z, hz⟩ := hq
    let t := abelianHigherDirectImageRawPullback (c.π.app (op i)).left
      (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p (F i)
      (colimit H) ((eH i).inv ≫ colimit.ι H i) U z
    have ht : (toSheafify S.smallEtaleTopology
        (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H))).app (op U) t = 0 := by
      have hzero := he (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
        (Over.w (c.π.app (op i))) (F i) (colimit H)
        ((eH i).inv ≫ colimit.ι H i) U z
      have hnat : (abelianHigherDirectImageMap (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
          (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i)).hom.app (op U)
            ((K i).obj.map q.op y) = 0 := by
        rw [NatTrans.naturality_apply, hy, map_zero]
      change _ = (e c.pt.hom (colimit H)).hom.hom.app (op U)
        ((toSheafify S.smallEtaleTopology
          (abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H))).app (op U) t)
        at hzero
      rw [show (toSheafify S.smallEtaleTopology P ≫
          (e (D.obj (op i)).hom (F i)).hom.hom).app (op U) z =
          (K i).obj.map q.op y from hz, hnat] at hzero
      exact (ConcreteCategory.bijective_of_isIso
        ((e c.pt.hom (colimit H)).hom.hom.app (op U))).injective
          (hzero.symm.trans (map_zero _).symm)
    obtain ⟨Q, hQ, hlocal⟩ := exists_higherDirectImage_raw_local_class_eq_zero
      D c hc F φ hφid hφcomp H eH hH p U i z ht
    apply S.smallEtaleTopology.superset_covering _ hQ
    intro W b hb
    obtain ⟨j, f, hf⟩ := hlocal W b hb
    change ∃ (j : I) (f : i ⟶ j),
      (T f).hom.app (op W) ((K i).obj.map (b ≫ q).op y) = 0
    refine ⟨j, f, ?_⟩
    have hz' : τ.app (op W) (P.map b.op z) =
        (K i).obj.map (b ≫ q).op y := by
      rw [NatTrans.naturality_apply, hz, op_comp, (K i).obj.map_comp]
      rfl
    rw [← hz']
    change (abelianHigherDirectImageMap (D.map f.op).left (D.obj (op i)).hom
      (D.obj (op j)).hom (Over.w (D.map f.op)) p (F i) (F j) (φ f)).hom.app (op W)
        ((toSheafify S.smallEtaleTopology P ≫
          (e (D.obj (op i)).hom (F i)).hom.hom).app (op W) (P.map b.op z)) = 0
    rw [he, hf]
    exact map_zero _
  let A := R.arrows.category
  let W (a : A) : S.Etale := a.obj.left
  let q (a : A) : W a ⟶ V := a.obj.hom
  have hq : Sieve.ofArrows W q ∈ S.smallEtaleTopology V := by
    rw [show Sieve.ofArrows W q = R from Sieve.ofArrows_category R]
    exact hR
  have hcover := (Scheme.ofArrows_mem_smallEtaleTopology_iff q).mp hq
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun a ↦ Set.range (q a).left)
    (fun a ↦ (q a).left.isOpenMap.isOpen_range) (by rw [hcover])
  have htcover : Sieve.ofArrows (fun a : t ↦ W a.val) (fun a : t ↦ q a.val) ∈
      S.smallEtaleTopology V := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hx⟩
  have hzero : ∀ a : t, ∃ (j : I) (f : i ⟶ j),
      (T f).hom.app (op (W a.val)) ((K i).obj.map (q a.val).op y) = 0 := by
    intro a
    exact a.val.property
  choose j f hf using hzero
  obtain ⟨l, g, b, hb⟩ := IsFiltered.wideSpan f
  have hres : ∀ a : t, (K l).obj.map (q a.val).op
      ((T g).hom.app (op V) y) = 0 := by
    intro a
    have hnat := congrArg (fun k ↦ k y) ((T g).hom.naturality (q a.val).op)
    simp only [AddCommGrpCat.comp_apply] at hnat
    rw [← hnat, ← hb a, hT]
    change (T (b a)).hom.app (op (W a.val))
      ((T (f a)).hom.app (op (W a.val)) ((K i).obj.map (q a.val).op y)) = 0
    rw [hf a, map_zero]
  refine ⟨l, g, ?_⟩
  let a : AddCommGrpCat.of (ULift.{v + 1} ℤ) ⟶ (K l).obj.obj (op V) :=
    AddCommGrpCat.ofHom
      { toFun := fun n ↦ n.down • ((T g).hom.app (op V) y)
        map_zero' := zero_zsmul _
        map_add' := fun m n ↦ add_zsmul _ _ _ }
  have ha : a = 0 := by
    apply (K l).property.hom_ext_ofArrows (fun a : t ↦ q a.val) htcover
    intro a
    rw [Limits.zero_comp]
    ext n
    change (K l).obj.map (q a.val).op (n.down • ((T g).hom.app (op V) y)) = 0
    rw [map_zsmul, hres a, zsmul_zero]
  have h := congrArg (fun k ↦ k (ULift.up (1 : ℤ))) ha
  change (1 : ℤ) • ((T g).hom.app (op V) y) = 0 at h
  simpa only [one_zsmul] using h

end AlgebraicGeometry.Etale
