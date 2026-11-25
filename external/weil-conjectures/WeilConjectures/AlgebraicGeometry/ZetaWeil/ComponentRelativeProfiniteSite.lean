/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.ProEtaleCoefficients.ConnectedComponentsProfinite
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Topology.Category.Profinite.Limits
import WeilConjectures.AlgebraicGeometry.ZetaWeil.StalkIsomorphismLifting
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteFunctorExtension
import WeilConjectures.CategoryTheory.RingObjects.Condensed.RelativeFiniteProfinitePresentation
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import WeilConjectures.AlgebraicGeometry.Affine.AffineComponentSiteProjection

/-!
# Relative profinite tests over an affine scheme's component space

Source: Hemo--Richarz--Scholbach, paragraph preceding (4.1) and its factorization sentence;
Bhatt--Scholze, proof and more precise statement of Lemma 2.2.8
(blueprint: lem-zl-component-relative-profinite-site).

The functor in the theorem is specified by a universal property, not by an arbitrary
choice of affine schemes. Its finite stages are coproducts of actual restricted open
subschemes. Its image of every finite-clopen presentation is a limit cone over the base.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology

namespace AlgebraicGeometry.ProEtale

/-- The quotient by connected components, with its quotient topology, bundled as profinite.
Source: Hemo--Richarz--Scholbach, before (4.1); Stacks, Tag 0906
(blueprint: lem-zl-component-relative-profinite-site). -/
def affineComponentSpace (T : Scheme.{u}) [IsAffine T] : Profinite.{u} := by
  letI : SpectralSpace T := {}
  exact @Profinite.of (ConnectedComponents T) _
    (spectralSpace_connectedComponents_profinite (T := T)).1
    (spectralSpace_connectedComponents_profinite (T := T)).2.1
    (spectralSpace_connectedComponents_profinite (T := T)).2.2

/-- A finite stage over the component space: pull back a map of finite sets along a
finite clopen quotient of the base. The quotient's surjectivity is imposed in the theorem.
Source: Hemo--Richarz--Scholbach, before (4.1); Bhatt--Scholze, Lemma 2.2.8, proof
(blueprint: lem-zl-component-relative-profinite-site). -/
noncomputable def componentFiniteStage {S : Profinite.{u}} (A C : FintypeCat.{u})
    (q : S ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C) : Over S :=
  Over.mk (pullback.fst q (FintypeCat.toProfinite.map f))

/-- Exactly the allowed finite stages, including isomorphic presentations.
Source: Hemo--Richarz--Scholbach, before (4.1); Bhatt--Scholze, Lemma 2.2.8, proof
(blueprint: lem-zl-component-relative-profinite-site). -/
def IsComponentFiniteStage {S : Profinite.{u}} (E : Over S) : Prop :=
  ∃ (A C : FintypeCat.{u}) (q : S ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C),
    Function.Surjective q ∧ Nonempty (E ≅ componentFiniteStage A C q f)

/-- The open-and-closed part of the affine base belonging to one finite block. Its
associated scheme carries the restriction of the structure sheaf, via `Scheme.Opens`.
Source: Hemo--Richarz--Scholbach, before (4.1); Bhatt--Scholze, Lemma 2.2.8, proof
(blueprint: lem-zl-component-relative-profinite-site). -/
def componentFiniteOpen (T : Scheme.{u}) [IsAffine T] (A C : FintypeCat.{u})
    (q : affineComponentSpace T ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C)
    (a : A) : T.Opens :=
  ⟨{t | q (ConnectedComponents.mk t) = f a},
    (isOpen_discrete ({f a} : Set (FintypeCat.toProfinite.obj C))).preimage
      (q.hom.hom.continuous.comp ConnectedComponents.continuous_coe)⟩

/-- The finite scheme stage is the disjoint union of the actual clopen subschemes,
including repeated blocks as separate copies and the empty coproduct.
Source: Hemo--Richarz--Scholbach, before (4.1); Bhatt--Scholze, Lemma 2.2.8, proof
(blueprint: lem-zl-component-relative-profinite-site). -/
noncomputable def componentFiniteScheme (T : Scheme.{u}) [IsAffine T]
    (A C : FintypeCat.{u})
    (q : affineComponentSpace T ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C) : Over T :=
  ∐ fun a : A => Over.mk (componentFiniteOpen T A C q f a).ι

set_option backward.isDefEq.respectTransparency false in
/-- The pullback topology and stalkwise isomorphisms give the relative universal
mapping property, including maps from arbitrary schemes over the base.

Source: Bhatt--Scholze, the more precise statement following Lemma 2.2.8
(blueprint: lem-zl-component-relative-profinite-site).

Proof: pair the given coordinate with the map to the base, apply the inverse pullback
homeomorphism, and lift the resulting continuous map by stalk-isomorphism lifting.
Equality of both coordinates gives uniqueness. -/
theorem component_mapping_property (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left))
    (hF : ∀ E : Over (affineComponentSpace T),
      (∀ x : (F.obj E).left, IsIso ((F.obj E).hom.stalkMap x)) ∧
      ∃ h : (F.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x)) :
    (∀ (E : Over (affineComponentSpace T)) (x : (F.obj E).left),
      E.hom (p E x) = ConnectedComponents.mk ((F.obj E).hom x)) ∧
    ∀ (W : Over T) (E : Over (affineComponentSpace T)) (g : C(W.left, E.left)),
      (∀ w : W.left, E.hom (g w) = ConnectedComponents.mk (W.hom w)) →
      ∃! m : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E),
        ∀ w : W.left, p E (m.left w) = g w := by
  classical
  constructor
  · intro E x
    obtain ⟨h, ht, hp⟩ := (hF E).2
    simpa only [ht, hp] using (h x).property.symm
  · intro W E g hg
    obtain ⟨h, ht, hp⟩ := (hF E).2
    let a : W.left.toTopCat ⟶ (F.obj E).left.toTopCat := TopCat.ofHom
      ⟨fun w ↦ h.symm ⟨(W.hom w, g w), (hg w).symm⟩,
        h.symm.continuous.comp ((W.hom.continuous.prodMk g.continuous).subtype_mk _)⟩
    have ha : a ≫ (F.obj E).hom.base = W.hom.base := by
      ext w
      exact (ht _).symm.trans (congrArg (fun z ↦ z.val.1) (h.apply_symm_apply _))
    obtain ⟨m, ⟨hm, hmt⟩, hmuniq⟩ :=
      Scheme.existsUnique_lift_of_stalkMap_isIso (F.obj E).hom (hF E).1 W.hom a ha
    refine ⟨Over.homMk m hmt, ?_, ?_⟩
    · intro w
      change p E (m w) = g w
      erw [← hp]
      have hw := ConcreteCategory.congr_hom hm w
      exact congrArg (fun z ↦ z.val.2) ((congrArg h hw).trans (h.apply_symm_apply _))
    · intro n hn
      apply Over.OverMorphism.ext
      apply (hmuniq n.left ⟨?_, n.w⟩)
      ext w
      apply h.injective
      have hwa : h (a w) = ⟨(W.hom w, g w), (hg w).symm⟩ :=
        h.apply_symm_apply _
      apply Subtype.ext
      apply Prod.ext
      · erw [ht]
        exact (congrArg (fun l ↦ l w) n.w).trans
          (congrArg (fun z ↦ z.val.1) hwa).symm
      · erw [hp, hn]
        exact (congrArg (fun z ↦ z.val.2) hwa).symm

set_option backward.isDefEq.respectTransparency false in
private theorem component_joint_surjective (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left))
    (hF : ∀ E : Over (affineComponentSpace T),
      ∃ h : (F.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x))
    (hnat : ∀ (E E' : Over (affineComponentSpace T)) (a : E ⟶ E')
      (x : (F.obj E).left), p E' ((F.map a).left x) = a.left (p E x))
    {A : Type u} (E : A → Over (affineComponentSpace T))
    (E₀ : Over (affineComponentSpace T)) (f : ∀ a, E a ⟶ E₀)
    (hf : ∀ x : E₀.left, ∃ (a : A) (y : (E a).left), (f a).left y = x) :
    ∀ x : (F.obj E₀).left, ∃ (a : A) (y : (F.obj (E a)).left),
      (F.map (f a)).left y = x := by
  classical
  intro x
  obtain ⟨h₀, ht₀, hp₀⟩ := hF E₀
  obtain ⟨a, y, hy⟩ := hf (p E₀ x)
  obtain ⟨h, ht, hp⟩ := hF (E a)
  have hw : ConnectedComponents.mk ((F.obj E₀).hom x) = (E a).hom y := by
    erw [← ht₀]
    exact (h₀ x).property.trans ((congrArg E₀.hom (hp₀ x)).trans
      ((congrArg E₀.hom hy.symm).trans (ConcreteCategory.congr_hom (f a).w y)))
  let z := h.symm ⟨((F.obj E₀).hom x, y), hw⟩
  have hz₁ : (F.obj (E a)).hom z = (F.obj E₀).hom x :=
    (ht z).symm.trans (congrArg (fun z ↦ z.val.1) (h.apply_symm_apply _))
  have hz₂ : p (E a) z = y :=
    (hp z).symm.trans (congrArg (fun z ↦ z.val.2) (h.apply_symm_apply _))
  refine ⟨a, z, h₀.injective ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · erw [ht₀, ht₀]
    exact (congrArg (fun l ↦ l z) (F.map (f a)).w).trans hz₁
  · erw [hp₀, hp₀, hnat, hz₂, hy]

set_option backward.isDefEq.respectTransparency false in
private theorem component_map_open_immersion (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left))
    (hF : ∀ E : Over (affineComponentSpace T),
      (∀ x : (F.obj E).left, IsIso ((F.obj E).hom.stalkMap x)) ∧
      ∃ h : (F.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x))
    (hnat : ∀ (E E' : Over (affineComponentSpace T)) (a : E ⟶ E')
      (x : (F.obj E).left), p E' ((F.map a).left x) = a.left (p E x))
    {E E' : Over (affineComponentSpace T)} (a : E ⟶ E')
    (ha : IsOpenEmbedding a.left) : IsOpenImmersion (F.map a).left := by
  classical
  obtain ⟨h, ht, hpt⟩ := (hF E).2
  obtain ⟨h', ht', hpt'⟩ := (hF E').2
  let P : Set (T × E.left) := {z | ConnectedComponents.mk z.1 = E.hom z.2}
  let P' : Set (T × E'.left) := {z | ConnectedComponents.mk z.1 = E'.hom z.2}
  let b : T × E.left → T × E'.left := fun z ↦ (z.1, a.left z.2)
  have hb : IsOpenEmbedding b := IsOpenEmbedding.id.prodMap ha
  have heq : b ⁻¹' P' = P := by
    ext z
    change (ConnectedComponents.mk z.1 = E'.hom (a.left z.2)) ↔ _
    erw [ConcreteCategory.congr_hom a.w z.2]
    rfl
  let e : P ≃ₜ b ⁻¹' P' := Homeomorph.setCongr heq.symm
  let b' : P → P' := fun z ↦ ⟨b z, by
    change ConnectedComponents.mk z.val.1 = E'.hom (a.left z.val.2)
    erw [ConcreteCategory.congr_hom a.w z.val.2]
    exact z.property⟩
  have hb' : IsOpenEmbedding b' := (hb.restrictPreimage P').comp e.isOpenEmbedding
  have hcomm : (fun x : (F.obj E).left ↦ (F.map a).left x) =
      h'.symm ∘ b' ∘ h := by
    funext x
    apply h'.injective
    erw [h'.apply_symm_apply]
    apply Subtype.ext
    exact Prod.ext ((ht' _).trans
      ((congrArg (fun l ↦ l x) (F.map a).w).trans (ht x).symm))
      ((hpt' _).trans ((hnat E E' a x).trans (congrArg a.left (hpt x).symm)))
  have hopen : IsOpenEmbedding (F.map a).left := by
    exact (congrArg (fun k : (F.obj E).left → (F.obj E').left ↦
      IsOpenEmbedding k) hcomm).mpr
        (h'.symm.isOpenEmbedding.comp (hb'.comp h.isOpenEmbedding))
  have (x : (F.obj E).left) : IsIso ((F.map a).left.stalkMap x) := by
    have := (hF E).1 x
    have := (hF E').1 ((F.map a).left x)
    have hc : IsIso (((F.map a).left ≫ (F.obj E').hom).stalkMap x) := by
      have hw : (F.map a).left ≫ (F.obj E').hom = (F.obj E).hom := (F.map a).w
      exact (congrArg (fun l : (F.obj E).left ⟶ T ↦ IsIso (l.stalkMap x)) hw).mpr
        ((hF E).1 x)
    have : IsIso ((F.obj E').hom.stalkMap ((F.map a).left x) ≫
        (F.map a).left.stalkMap x) := by
      erw [← Scheme.Hom.stalkMap_comp]
      exact hc
    exact IsIso.of_isIso_comp_left ((F.obj E').hom.stalkMap ((F.map a).left x)) _
  exact IsOpenImmersion.of_isIso_stalkMap _ hopen

set_option backward.isDefEq.respectTransparency false in
private theorem component_preserves_coproducts (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left))
    (hF : ∀ E : Over (affineComponentSpace T),
      (∀ x : (F.obj E).left, IsIso ((F.obj E).hom.stalkMap x)) ∧
      ∃ h : (F.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x))
    (hnat : ∀ (E E' : Over (affineComponentSpace T)) (a : E ⟶ E')
      (x : (F.obj E).left), p E' ((F.map a).left x) = a.left (p E x))
    (A : Type u) [Finite A] : PreservesColimitsOfShape (Discrete A) F := by
  classical
  let S := affineComponentSpace T
  have hpres (E : A → Over S) : PreservesColimit (Discrete.functor E) F := by
    let B : Over S := Over.mk
      (CompHausLike.finiteCoproduct.desc (fun a ↦ (E a).left) (fun a ↦ (E a).hom))
    let j (a : A) : E a ⟶ B :=
      Over.homMk (CompHausLike.finiteCoproduct.ι (fun a ↦ (E a).left) a) (by rfl)
    have hc : IsColimit (Cofan.mk B j) := by
      apply isColimitOfIsColimitCofanMkObj (Over.forget S) E j
      exact CompHausLike.finiteCoproduct.isColimit (fun a ↦ (E a).left)
    have hj (a : A) : IsOpenImmersion (F.map (j a)).left :=
      component_map_open_immersion T F p hF hnat (j a)
        (CompHausLike.finiteCoproduct.isOpenEmbedding_ι _ a)
    have hc' : Nonempty (IsColimit
        (Cofan.mk (F.obj B).left (fun a ↦ (F.map (j a)).left))) := by
      have (a : A) := hj a
      apply nonempty_isColimit_cofanMk_of
      · apply top_unique
        intro x hx
        obtain ⟨a, y, rfl⟩ := component_joint_surjective T F p (fun E ↦ (hF E).2)
          hnat E B j (fun z ↦ ⟨z.1, z.2, rfl⟩) x
        exact (le_iSup (fun a ↦ (F.map (j a)).left.opensRange) a)
          (by exact ⟨y, rfl⟩)
      · intro a b hab
        apply disjoint_iff_inf_le.mpr
        intro x hx
        obtain ⟨y, hy⟩ := hx.1
        obtain ⟨z, hz⟩ := hx.2
        have he := congrArg (p B) (hy.trans hz.symm)
        erw [hnat, hnat] at he
        exact hab (congrArg Sigma.fst he)
    have hcF : IsColimit (F.mapCocone (Cofan.mk B j)) := by
      refine (isColimitMapCoconeCofanMkEquiv F E j).symm ?_
      exact isColimitOfIsColimitCofanMkObj
        (Scheme.ProEt.forget T ⋙ Over.forget T) (fun a ↦ F.obj (E a))
        (fun a ↦ F.map (j a)) hc'.some
    exact preservesColimit_of_preserves_colimit_cocone hc hcF
  constructor
  intro D
  have := hpres (fun a ↦ D.obj ⟨a⟩)
  exact preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor (F := D)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem component_preserves_limits (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left))
    (hp : ∀ (E : Over (affineComponentSpace T)) (x : (F.obj E).left),
      E.hom (p E x) = ConnectedComponents.mk ((F.obj E).hom x))
    (hnat : ∀ (E E' : Over (affineComponentSpace T)) (a : E ⟶ E')
      (x : (F.obj E).left), p E' ((F.map a).left x) = a.left (p E x))
    (hmap : ∀ (W : Over T) (E : Over (affineComponentSpace T)) (g : C(W.left, E.left)),
      (∀ w : W.left, E.hom (g w) = ConnectedComponents.mk (W.hom w)) →
      ∃! m : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E),
        ∀ w : W.left, p E (m.left w) = g w)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over (affineComponentSpace T))
    (c : Cone D) (hc : IsLimit c) :
    Nonempty (IsLimit ((F ⋙ Scheme.ProEt.forget T).mapCone c)) := by
  classical
  let H := Over.post (X := affineComponentSpace T) Profinite.toTopCat
  have : H.IsRightAdjoint := inferInstance
  let htop := isLimitOfPreserves H hc
  let liftCone (s : Cone (D ⋙ F ⋙ Scheme.ProEt.forget T)) : Cone (D ⋙ H) :=
    { pt := Over.mk (TopCat.ofHom
        ⟨fun w ↦ ConnectedComponents.mk (s.pt.hom w),
          ConnectedComponents.continuous_coe.comp s.pt.hom.continuous⟩)
      π :=
        { app := fun i ↦ Over.homMk
            (TopCat.ofHom ((p (D.obj i)).comp ⟨(s.π.app i).left,
              (s.π.app i).left.continuous⟩)) (by
                ext w
                exact (hp _ _).trans (congrArg ConnectedComponents.mk
                  (congrArg (fun l ↦ l w) (s.π.app i).w)))
          naturality := fun i j a ↦ by
            ext w
            change p (D.obj j) ((s.π.app j).left w) =
              (D.map a).left (p (D.obj i) ((s.π.app i).left w))
            erw [← hnat]
            exact (congrArg (p _) (congrArg (fun k ↦ k.left w) (s.w a))).symm } }
  let g (s : Cone (D ⋙ F ⋙ Scheme.ProEt.forget T)) : C(s.pt.left, c.pt.left) :=
    (htop.lift (liftCone s)).left.hom
  have hg (s : Cone (D ⋙ F ⋙ Scheme.ProEt.forget T)) (w : s.pt.left) :
      c.pt.hom (g s w) = ConnectedComponents.mk (s.pt.hom w) :=
    ConcreteCategory.congr_hom (htop.lift (liftCone s)).w w
  let m (s : Cone (D ⋙ F ⋙ Scheme.ProEt.forget T)) := (hmap s.pt c.pt (g s) (hg s)).choose
  have hm (s : Cone (D ⋙ F ⋙ Scheme.ProEt.forget T)) :
      ∀ w : s.pt.left, p c.pt ((m s).left w) = g s w :=
    (hmap s.pt c.pt (g s) (hg s)).choose_spec.1
  have extmap (W : Over T) (E : Over (affineComponentSpace T))
      (a b : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E))
      (hab : ∀ w, p E (a.left w) = p E (b.left w)) : a = b := by
    let g' : C(W.left, E.left) := (p E).comp ⟨b.left, b.left.continuous⟩
    have hg' (w : W.left) : E.hom (g' w) = ConnectedComponents.mk (W.hom w) :=
      (hp E _).trans (congrArg ConnectedComponents.mk (congrArg (fun l ↦ l w) b.w))
    exact ((hmap W E g' hg').unique hab (fun _ ↦ rfl))
  refine ⟨{ lift := m, fac := ?_, uniq := ?_ }⟩
  · intro s i
    apply extmap
    intro w
    change p (D.obj i) ((F.map (c.π.app i)).left ((m s).left w)) =
      p (D.obj i) ((s.π.app i).left w)
    erw [hnat, hm]
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.left) (htop.fac (liftCone s) i)) w
  · intro s n hn
    apply extmap
    intro w
    have ht : (Over.homMk (TopCat.ofHom ((p c.pt).comp
        ⟨n.left, n.left.continuous⟩)) (by
          ext w
          exact (hp _ _).trans (congrArg ConnectedComponents.mk
            (congrArg (fun l ↦ l w) n.w))) : (liftCone s).pt ⟶ H.obj c.pt) =
        htop.lift (liftCone s) := by
      apply htop.uniq
      intro i
      ext x
      change (c.π.app i).left (p c.pt (n.left x)) =
        p (D.obj i) ((s.π.app i).left x)
      erw [← hnat]
      exact congrArg (p _) (congrArg (fun k ↦ k.left x) (hn i))
    exact (ConcreteCategory.congr_hom (congrArg (fun k ↦ k.left) ht) w).trans (hm s w).symm

set_option backward.isDefEq.respectTransparency false in
private theorem component_finite_comparison (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left))
    (hF : ∀ E : Over (affineComponentSpace T),
      (∀ x : (F.obj E).left, IsIso ((F.obj E).hom.stalkMap x)) ∧
      ∃ h : (F.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x))
    (hp : ∀ (E : Over (affineComponentSpace T)) (x : (F.obj E).left),
      E.hom (p E x) = ConnectedComponents.mk ((F.obj E).hom x))
    (hmap : ∀ (W : Over T) (E : Over (affineComponentSpace T)) (g : C(W.left, E.left)),
      (∀ w : W.left, E.hom (g w) = ConnectedComponents.mk (W.hom w)) →
      ∃! m : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E),
        ∀ w : W.left, p E (m.left w) = g w)
    (A C : FintypeCat.{u}) (q : affineComponentSpace T ⟶ FintypeCat.toProfinite.obj C)
    (f : A ⟶ C) :
    Nonempty ((Scheme.ProEt.forget T).obj (F.obj (componentFiniteStage A C q f)) ≅
      componentFiniteScheme T A C q f) := by
  classical
  let E := componentFiniteStage A C q f
  let U (a : A) := componentFiniteOpen T A C q f a
  let e : E.left ≅ CompHausLike.pullback q (FintypeCat.toProfinite.map f) :=
    (pullback.isLimit q (FintypeCat.toProfinite.map f)).conePointUniqueUpToIso
      (CompHausLike.pullback.isLimit q (FintypeCat.toProfinite.map f))
  let eh := CompHausLike.homeoOfIso e
  have efst (x : E.left) : (eh x).val.1 = E.hom x :=
    by
      exact ConcreteCategory.congr_hom
        ((pullback.isLimit q (FintypeCat.toProfinite.map f)).conePointUniqueUpToIso_hom_comp
          (CompHausLike.pullback.isLimit q (FintypeCat.toProfinite.map f)) WalkingCospan.left) x
  let g (a : A) : C((U a).toScheme, E.left) :=
    ⟨fun t ↦ eh.symm ⟨(ConnectedComponents.mk t.val, a), t.property⟩,
      eh.symm.continuous.comp
        ((ConnectedComponents.continuous_coe.comp continuous_subtype_val).prodMk
          continuous_const |>.subtype_mk _)⟩
  have hg (a : A) (w : (U a).toScheme) : E.hom (g a w) =
      ConnectedComponents.mk ((U a).ι w) := by
    erw [← efst]
    exact congrArg (fun z ↦ z.val.1) (eh.apply_symm_apply _)
  let k (a : A) : Over.mk (U a).ι ⟶ (Scheme.ProEt.forget T).obj (F.obj E) :=
    (hmap (Over.mk (U a).ι) E (g a) (hg a)).choose
  have hk (a : A) (w : (U a).toScheme) : p E ((k a).left w) = g a w :=
    (hmap (Over.mk (U a).ι) E (g a) (hg a)).choose_spec.1 w
  let r : C((F.obj E).left, FintypeCat.toProfinite.obj A) :=
    ⟨fun x ↦ (eh (p E x)).val.2,
      continuous_snd.comp (continuous_subtype_val.comp (eh.continuous.comp (p E).continuous))⟩
  have hkr (a : A) (w : (U a).toScheme) : r ((k a).left w) = a := by
    change (eh (p E ((k a).left w))).val.2 = a
    erw [hk]
    exact congrArg (fun z ↦ z.val.2) (eh.apply_symm_apply _)
  have hrange (a : A) : Set.range (k a).left = r ⁻¹' {a} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact hkr a w
    · intro hx
      have hx' : q (ConnectedComponents.mk ((F.obj E).hom x)) = f a := by
        erw [← hp E x, ← efst]
        exact (eh (p E x)).property.trans (congrArg f hx)
      let w : (U a).toScheme := ⟨(F.obj E).hom x, hx'⟩
      refine ⟨w, ?_⟩
      obtain ⟨h, ht, hpt⟩ := (hF E).2
      apply h.injective
      apply Subtype.ext
      apply Prod.ext
      · erw [ht, ht]
        exact congrArg (fun l : (U a).toScheme ⟶ T ↦ l w) (k a).w
      · erw [hpt, hpt, hk]
        apply eh.injective
        erw [show eh (g a w) = ⟨(ConnectedComponents.mk w.val, a), w.property⟩ from
          eh.apply_symm_apply _]
        apply Subtype.ext
        exact Prod.ext ((efst _).trans (hp E x)).symm hx.symm
  have hki (a : A) : IsOpenImmersion (k a).left := by
    have hemb : IsEmbedding (k a).left := IsEmbedding.of_comp
      (k a).left.continuous (F.obj E).hom.continuous (by
        have heq : (fun w : (U a).toScheme ↦ (F.obj E).hom ((k a).left w)) =
            (fun w : (U a).toScheme ↦ (U a).ι w) := by
          funext w
          exact congrArg (fun l : (U a).toScheme ⟶ T ↦ l w) (k a).w
        exact (congrArg (fun l : (U a).toScheme → T ↦ IsEmbedding l) heq).mpr
          (U a).ι.isOpenEmbedding.isEmbedding)
    have hopen : IsOpenEmbedding (k a).left :=
      ⟨hemb, (hrange a).symm ▸
        (isOpen_discrete ({a} : Set (FintypeCat.toProfinite.obj A))).preimage r.continuous⟩
    have (w : (U a).toScheme) : IsIso ((k a).left.stalkMap w) := by
      have := (hF E).1 ((k a).left w)
      have hc : IsIso (((k a).left ≫ (F.obj E).hom).stalkMap w) := by
        have hw : (k a).left ≫ (F.obj E).hom = (U a).ι := (k a).w
        exact (congrArg (fun l : (U a).toScheme ⟶ T ↦ IsIso (l.stalkMap w)) hw).mpr
          (inferInstance : IsIso ((U a).ι.stalkMap w))
      have : IsIso ((F.obj E).hom.stalkMap ((k a).left w) ≫ (k a).left.stalkMap w) := by
        erw [← Scheme.Hom.stalkMap_comp]
        exact hc
      exact IsIso.of_isIso_comp_left ((F.obj E).hom.stalkMap ((k a).left w)) _
    exact IsOpenImmersion.of_isIso_stalkMap _ hopen
  have (a : A) := hki a
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (fun a ↦ (k a).left) (by
      apply top_unique
      intro x hx
      have hx' : x ∈ (k (r x)).left.opensRange := by
        change x ∈ Set.range (k (r x)).left
        erw [hrange]
        rfl
      exact (le_iSup (fun a ↦ (k a).left.opensRange) (r x)) hx') (by
      intro a b hab
      apply disjoint_iff_inf_le.mpr
      intro x hx
      obtain ⟨y, hy⟩ := hx.1
      obtain ⟨z, hz⟩ := hx.2
      exact hab ((hkr a y).symm.trans ((congrArg r (hy.trans hz.symm)).trans (hkr b z))))
  let hcOver : IsColimit (Cofan.mk ((Scheme.ProEt.forget T).obj (F.obj E)) k) :=
    isColimitOfIsColimitCofanMkObj (Over.forget T) (fun a ↦ Over.mk (U a).ι) k hc
  exact ⟨(hcOver.coconePointUniqueUpToIso (coproductIsCoproduct
    (fun a : A ↦ Over.mk (U a).ι)))⟩

private theorem component_coproducts_of_hom_sheaves {D : Type*} [Category* D]
    (F : Profinite.{u} ⥤ D)
    (hF : ∀ Y, Presieve.IsSheaf (extensiveTopology Profinite) (F.op ⋙ yoneda.obj Y))
    (A : Type u) [Finite A] : PreservesColimitsOfShape (Discrete A) F := by
  constructor
  intro K
  constructor
  intro c hc
  constructor
  refine (F.mapCocone c).isColimitYonedaEquiv.symm ?_
  intro Y
  have : PreservesFiniteProducts (F.op ⋙ yoneda.obj Y) :=
    (Presieve.isSheaf_iff_preservesFiniteProducts _).mp (hF Y)
  have : PreservesLimitsOfShape (Discrete A) (F.op ⋙ yoneda.obj Y) := inferInstance
  have : PreservesLimitsOfShape (Discrete A)ᵒᵖ (F.op ⋙ yoneda.obj Y) :=
    preservesLimitsOfShape_of_equiv (Discrete.opposite A).symm _
  exact isLimitOfPreserves (F.op ⋙ yoneda.obj Y) hc.op

private theorem component_coproducts_of_continuous {D : Type*} [Category* D]
    (F : Profinite.{u} ⥤ D) (J : GrothendieckTopology D) [J.Subcanonical]
    [F.IsContinuous (coherentTopology Profinite) J] (A : Type u) [Finite A] :
    PreservesColimitsOfShape (Discrete A) F := by
  have hle : extensiveTopology Profinite.{u} ≤ coherentTopology Profinite.{u} := by
    erw [extensiveTopology, ← extensive_regular_generate_coherent]
    exact (Coverage.gi Profinite).gc.monotone_l le_sup_left
  apply component_coproducts_of_hom_sheaves
  intro Y
  apply Presieve.isSheaf_of_le _ hle
  exact F.op_comp_isSheaf_of_isSheaf_type (coherentTopology Profinite)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj Y))

private abbrev component_point : Profinite.{u} := Profinite.of PUnit.{u + 1}
private def component_pointMap (S : Profinite.{u}) (s : S) : component_point ⟶ S :=
  CompHausLike.ofHom _ ⟨fun _ ↦ s, continuous_const⟩
private abbrev component_finiteCofan (S : FintypeCat.{u}) :
    Cofan (fun _ : S ↦ component_point.{u}) :=
  Cofan.mk (FintypeCat.toProfinite.obj S)
    (fun s : S ↦ component_pointMap (FintypeCat.toProfinite.obj S) s)

set_option backward.isDefEq.respectTransparency false in
private def component_finiteCofanIsColimit (S : FintypeCat.{u}) :
    IsColimit (component_finiteCofan S) := by
  let : TopologicalSpace S := FintypeCat.botTopology S
  have : DiscreteTopology S := FintypeCat.discreteTopology S
  refine Cofan.IsColimit.mk _ (fun t ↦ CompHausLike.ofHom _
    ⟨fun s ↦ t.inj s PUnit.unit, continuous_of_discreteTopology⟩) ?_ ?_
  · intro t s
    ext x
    exact congrArg (t.inj s) (Subsingleton.elim _ _)
  · intro t m hm
    ext s
    exact ConcreteCategory.congr_hom (hm s) PUnit.unit

set_option backward.isDefEq.respectTransparency false in
private theorem component_finiteIso {C : Type*} [Category* C] [HasCoproducts.{u} C]
    (F : Profinite.{u} ⥤ C)
    (hF : ∀ (A : Type u) [Finite A], PreservesColimitsOfShape (Discrete A) F) :
    Nonempty (FintypeCat.toProfinite ⋙ F ≅
      forget FintypeCat.{u} ⋙ sigmaConst.obj (F.obj component_point)) := by
  have (A : Type u) [Finite A] := hF A
  let hi (S : FintypeCat.{u}) :=
    isColimitCofanMkObjOfIsColimit F _ _ (component_finiteCofanIsColimit S)
  let e (S : FintypeCat.{u}) :
      (sigmaConst.obj (F.obj component_point)).obj S ≅ F.obj (FintypeCat.toProfinite.obj S) :=
    (coproductIsCoproduct (fun _ : S ↦ F.obj component_point)).coconePointUniqueUpToIso (hi S)
  have he (S : FintypeCat.{u}) (s : S) :
      Sigma.ι (fun _ : S ↦ F.obj component_point) s ≫ (e S).hom =
        F.map (component_pointMap (FintypeCat.toProfinite.obj S) s) :=
    (coproductIsCoproduct (fun _ : S ↦ F.obj component_point)).comp_coconePointUniqueUpToIso_hom
      (hi S) ⟨s⟩
  refine ⟨(NatIso.ofComponents e ?_).symm⟩
  intro S T f
  apply Sigma.hom_ext
  intro s
  change Sigma.ι (fun _ : S ↦ F.obj component_point) s ≫
      (Sigma.map' f (fun _ ↦ 𝟙 (F.obj component_point))) ≫ (e T).hom =
    Sigma.ι (fun _ : S ↦ F.obj component_point) s ≫ (e S).hom ≫ F.map (FintypeCat.toProfinite.map f)
  erw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp, he,
    ← Category.assoc, he, ← F.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The relative profinite test functor, its presentation characterization, and the
factorization of the condensed-point morphism.

Source: Hemo--Richarz--Scholbach, paragraph before (4.1) and factorization after it;
Bhatt--Scholze, Lemma 2.2.8 and its more precise statement
(blueprint: lem-zl-component-relative-profinite-site).

Proof for stage 3.
1. The affine component-site projection supplies the functor, stalkwise isomorphisms,
   the pullback homeomorphisms, finite limits, coverings, and the geometric morphism.
2. The inverse-image adjunction makes each continuous lift over T into a unique
   scheme morphism, since the structure morphism is an isomorphism on stalks.
3. At a finite stage, each restricted clopen subscheme maps to its corresponding
   finite-coordinate fibre. These are disjoint open immersions covering the test
   scheme, so their cofan is a coproduct, including empty and repeated blocks.
4. Compatible finite clopen partitions give a small cofiltered relative presentation;
   its limiting property follows from Mathlib's canonical finite-quotient limit.
5. Apply the universal mapping property to the limiting cone in topological spaces
   over the component space. This proves preservation of every small relative limit.
6. For finite coproducts, images of the component injections are disjoint open
   immersions covering the target. Their cofan is again a scheme coproduct.
7. The absolute functor and the relative functor applied to S times a profinite test
   agree on finite tests: continuity gives finite coproducts and finite limits give
   the terminal test. Both preserve the canonical finite-quotient limits. The finite
   comparison extends naturally through these limits.
8. Mathlib's slice adjunction gives the geometric morphism with inverse image
   overPullback. Restriction along the natural comparison identifies the composite
   direct image with the condensed-point direct image. Its adjoint mate gives the
   stated isomorphism of inverse images. -/
theorem component_relative_profinite_site (T : Scheme.{u}) [IsAffine T] :
    ∃ F : Over (affineComponentSpace T) ⥤ T.ProEt,
      (∀ E : Over (affineComponentSpace T), IsAffine (F.obj E).left) ∧
      (∃ p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left),
        (∀ (E : Over (affineComponentSpace T)) (x : (F.obj E).left),
          E.hom (p E x) = ConnectedComponents.mk ((F.obj E).hom x)) ∧
        (∀ (E E' : Over (affineComponentSpace T)) (a : E ⟶ E') (x : (F.obj E).left),
          p E' ((F.map a).left x) = a.left (p E x)) ∧
        ∀ (W : Over T) (E : Over (affineComponentSpace T)) (g : C(W.left, E.left)),
          (∀ w : W.left, E.hom (g w) = ConnectedComponents.mk (W.hom w)) →
          ∃! m : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E),
            ∀ w : W.left, p E (m.left w) = g w) ∧
      (∀ (A C : FintypeCat.{u})
        (q : affineComponentSpace T ⟶ FintypeCat.toProfinite.obj C) (f : A ⟶ C),
        Function.Surjective q →
        Nonempty ((Scheme.ProEt.forget T).obj (F.obj (componentFiniteStage A C q f)) ≅
          componentFiniteScheme T A C q f)) ∧
      (∀ E : Over (affineComponentSpace T),
        ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
          (D : I ⥤ Over (affineComponentSpace T)) (c : Cone D),
          c.pt = E ∧ Nonempty (IsLimit c) ∧ ∀ i : I, IsComponentFiniteStage (D.obj i)) ∧
      (∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
        (D : I ⥤ Over (affineComponentSpace T)) (c : Cone D),
        (∀ i : I, IsComponentFiniteStage (D.obj i)) → IsLimit c →
        Nonempty (IsLimit ((F ⋙ Scheme.ProEt.forget T).mapCone c))) ∧
      PreservesFiniteLimits F ∧
      (∀ (A : Type u) [Finite A], PreservesColimitsOfShape (Discrete A) F) ∧
      (∀ (A : Type u) [Finite A] (E : A → Over (affineComponentSpace T))
        (E₀ : Over (affineComponentSpace T)) (f : ∀ a : A, E a ⟶ E₀),
        (∀ x : E₀.left, ∃ (a : A) (y : (E a).left), (f a).left y = x) →
        Presieve.ofArrows (fun a : A => F.obj (E a)) (fun a : A => F.map (f a)) ∈
          Scheme.ProEt.precoverage T (F.obj E₀)) ∧
      ∃ π : GeometricMorphism
          (Sheaf (Scheme.ProEt.topology T) (Type (u + 1)))
          (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
            (Type (u + 1))),
        Nonempty (π.direct ⋙
            sheafToPresheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
              (Type (u + 1)) ≅
          sheafToPresheaf (Scheme.ProEt.topology T) (Type (u + 1)) ⋙
            (Functor.whiskeringLeft _ _ _).obj F.op) ∧
        ∃ q : GeometricMorphism
            (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
              (Type (u + 1)))
            (Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))),
          q.inverse = (coherentTopology Profinite.{u}).overPullback
            (Type (u + 1)) (affineComponentSpace T) ∧
          Nonempty (profinitePointSetSchemeInverseImage T ≅ (π.comp q).inverse) := by
  classical
  obtain ⟨F, p, hF, hnat, hlim, hcov, hcont, hset, hab, hring⟩ :=
    Scheme.ProEt.affine_component_site_projection T
  have hgeom : ∀ E : Over (affineComponentSpace T),
      (∀ x : (F.obj E).left, IsIso ((F.obj E).hom.stalkMap x)) ∧
      ∃ h : (F.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x) :=
    fun E ↦ ⟨(hF E).2.2.1, (hF E).2.2.2.1⟩
  obtain ⟨hp, hmap⟩ := component_mapping_property T F p hgeom
  refine ⟨F, fun E ↦ (hF E).1, ⟨p, hp, hnat, hmap⟩, ?_, ?_, ?_, hlim, ?_, ?_, ?_⟩
  · intro A C q f hq
    exact component_finite_comparison T F p hgeom hp hmap A C q f
  · intro E
    obtain ⟨I, hI, hcof, D, c, hc, hL, hstage⟩ :=
      Profinite.exists_relative_finite_presentation E
    exact ⟨I, hI, hcof, D, c, hc, hL, hstage⟩
  · intro I hI hcof D c hstage hc
    exact component_preserves_limits T F p hp hnat hmap D c hc
  · exact component_preserves_coproducts T F p hgeom hnat
  · intro A hA E E₀ f hf
    let := Fintype.ofFinite A
    let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
    have h := hcov (Fintype.card A) (fun i ↦ E (e i)) E₀ (fun i ↦ f (e i))
      (by
        intro x
        obtain ⟨a, y, hy⟩ := hf x
        obtain ⟨i, rfl⟩ := e.surjective a
        exact ⟨i, y, hy⟩)
    convert h using 1
    apply funext
    intro V
    apply funext
    intro g
    apply propext
    constructor
    · rintro ⟨a⟩
      obtain ⟨i, rfl⟩ := e.surjective a
      exact ⟨i⟩
    · rintro ⟨i⟩
      exact ⟨e i⟩
  · have := hcont
    have := hlim
    let S := affineComponentSpace T
    let J := coherentTopology Profinite.{u}
    let K := J.over S
    let L := Scheme.ProEt.topology T
    have hFc : F.IsContinuous K L := hcont
    have hHc : (profiniteToProEtOf T).IsContinuous J L :=
      Functor.isContinuous_comp profiniteToProEt
        (Scheme.proEtaleBaseChange (toSpecZ T)) J (Scheme.ProEt.topology specZ) L
    let G₀ : Profinite.{u} ⥤ T.ProEt := Over.star S ⋙ F
    have hG₀ : G₀.IsContinuous J L :=
      Functor.isContinuous_comp (Over.star S) F J K L
    let G := G₀ ⋙ Scheme.ProEt.forget T
    let H := profiniteToProEtOf T ⋙ Scheme.ProEt.forget T
    have hGc : G.IsContinuous J (Scheme.proetaleTopology.over T) :=
      Functor.isContinuous_comp G₀ (Scheme.ProEt.forget T) J L _
    have hcop (A : Type u) [Finite A] : PreservesColimitsOfShape (Discrete A) G :=
      component_coproducts_of_continuous G (Scheme.proetaleTopology.over T) A
    have : PreservesFiniteLimits G := inferInstance
    let et : G.obj component_point ≅ Over.mk (𝟙 T) :=
      (Profinite.isTerminalPUnit.isTerminalObj G _).uniqueUpToIso Over.mkIdTerminal
    have (A : Type u) : HasColimitsOfShape (Discrete A) (Over T) := by
      have : HasColimitsOfShape (Discrete A) Scheme.{u} := inferInstance
      exact ⟨fun D ↦ Over.hasColimit_of_hasColimit_comp_forget D⟩
    let eG : FintypeCat.toProfinite ⋙ G ≅
        forget FintypeCat.{u} ⋙ sigmaConst.obj (Over.mk (𝟙 T)) :=
      (component_finiteIso G hcop).some ≪≫
        Functor.isoWhiskerLeft (forget FintypeCat) (sigmaConst.mapIso et)
    obtain ⟨eH⟩ := (profinite_test_object_functor T).2.2.1
    have hGl (P : Profinite.{u}) : Nonempty (IsLimit (G.mapCone P.asLimitCone)) :=
      component_preserves_limits T F p hp hnat hmap (P.diagram ⋙ Over.star S)
        ((Over.star S).mapCone P.asLimitCone)
        (isLimitOfPreserves (Over.star S) P.asLimit)
    have hHl (P : Profinite.{u}) : Nonempty (IsLimit (H.mapCone P.asLimitCone)) :=
      (profinite_test_object_functor T).2.2.2.1 _ P.fintypeDiagram P.asLimitCone P.asLimit
        (fun Q ↦ DiscreteQuotient.proj_surjective Q)
    obtain ⟨e⟩ := Profinite.functor_iso_of_finite G H hGl hHl (eG ≪≫ eH.symm)
    let e₀ : G₀ ≅ profiniteToProEtOf T :=
      Functor.fullyFaithfulCancelRight (Scheme.ProEt.forget T) e
    obtain ⟨π, d, _⟩ := hset
    let qGeom : GeometricMorphism (Sheaf K (Type (u + 1))) (Sheaf J (Type (u + 1))) :=
      { inverse := J.overPullback (Type (u + 1)) S
        direct := (Over.star S).sheafPushforwardContinuous (Type (u + 1)) J K
        adj := (Over.forgetAdjStar S).sheafPushforwardContinuous K J
        leftExact := by infer_instance }
    refine ⟨π, ⟨Functor.isoWhiskerRight d (sheafToPresheaf K (Type (u + 1))) ≪≫
      F.sheafPushforwardContinuousCompSheafToPresheafIso _ _ _⟩, qGeom, rfl, ?_⟩
    let R := (profiniteToProEtOf T).sheafPushforwardContinuous (Type (u + 1)) J L
    let eR : (π.comp qGeom).direct ≅ R :=
      Functor.isoWhiskerRight d qGeom.direct ≪≫
        Functor.sheafPushforwardContinuousComp (Over.star S) F (Type (u + 1)) J K L ≪≫
        Functor.sheafPushforwardContinuousIso e₀ (Type (u + 1)) J L
    let adj := profinite_point_pullback.{u}.2.2.2.2.2.1.some |>.comp
      (Scheme.proEtaleSheafAdjunction (toSpecZ T) (Type (u + 1)))
    let ecomp : R ≅ Scheme.proEtaleSheafDirectImage (toSpecZ T) (Type (u + 1)) ⋙
        profiniteToProEt.sheafPushforwardContinuous (Type (u + 1))
          J (Scheme.ProEt.topology specZ) :=
      (Functor.sheafPushforwardContinuousComp profiniteToProEt
        (Scheme.proEtaleBaseChange (toSpecZ T)) (Type (u + 1))
        J (Scheme.ProEt.topology specZ) L).symm
    exact ⟨((conjugateIsoEquiv (π.comp qGeom).adj adj).symm (eR ≪≫ ecomp))⟩

end AlgebraicGeometry.ProEtale
