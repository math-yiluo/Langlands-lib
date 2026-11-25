/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Representations over disjoint components

Source: Stacks Project, Tags 03RV and 02W5, gluing local representations.
(blueprint: lem-weil-pbc-etale-coproduct-representation)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Functor

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

-- The inverse image of a component under a componentwise map is that component.
private theorem sigma_map_isPullback {ι : Type u} (X Y : ι → Scheme.{u})
    (f : ∀ i, X i ⟶ Y i) (i : ι) :
    IsPullback (f i) (Sigma.ι X i) (Sigma.ι Y i) (Limits.Sigma.map f) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨⟨j, x⟩, rfl⟩ := (sigmaMk X).surjective x
    rw [sigmaMk_mk] at hxy ⊢
    have hx : Sigma.ι Y i y = Sigma.ι Y j (f j x) := by
      simpa [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base] using hxy
    have hij : i = j := congrArg Sigma.fst ((sigmaι_eq_iff Y i j y (f j x)).mp hx)
    subst j
    exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨f i x, by simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]⟩

-- Compose an etale object with the open coprojection.
private noncomputable def componentFunctor {ι : Type u} (X : ι → Scheme.{u}) (i : ι) :
    (X i).Etale ⥤ (∐ X).Etale :=
  MorphismProperty.Over.map (f := Sigma.ι X i) ⊤ (inferInstance : Etale (Sigma.ι X i))

-- The counit supplies the pullback projections, naturally in the etale object.
private noncomputable def componentProjection {ι : Type u} (X : ι → Scheme.{u}) (i : ι) :
    (Sigma.ι X i).Etale ⋙ componentFunctor X i ⟶ 𝟭 (∐ X).Etale :=
  (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ (Sigma.ι X i)
    (inferInstance : Etale (Sigma.ι X i)) trivial).counit

private noncomputable def componentRestriction {ι : Type u} (X : ι → Scheme.{u})
    (F : Sheaf (∐ X).smallEtaleTopology (Type (u + 1))) (i : ι) :
    F.obj ⟶ ((Sigma.ι X i).Etale ⋙ componentFunctor X i).op ⋙ F.obj where
  app W := F.obj.map ((componentProjection X i).app W.unop).op
  naturality W W' f := by
    change F.obj.map f ≫ F.obj.map ((componentProjection X i).app W'.unop).op =
      F.obj.map ((componentProjection X i).app W.unop).op ≫
        F.obj.map (((Sigma.ι X i).Etale ⋙ componentFunctor X i).map f.unop).op
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    change F.obj.map (((componentProjection X i).app W'.unop ≫ f.unop).op) = _
    exact congrArg (fun g ↦ F.obj.map g.op) ((componentProjection X i).naturality f.unop).symm

-- The disjoint-cover theorem identifies sections with the product of their restrictions.
private theorem componentRestriction_isIso {ι : Type u} (X : ι → Scheme.{u})
    (F : Sheaf (∐ X).smallEtaleTopology (Type (u + 1))) :
    IsIso (Pi.lift (componentRestriction X F)) := by
  have happ (W : (∐ X).Etaleᵒᵖ) :
      IsIso ((Pi.lift (componentRestriction X F)).app W) := by
    let D (i : ι) := ((Sigma.ι X i).Etale ⋙ componentFunctor X i).obj W.unop
    let π (i : ι) : D i ⟶ W.unop := (componentProjection X i).app W.unop
    have hmono : ∀ i, Mono (π i) := fun i ↦ by
      have : IsOpenImmersion (π i).left := by
        change IsOpenImmersion (pullback.fst W.unop.hom (Sigma.ι X i))
        infer_instance
      exact (MorphismProperty.Over.forget @Etale ⊤ (∐ X) ⋙ Over.forget (∐ X)).mono_of_mono_map
        (by change Mono (π i).left; infer_instance)
    have hrange (i : ι) : Set.range (π i).left.base =
        W.unop.hom.base ⁻¹' Set.range (Sigma.ι X i).base :=
      Pullback.range_fst W.unop.hom (Sigma.ι X i)
    have hcov : Sieve.ofArrows D π ∈ (∐ X).smallEtaleTopology W.unop := by
      rw [ofArrows_mem_smallEtaleTopology_iff]
      simp only [hrange, ← Set.preimage_iUnion]
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk X).surjective (W.unop.hom x)
      exact Set.mem_iUnion.mpr ⟨i, y, (sigmaMk_mk X i y).symm.trans hy⟩
    have hdisj (i j : ι) (hij : i ≠ j) :
        Disjoint (Set.range (π i).left.base) (Set.range (π j).left.base) := by
      rw [hrange, hrange]
      exact (TopologicalSpace.Opens.coe_disjoint.mpr
        (disjoint_opensRange_sigmaι X i j hij)).preimage _
    have h : (Pi.lift (componentRestriction X F)).app W ≫
        (piObjIso _ W).hom = Pi.lift (fun i ↦ F.obj.map (π i).op) := by
      apply Pi.hom_ext
      intro i
      rw [Category.assoc, piObjIso_hom_comp_π, ← NatTrans.comp_app, Pi.lift_comp_π]
      change (componentRestriction X F i).app W =
        (Pi.lift (fun i ↦ F.obj.map (π i).op)) ≫
          Pi.π (fun i ↦ F.obj.obj (op (D i))) i
      rw [Pi.lift_comp_π]
      rfl
    rw [← Iso.eq_comp_inv] at h
    rw [h]
    have := Etale.isIso_piLift_of_disjoint F D π hcov hdisj
    infer_instance
  exact NatIso.isIso_of_isIso_app _

-- Whisker local isomorphisms with base change and conjugate their product by restriction.
private theorem coproduct_sheaf_iso {ι : Type u} (X : ι → Scheme.{u})
    (F G : Sheaf (∐ X).smallEtaleTopology (Type (u + 1)))
    (e : ∀ i, (componentFunctor X i).op ⋙ F.obj ≅
      (componentFunctor X i).op ⋙ G.obj) : Nonempty (F.obj ≅ G.obj) := by
  let := componentRestriction_isIso X F
  let := componentRestriction_isIso X G
  exact ⟨asIso (Pi.lift (componentRestriction X F)) ≪≫
    Pi.mapIso (fun i ↦ isoWhiskerLeft (Sigma.ι X i).Etale.op (e i)) ≪≫
    (asIso (Pi.lift (componentRestriction X G))).symm⟩

-- The component pullback universal property gives the representable comparison.
private noncomputable def coproductYonedaRestrictionIso {ι : Type u}
    (X Y : ι → Scheme.{u}) (f : ∀ i, X i ⟶ Y i) [∀ i, Etale (f i)]
    [Etale (Limits.Sigma.map f)] (i : ι) :
    (componentFunctor Y i).op ⋙ uliftYoneda.{u + 1}.obj (Etale.mk (Limits.Sigma.map f)) ≅
      uliftYoneda.{u + 1}.obj (Etale.mk (f i)) := by
  let h := sigma_map_isPullback X Y f i
  refine NatIso.ofComponents (fun W ↦ Equiv.toIso ?_) ?_
  · exact
      { toFun := fun a ↦ ⟨MorphismProperty.Over.homMk
          (h.lift W.unop.hom a.down.left (MorphismProperty.Over.w a.down).symm)
          (h.lift_fst _ _ _)⟩
        invFun := fun b ↦ ⟨MorphismProperty.Over.homMk (b.down.left ≫ Sigma.ι X i) (by
          change (b.down.left ≫ Sigma.ι X i) ≫ Limits.Sigma.map f =
            W.unop.hom ≫ Sigma.ι Y i
          rw [Category.assoc, Sigma.ι_map, ← Category.assoc]
          exact congrArg (fun g ↦ g ≫ Sigma.ι Y i)
            (MorphismProperty.Over.w b.down))⟩
        left_inv := by
          intro a
          apply ULift.ext
          apply MorphismProperty.Over.Hom.ext
          exact h.lift_snd _ _ _
        right_inv := by
          intro b
          apply ULift.ext
          apply MorphismProperty.Over.Hom.ext
          change h.lift W.unop.hom (b.down.left ≫ Sigma.ι X i) _ = b.down.left
          apply h.hom_ext
          · rw [h.lift_fst]
            exact (MorphismProperty.Over.w b.down).symm
          · rw [h.lift_snd] }
  · intro W W' k
    ext a
    apply ULift.ext
    apply MorphismProperty.Over.Hom.ext
    change h.lift W'.unop.hom (k.unop.left ≫ a.down.left) _ =
      k.unop.left ≫ h.lift W.unop.hom a.down.left _
    apply h.hom_ext
    · rw [h.lift_fst, Category.assoc, h.lift_fst]
      exact (MorphismProperty.Over.w k.unop).symm
    · rw [h.lift_snd, Category.assoc, h.lift_snd]

/-- Chosen etale representatives on a family of components represent the transported
restriction to their coproduct. Finiteness and joint surjectivity onto T are not needed.

Source: Stacks Project, Tag 03RV (lemma-characterize-finite-locally-constant), the
assembly of local representations; Tag 02W5 (lemma-descent-data-sheaves), the sheaf
identification in the effective case. This is the disjoint-cover instance of that argument.
(blueprint: lem-weil-pbc-etale-coproduct-representation)

Proof: Put B = coproduct U_i and V = coproduct Q_i, with the displayed structure map.
For an etale W over B, let W_i = W times_B U_i. The coprojections U_i to B are open
immersions, disjoint, and jointly surjective; their base changes give a disjoint etale
cover of W. Its component square with V is cartesian: the inverse image of U_i in V
is Q_i, as follows from disjointness and the coproduct universal property. A morphism
W_i to V over B therefore factors uniquely through Q_i over U_i. Under the localized
site equivalence, the restriction of the transported sheaf to W_i is the original
sheaf evaluated at W_i to U_i to T. Apply the given representation isomorphism on
each W_i. The disjoint-cover sheaf axiom identifies sections on W with the product
of the sections on W_i. Representable presheaves satisfy the same sheaf axiom, so
the local maps to Q_i glue uniquely to a map W to V over B. Applying the inverse
local isomorphisms and gluing sections gives its inverse. Both composites restrict
to the identity on every W_i, hence are identities by separatedness. For a morphism
W' to W over B, its pullbacks W'_i to W_i commute with restriction, and naturality
of the given local isomorphisms followed by uniqueness of gluing proves naturality
of the assembled maps. These maps are the claimed presheaf isomorphism. For an empty
index type B, V and every W are empty, and the empty-cover axiom makes the section
sets singletons; thus the same construction works. No bound on the index set or
on the ranks is used. -/
theorem etaleCoproduct_representation
    {ι : Type u} (T : Scheme.{u})
    (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : ι → T.Etale) (Q : ∀ i, (U i).left.Etale)
    [Etale (CategoryTheory.Limits.Sigma.desc fun i ↦ (U i).hom)]
    [Etale (CategoryTheory.Limits.Sigma.map fun i ↦ (Q i).hom)]
    (hrep : ∀ i,
      Nonempty (((Etale.overSheafEquiv (U i) (Type (u + 1))).functor.obj
        (E.over (U i))).obj ≅ uliftYoneda.{u + 1}.obj (Q i))) :
    let B := Etale.mk (CategoryTheory.Limits.Sigma.desc fun i ↦ (U i).hom)
    Nonempty (((Etale.overSheafEquiv B (Type (u + 1))).functor.obj
      (E.over B)).obj ≅ uliftYoneda.{u + 1}.obj
        (Etale.mk (CategoryTheory.Limits.Sigma.map fun i ↦ (Q i).hom))) := by
  classical
  let B := Etale.mk (Limits.Sigma.desc fun i ↦ (U i).hom)
  let F := (Etale.overSheafEquiv B (Type (u + 1))).functor.obj (E.over B)
  let : Scheme.etaleTopology.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  let : B.left.smallEtaleTopology.Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful
      (Etale.forget B.left) _ (Scheme.etaleTopology.over B.left)
  let G := B.left.smallEtaleTopology.uliftYoneda.{u + 1}.obj
    (Etale.mk (Limits.Sigma.map fun i ↦ (Q i).hom))
  change Nonempty (F.obj ≅ G.obj)
  apply coproduct_sheaf_iso (fun i ↦ (U i).left) F G
  intro i
  let e := (hrep i).some
  have eE : (componentFunctor (fun i ↦ (U i).left) i).op ⋙ F.obj ≅
      ((Etale.overSheafEquiv (U i) (Type (u + 1))).functor.obj (E.over (U i))).obj := by
    refine NatIso.ofComponents (fun W ↦ ?_) ?_
    · change E.obj.obj (op (Etale.mk ((W.unop.hom ≫ Sigma.ι (fun i ↦ (U i).left) i) ≫ B.hom))) ≅
        E.obj.obj (op (Etale.mk (W.unop.hom ≫ (U i).hom)))
      apply E.obj.mapIso
      apply Iso.op
      refine MorphismProperty.Over.isoMk (Iso.refl _) ?_
      change 𝟙 _ ≫ (W.unop.hom ≫ Sigma.ι (fun i ↦ (U i).left) i) ≫ B.hom = W.unop.hom ≫ (U i).hom
      simp [B, Category.assoc]
    · intro W W' f
      change E.obj.map _ ≫ E.obj.map _ = E.obj.map _ ≫ E.obj.map _
      rw [← E.obj.map_comp, ← E.obj.map_comp]
      congr 1
  exact eE ≪≫ e ≪≫
    (coproductYonedaRestrictionIso (fun i ↦ (Q i).left) (fun i ↦ (U i).left)
      (fun i ↦ (Q i).hom) i).symm

end AlgebraicGeometry.Scheme
