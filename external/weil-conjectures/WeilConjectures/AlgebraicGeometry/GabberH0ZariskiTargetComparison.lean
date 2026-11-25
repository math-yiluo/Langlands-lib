/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison

/-! # Global transport through the composition comparison

Source: Stacks Project, Tag 09ZF, third and fourth proof paragraphs.
(blueprint: lem-weil-pbc-gabber-h0-zariski-target-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry


private lemma comparison_inverse_hom.{v, w} {C : Type v} [Category C]
    {K P : Cᵒᵖ ⥤ Type w} (c : K ≅ P) {V A D : C}
    (a : V ≅ A) (d : D ≅ A) (b : V ≅ D)
    (ha : a.hom ≫ d.inv = b.hom) {T : Type w} (e : P.obj (op D) ≅ T)
    (q : K.obj (op V) ≅ T)
    (hq : q = K.mapIso a.symm.op ≪≫ c.app (op A) ≪≫ P.mapIso d.op ≪≫ e) :
    q.inv ≫ c.hom.app (op V) = e.inv ≫ P.map b.hom.op := by
  subst q
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.op_inv,
    Iso.symm_inv]
  simp only [Category.assoc]
  rw [c.hom.naturality, ← Category.assoc (c.inv.app _) (c.hom.app _),
    Iso.inv_hom_id_app, Category.id_comp, ← P.map_comp, ← op_comp, ha]

private lemma eqToIso_congrArg_symm_inv.{v, w} {α : Sort v} {x y : α}
    (E : α → Type w) (p : x = y) :
    (eqToIso (congrArg E p.symm)).inv = eqToHom (congrArg E p) := by
  cases p
  rfl

private lemma descentComparison_transport {R S T : Scheme.{u}}
    (f : S ⟶ R) (g : T ⟶ S) (k : T ⟶ R) (hk : g ≫ f = k)
    (F : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale)
    (s : ((Scheme.etaleSetPullback f).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) :
    eqToHom (congrArg
      (fun k : T ⟶ R ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U))) hk)
      (etaleSetDescentComparison f g F U s) =
        etaleSetSectionComparison g f k hk F U s := by
  subst k
  rfl

private lemma identityPullback_hom_ext {S T : Scheme.{u}} (f : T ⟶ S)
    {V : T.Etale}
    (a b : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj
      (Scheme.Etale.mk (𝟙 S))) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (pullback.snd (𝟙 S) f)).1
  exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm

private lemma sectionIso_inverse_component
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback (pullback.fst i h ≫ i)).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst i h ≫ i)).obj
        (Scheme.Etale.mk (𝟙 X))))) :
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
      X X' (pullback i h) h (pullback.snd i h)).hom.app F).hom.app
        (op (Scheme.Etale.mk (⊤ : (pullback i h).Opens).ι)))
          ((gabberZariskiSectionIso i h F).inv t) =
      ((Scheme.etaleSetPullback (pullback.snd i h ≫ h)).obj F).obj.map
        (gabberTopPullbackIso (pullback.snd i h ≫ h)).hom.op
          (eqToHom (congrArg
            (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
              (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
                (Scheme.Etale.mk (𝟙 X)))))
            (pullback.condition (f := i) (g := h))) t) := by
  set_option backward.isDefEq.respectTransparency.types false in
  let j := pullback.snd i h
  let k := j ≫ h
  let U := Scheme.Etale.mk (𝟙 X)
  let B := MorphismProperty.Over.pullback @Etale ⊤ j
  let a := gabberTopEtaleIso (pullback i h) ≪≫
    gabberIdentityEtaleIso j ≪≫ B.mapIso (gabberIdentityEtaleIso h)
  let d := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) j h
  let K := (Scheme.etaleSetPullback j).obj ((Scheme.etaleSetPullback h).obj F)
  let P := (Scheme.etaleSetPullback k).obj F
  let c : K.obj ≅ P.obj := (sheafToPresheaf _ _).mapIso
    (((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
      X X' (pullback i h) h j).app F)
  have ha : a.hom ≫ d.inv.app U = (gabberTopPullbackIso k).hom :=
    identityPullback_hom_ext k _ _
  let E := fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
    (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U))
  let e : E k ≅ E (pullback.fst i h ≫ i) :=
    eqToIso (congrArg E ((pullback.condition (f := i) (g := h)).symm))
  -- Keep the constructed section isomorphism intact during the cancellation.
  have hq : gabberZariskiSectionIso i h F =
      K.obj.mapIso a.symm.op ≪≫ c.app (op ((B.obj
        ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)))) ≪≫
        P.obj.mapIso (d.app U).op ≪≫ e := by
    rfl
  have ht : e.inv = eqToHom
      (congrArg E (pullback.condition (f := i) (g := h))) :=
    eqToIso_congrArg_symm_inv E (pullback.condition (f := i) (g := h))
  have he := comparison_inverse_hom c a (d.app U) (gabberTopPullbackIso k) ha e
    (gabberZariskiSectionIso i h F) hq
  have hr := congrArg (fun v ↦ v ≫ P.obj.map (gabberTopPullbackIso k).hom.op) ht
  -- Expose the forgetful map before comparing the concrete section functions.
  have hv := ConcreteCategory.congr_hom (he.trans hr) t
  dsimp only [c, P, k, j, E, U, Functor.mapIso_hom, Iso.app_hom,
    sheafToPresheaf, ObjectProperty.ι, inducedFunctor] at hv
  simp only [comp_apply] at hv
  exact hv


/-- The chosen global transport agrees with section comparison through the other
side of the pullback square.
Source: Stacks Project, Tag 09ZF, third and fourth proof paragraphs; Sites,
Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-gabber-h0-zariski-target-comparison).

Proof: Expand the inverse defining the target section and the section isomorphism.
The latter first identifies the top open with the twice-pulled-back identity,
then applies the composition comparison for h and the second projection, and
then the fibre-product pasting isomorphism. Naturality of that comparison moves
these identifications to the composite inverse image. Their composite is the
canonical top-to-identity-pullback isomorphism: compose with each fibre-product
projection to check this by pullback uniqueness. Cancel the inverse of the
section isomorphism. The remaining equality transport is along pullback.condition;
the definition of section comparison along the first projection has exactly the
same transport and pasting map. Equality elimination and proof irrelevance identify
the transports. The result is an identity of functions on sections, so also applies
to empty schemes and to sheaves having no global sections. -/
theorem gabberZariskiTargetComparison
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj
        (Scheme.Etale.mk (𝟙 X))))) :
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
      X X' (pullback i h) h (pullback.snd i h)).hom.app F).hom.app
        (op (Scheme.Etale.mk (⊤ : (pullback i h).Opens).ι)))
          (gabberZariskiTargetSection i h F t) =
      ((Scheme.etaleSetPullback (pullback.snd i h ≫ h)).obj F).obj.map
        (gabberTopPullbackIso (pullback.snd i h ≫ h)).hom.op
          (etaleSetSectionComparison (pullback.fst i h) i (pullback.snd i h ≫ h)
            pullback.condition F (Scheme.Etale.mk (𝟙 X)) t) := by
  have hc := descentComparison_transport i (pullback.fst i h) (pullback.snd i h ≫ h)
    (pullback.condition (f := i) (g := h)) F (Scheme.Etale.mk (𝟙 X)) t
  have hi := sectionIso_inverse_component i h F
    (etaleSetDescentComparison i (pullback.fst i h) F (Scheme.Etale.mk (𝟙 X)) t)
  rw [hc] at hi
  exact hi

end AlgebraicGeometry
