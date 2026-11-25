/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.BaseChange.Pasting
import all WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift
import all WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp

/-! # Coherence of varying-coefficient raw pullbacks

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-raw-pullback-coherence-extend).
-/

@[expose] public section


universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem shiftedHom_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (P : C ⥤ D) (Q : D ⥤ E) (R : C ⥤ E)
    [P.CommShift ℤ] [Q.CommShift ℤ] [R.CommShift ℤ]
    (θ : R ⟶ P ⋙ Q) [NatTrans.CommShift θ ℤ]
    {X K : C} {Y L : D} {Z M : E}
    (a : Y ⟶ P.obj X) (b : Z ⟶ Q.obj Y) (c : Z ⟶ R.obj X)
    (t : P.obj K ⟶ L) (u : Q.obj L ⟶ M) (v : R.obj K ⟶ M)
    (hs : b ≫ Q.map a = c ≫ θ.app X)
    (ht : θ.app K ≫ Q.map t ≫ u = v) (n : ℤ) (z : X ⟶ K⟦n⟧) :
    b ≫ Q.map (a ≫ P.map z ≫ (P.commShiftIso n).hom.app K ≫ t⟦n⟧') ≫
        (Q.commShiftIso n).hom.app L ≫ u⟦n⟧' =
      c ≫ R.map z ≫ (R.commShiftIso n).hom.app K ≫ v⟦n⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [Q.commShiftIso_hom_naturality_assoc]
  rw [← Category.assoc b, hs, Category.assoc]
  have hn := θ.naturality z
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have hc := NatTrans.shift_app_comm θ n K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj] at hc
  rw [← reassoc_of% hc]
  simp only [← Functor.map_comp, ← ht]

private theorem singleComparison_source
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (P : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂) (R : C₀ ⥤ C₂)
    (T₀ : C₀ ⥤ D₀) (T₁ : C₁ ⥤ D₁) (T₂ : C₂ ⥤ D₂)
    (U : D₀ ⥤ D₁) (V : D₁ ⥤ D₂) (W : D₀ ⥤ D₂)
    (σP : T₀ ⋙ U ≅ P ⋙ T₁) (σQ : T₁ ⋙ V ≅ Q ⋙ T₂) (σR : T₀ ⋙ W ≅ R ⋙ T₂)
    (κ : R ⟶ P ⋙ Q) (θ : W ⟶ U ⋙ V)
    (X : C₀) (Y : C₁) (Z : C₂)
    (a : Y ⟶ P.obj X) (b : Z ⟶ Q.obj Y) (c : Z ⟶ R.obj X)
    (hs : b ≫ Q.map a = c ≫ κ.app X)
    (ht : σR.hom.app X ≫ T₂.map (κ.app X) ≫ σQ.inv.app (P.obj X) =
      θ.app (T₀.obj X) ≫ V.map (σP.hom.app X)) :
    (T₂.map b ≫ σQ.inv.app Y) ≫ V.map (T₁.map a ≫ σP.inv.app X) =
      (T₂.map c ≫ σR.inv.app X) ≫ θ.app (T₀.obj X) := by
  have he := congrArg (fun k ↦ σR.inv.app X ≫ k ≫ V.map (σP.inv.app X)) ht
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← V.map_comp,
    Iso.hom_inv_id_app] at he
  have hn := σQ.inv.naturality a
  dsimp only [Functor.comp_map] at hn
  simp only [V.map_comp, Category.assoc]
  rw [← reassoc_of% hn, ← T₂.map_comp_assoc, hs, T₂.map_comp, Category.assoc, he]
  erw [V.map_id, Category.comp_id]

private theorem singleComparison_target
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (P : C₀ ⥤ C₁) (Q : C₁ ⥤ C₂) (R : C₀ ⥤ C₂)
    (T₀ : C₀ ⥤ D₀) (T₁ : C₁ ⥤ D₁) (T₂ : C₂ ⥤ D₂)
    (U : D₀ ⥤ D₁) (V : D₁ ⥤ D₂) (W : D₀ ⥤ D₂)
    (σP : T₀ ⋙ U ≅ P ⋙ T₁) (σQ : T₁ ⋙ V ≅ Q ⋙ T₂) (σR : T₀ ⋙ W ≅ R ⋙ T₂)
    (κ : R ⟶ P ⋙ Q) (θ : W ⟶ U ⋙ V)
    (X : C₀) (Y : C₁) (Z : C₂)
    (a : P.obj X ⟶ Y) (b : Q.obj Y ⟶ Z)
    (ht : σR.hom.app X ≫ T₂.map (κ.app X) ≫ σQ.inv.app (P.obj X) =
      θ.app (T₀.obj X) ≫ V.map (σP.hom.app X)) :
    θ.app (T₀.obj X) ≫ V.map (σP.hom.app X ≫ T₁.map a) ≫
        σQ.hom.app Y ≫ T₂.map b =
      σR.hom.app X ≫ T₂.map (κ.app X ≫ Q.map a ≫ b) := by
  have he := congrArg (fun k ↦ k ≫ σQ.hom.app (P.obj X)) ht
  simp only [Category.assoc, Iso.inv_hom_id_app] at he
  have hn := σQ.hom.naturality a
  dsimp only [Functor.comp_map] at hn
  simp only [V.map_comp, T₂.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← reassoc_of% he]


set_option backward.isDefEq.respectTransparency false in
private theorem pullbackHom_comp (𝒜 : Type (v + 2)) [Category.{v + 1} 𝒜]
    [Abelian 𝒜] [IsGrothendieckAbelian.{v + 1} 𝒜]
    {S Y Y' Z : Scheme.{v}} (a : Y' ⟶ Y) (b : Z ⟶ Y') (h : Y ⟶ S)
    (M : Sheaf S.smallEtaleTopology 𝒜)
    (F : Sheaf Y.smallEtaleTopology 𝒜) (F' : Sheaf Y'.smallEtaleTopology 𝒜)
    (G : Sheaf Z.smallEtaleTopology 𝒜)
    (φ : ((a)^*[𝒜]).obj F ⟶ F') (ψ : ((b)^*[𝒜]).obj F' ⟶ G)
    (n : ℤ) (z : (DerivedCategory.Plus.singleFunctor _ 0).obj (((h)^*[𝒜]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦n⟧) :
  let raw := fun {X X' : Scheme.{v}} (a' : X' ⟶ X) (g : X ⟶ S)
    (g' : X' ⟶ S) (w : a' ≫ g = g')
    (B : Sheaf X.smallEtaleTopology 𝒜) (B' : Sheaf X'.smallEtaleTopology 𝒜)
    (f : ((a')^*[𝒜]).obj B ⟶ B')
    (t : (DerivedCategory.Plus.singleFunctor _ 0).obj (((g)^*[𝒜]).obj M) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj B)⟦n⟧) ↦
      (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp 𝒜 a' g g' w.symm).hom.app M) ≫
        (((a')^*[𝒜]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
        D+((a')^*[𝒜]).map t ≫
        (D+((a')^*[𝒜]).commShiftIso n).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj B) ≫
        (shiftFunctor _ n).map
          ((((a')^*[𝒜]).mapDerivedCategoryPlusSingleFunctor 0).hom.app B ≫
            (DerivedCategory.Plus.singleFunctor _ 0).map f)
  raw b (a ≫ h) (b ≫ a ≫ h) rfl F' G ψ
      (raw a h (a ≫ h) rfl F F' φ z) =
    raw (b ≫ a) h (b ≫ a ≫ h) (Category.assoc b a h) F G
      ((upperStarComp 𝒜 b a).hom.app F ≫ ((b)^*[𝒜]).map φ ≫ ψ) z := by
  intro raw
  let P := (a)^*[𝒜]
  let Q := (b)^*[𝒜]
  let R := (b ≫ a)^*[𝒜]
  let θ := upperStarPlusComp 𝒜 b a
  have : NatTrans.CommShift θ.hom ℤ := by
    dsimp only [θ, upperStarPlusComp, Iso.trans_hom]
    have := Functor.plusNatIso_commShift (upperStarComp 𝒜 b a)
    have := Functor.plusCompIso_commShift P Q
    infer_instance
  let T := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology 𝒜) 0
  let T' := DerivedCategory.Plus.singleFunctor
    (Sheaf Y'.smallEtaleTopology 𝒜) 0
  let T'' := DerivedCategory.Plus.singleFunctor
    (Sheaf Z.smallEtaleTopology 𝒜) 0
  let σP := P.mapDerivedCategoryPlusSingleFunctor 0
  let σQ := Q.mapDerivedCategoryPlusSingleFunctor 0
  let σR := R.mapDerivedCategoryPlusSingleFunctor 0
  let κ := upperStarComp 𝒜 b a
  let x := T'.map ((upperStarComp 𝒜 a h).hom.app M) ≫
    σP.inv.app _
  let y := T''.map ((upperStarComp 𝒜 b (a ≫ h)).hom.app M) ≫
    σQ.inv.app _
  let z' := T''.map ((upperStarComp 𝒜 (b ≫ a) h
      (b ≫ a ≫ h) (Category.assoc b a h).symm).hom.app M) ≫
    σR.inv.app _
  have hσ (B : Sheaf Y.smallEtaleTopology 𝒜) :
      σR.hom.app B ≫ T''.map (κ.hom.app B) ≫ σQ.inv.app (P.obj B) =
        θ.hom.app (T.obj B) ≫ D+(Q).map (σP.hom.app B) := by
    rw [← cancel_mono (σQ.hom.app (P.obj B))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    symm
    dsimp only [θ]
    rw [upperStarPlusComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    erw [Category.comp_id]
    rw [Functor.plus_single_comp P Q 0 B, Functor.plus_single_natIso κ 0 B]
  have hc := NatTrans.congr_app (upperStarComp_assoc' 𝒜
    b a h (b ≫ a) (a ≫ h) (b ≫ a ≫ h) rfl rfl (Category.assoc b a h).symm) M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj] at hc
  have hs : y ≫ D+(Q).map x = z' ≫ θ.hom.app _ :=
    singleComparison_source P Q R T T' T'' D+(P) D+(Q) D+(R) σP σQ σR κ.hom θ.hom
      _ _ _ ((upperStarComp 𝒜 a h).hom.app M)
      ((upperStarComp 𝒜 b (a ≫ h)).hom.app M)
      ((upperStarComp 𝒜 (b ≫ a) h
        (b ≫ a ≫ h) (Category.assoc b a h).symm).hom.app M) hc (hσ _)
  have ht := singleComparison_target P Q R T T' T'' D+(P) D+(Q) D+(R)
    σP σQ σR κ.hom θ.hom F F' G φ ψ (hσ F)
  simpa only [raw, x, y, z', Category.assoc] using
    shiftedHom_comp D+(P) D+(Q) D+(R) θ.hom x y z'
    (σP.hom.app F ≫ T'.map φ)
    (σQ.hom.app F' ≫ T''.map ψ)
    (σR.hom.app F ≫
      T''.map ((upperStarComp 𝒜 b a).hom.app F ≫ Q.map φ ≫ ψ))
    hs ht n z


set_option backward.isDefEq.respectTransparency false in
/-- Pulling a raw class back twice composes the coefficient morphisms through
`upperStarComp`. Source: Stacks Project, Tag 09Z1, canonical cohomology maps,
and Tag 03CB, composition of inverse images.
(blueprint: lem-sbc-abelian-raw-pullback-coherence-extend).

Proof: Transport along wd, wa, and wb to reduce to composite scheme morphisms.
Expand both five-factor raw pullback formulas and distribute the outer derived
pullback over composition. Naturality of its single-complex comparison moves the
inner source comparison through the outer inverse comparison. The adjacent
single-complex hom and inv cancel. The already proved generic lemmas
Functor.plus_single_comp and Functor.plus_single_natIso identify the single
comparisons with the derived composition comparison. Naturality of that derived
comparison moves it past the raw class;
its compatibility with shifts moves it through the shifted coefficient factors.
The underived upperStarComp associativity law for b, a, h identifies the remaining
source factors. Functor.map_comp combines the remaining shifted coefficient maps
into upperStarComp(b,a) followed by b inverse image of phi followed by psi.
These are exactly the five factors of the direct pullback. All transports in
witnesses of equalities coincide by proof irrelevance. This argument allows
identity maps, zero coefficients and classes, empty schemes, and degree zero. -/
private theorem abelianHigherDirectImageRawPullback_comp {S Y Y' Z : Scheme.{v}}
    (a : Y' ⟶ Y) (b : Z ⟶ Y') (d : Z ⟶ Y) (wd : b ≫ a = d)
    (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Z ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (wc : d ≫ h = h'')
    (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F')
    (ψ : ((b)^*[AddCommGrpCat.{v + 1}]).obj F' ⟶ G) (U : S.Etale)
    (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    abelianHigherDirectImageRawPullback b h' h'' wb p F' G ψ U
        (abelianHigherDirectImageRawPullback a h h' wa p F F' φ U z) =
      abelianHigherDirectImageRawPullback d h h'' wc p F G
        ((upperStarComp AddCommGrpCat.{v + 1} b a d wd.symm).hom.app F ≫
          ((b)^*[AddCommGrpCat.{v + 1}]).map φ ≫ ψ) U z := by
  subst d
  subst h'
  cases wb
  exact pullbackHom_comp AddCommGrpCat.{v + 1} a b h _ F F' G φ ψ (p : ℤ) z


set_option linter.unusedVariables false in
/-- Natural transformations with the prescribed raw components obey the colimit cocone law.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit), canonical comparison maps;
Tag 03CB for inverse-image composition.
(blueprint: lem-sbc-abelian-raw-pullback-coherence-extend).

Proof: Fix f : i → j and a raw class z at a test object V. By hτ and hβ, the
component of tau f followed by beta j is the iterated explicit raw pullback along
D.map f.op and c.π.app (op j). Expand its two five-factor formulas. Functor.map_comp
and naturality of the single comparison cancel the intermediate single hom/inv
pair. The derived composition comparison is natural in z, commutes with the shift,
and on single complexes agrees with the underived comparison, as in
abelianPullbackSingleComposition. Associativity of upperStarComp combines the source
factors. Cone naturality c.w f.op identifies the composite scheme map with
c.π.app (op i); proof irrelevance identifies the resulting witnesses of Over.w.

Write C for the component of upperStarComp in hH, and P for pullback along the
j-th cone leg. The coefficient of this composite is
C ≫ P.map (φ f) ≫ (eH j).inv ≫ colimit.ι H j.
From hH and colimit.w H f this is (eH i).inv ≫ colimit.ι H i: precompose
H.map f ≫ colimit.ι H j = colimit.ι H i with (eH i).inv, substitute hH,
and cancel (eH i).inv ≫ (eH i).hom. The composite formula therefore equals
the i-th cone-leg raw pullback, which hβ identifies with beta i. Extensionality
in z and V proves tau f ≫ beta j = beta i. No identity/composition laws of tau
are assumed, and hφid and hφcomp are not used. The proof uses only colimit
naturality, not a limit or a continuity theorem, and also covers zero coefficients,
empty test objects, and degree zero. For an empty index set the conclusion is vacuous. -/
theorem abelianRawPullback_coherent_extend {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (c : Cone D)
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
    (τ : ∀ {i j : I} (_f : i ⟶ j),
        abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
          abelianHigherDirectImageRawPresheaf (D.obj (op j)).hom p (F j))
    (β : ∀ i : I, abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
        abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H))
    (hτ : ∀ {i j : I} (f : i ⟶ j) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (τ f).app (op V) t = abelianHigherDirectImageRawPullback (D.map f.op).left
          (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
          (F i) (F j) (φ f) V t)
    (hβ : ∀ (i : I) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (β i).app (op V) t = abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
          (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i) V t) :
    ∀ {i j : I} (f : i ⟶ j), τ f ≫ β j = β i := by
  intro i j f
  have hc :
      (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
        (c.π.app (op i)).left
        (congrArg (fun t ↦ t.left) (c.w f.op)).symm).hom.app (F i) ≫
          (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫
          ((eH j).inv ≫ colimit.ι H j) = (eH i).inv ≫ colimit.ι H i := by
    have hw := congrArg (fun k ↦ (eH i).inv ≫ k) (colimit.w H f)
    rw [hH f] at hw
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hw
  apply NatTrans.ext
  funext V
  ext t
  change (β j).app V ((τ f).app V t) = (β i).app V t
  obtain ⟨V⟩ := V
  rw [hβ, hτ, hβ]
  rw [abelianHigherDirectImageRawPullback_comp
    (D.map f.op).left (c.π.app (op j)).left (c.π.app (op i)).left
    (congrArg (fun t ↦ t.left) (c.w f.op))]
  rw [hc]

end AlgebraicGeometry.Etale
