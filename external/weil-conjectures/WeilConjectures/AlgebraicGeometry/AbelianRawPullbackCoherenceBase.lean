/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.AbelianRawPullbackIdentity
import WeilConjectures.AlgebraicGeometry.AbelianRawPullbackComposition

/-! # Coherence of varying-coefficient raw pullbacks

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-raw-pullback-coherence-base).
-/

@[expose] public section


universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private lemma presheaf_map_ext {C : Type*} [Category* C]
    {P Q : C ⥤ AddCommGrpCat.{v + 1}} (f g : P ⟶ Q)
    (h : ∀ U (z : P.obj U), f.app U z = g.app U z) : f = g := by
  apply NatTrans.ext
  funext U
  exact AddCommGrpCat.ext (h U)

private def homAddMap {D E : Type*} [Category.{v + 1} D] [Category.{v + 1} E]
    [Preadditive D] [Preadditive E] (L : D ⥤ E) [L.Additive]
    {X Z : D} {X' X'' Z'' Z' : E}
    (s₁ : X' ⟶ X'') (s₂ : X'' ⟶ L.obj X)
    (e₁ : L.obj Z ⟶ Z'') (e₂ : Z'' ⟶ Z') :
    (X ⟶ Z) →+ (X' ⟶ Z') where
  toFun z := s₁ ≫ s₂ ≫ L.map z ≫ e₁ ≫ e₂
  map_zero' := by simp
  map_add' x y := by
    simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

private noncomputable def rawPullbackMapGeneral
    {T C₀ C₁ C D E D' E' : Type*}
    [Category* T] [Category* C₀] [Category* C₁] [Category* C]
    [Category* D] [Category* E] [Category.{v + 1} D'] [Category.{v + 1} E']
    [Preadditive D'] [Preadditive E']
    (Q₀ : T ⥤ C₀) (Q₁ : C₀ ⥤ C₁) (Q₂ : C₁ ⥤ C)
    (P : C ⥤ D) (P' : C ⥤ E) (A : D ⥤ E)
    (SY : D ⥤ D') (SY' : E ⥤ E') (L : D' ⥤ E') [L.Additive]
    (c : P' ⟶ P ⋙ A) (t : SY ⋙ L ≅ A ⋙ SY')
    {Z : D'} {Z₁ Z₂ : E'} (e₁ : L.obj Z ⟶ Z₁) (e₂ : Z₁ ⟶ Z₂) :
    (Q₀ ⋙ Q₁ ⋙ Q₂ ⋙ P ⋙ SY).op ⋙ preadditiveYoneda.obj Z ⟶
      (Q₀ ⋙ Q₁ ⋙ Q₂ ⋙ P' ⋙ SY').op ⋙ preadditiveYoneda.obj Z₂ := by
  let Q := Q₀ ⋙ Q₁ ⋙ Q₂
  refine
    { app := fun U ↦ AddCommGrpCat.ofHom
        (homAddMap L (SY'.map (c.app (Q.obj U.unop)))
          (t.inv.app (P.obj (Q.obj U.unop))) e₁ e₂)
      naturality := ?_ }
  intro U V r
  apply AddCommGrpCat.ext
  intro z
  change SY'.map (c.app (Q.obj V.unop)) ≫ t.inv.app (P.obj (Q.obj V.unop)) ≫
      L.map (SY.map (P.map (Q.map r.unop)) ≫ z) ≫ (e₁ ≫ e₂) =
    SY'.map (P'.map (Q.map r.unop)) ≫ SY'.map (c.app (Q.obj U.unop)) ≫
      t.inv.app (P.obj (Q.obj U.unop)) ≫ L.map z ≫ (e₁ ≫ e₂)
  have hc := c.naturality (Q.map r.unop)
  have ht := t.inv.naturality (P.map (Q.map r.unop))
  change P'.map (Q.map r.unop) ≫ c.app (Q.obj U.unop) =
    c.app (Q.obj V.unop) ≫ A.map (P.map (Q.map r.unop)) at hc
  change SY'.map (A.map (P.map (Q.map r.unop))) ≫
      t.inv.app (P.obj (Q.obj U.unop)) =
    t.inv.app (P.obj (Q.obj V.unop)) ≫
      L.map (SY.map (P.map (Q.map r.unop))) at ht
  rw [L.map_comp, Category.assoc, ← reassoc_of% ht,
    ← SY'.map_comp_assoc, ← hc, SY'.map_comp, Category.assoc]

private noncomputable def rawPullbackMap {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F') :
    abelianHigherDirectImageRawPresheaf h p F ⟶
      abelianHigherDirectImageRawPresheaf h' p F' :=
  rawPullbackMapGeneral uliftYoneda.{v + 1}
    ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)
    (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (h)^*[AddCommGrpCat.{v + 1}] (h')^*[AddCommGrpCat.{v + 1}]
    (a)^*[AddCommGrpCat.{v + 1}]
    (DerivedCategory.Plus.singleFunctor _ 0) (DerivedCategory.Plus.singleFunctor _ 0)
    D+((a)^*[AddCommGrpCat.{v + 1}])
    (upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom
    (((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0)
    ((D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    ((shiftFunctor _ (p : ℤ)).map
      ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ))

private lemma rawPullbackMap_app {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F') (U : S.Etale)
    (z : (abelianHigherDirectImageRawPresheaf h p F).obj (op U)) :
    (rawPullbackMap a h h' w p F F' φ).app (op U) z =
      abelianHigherDirectImageRawPullback a h h' w p F F' φ U z := by
  rfl


/-- The explicit raw pullbacks form natural transformations and obey identity and composition.
Source: Stacks Project, Tag 09Z1 (lemma-relative-colimit), canonical comparison maps;
Tag 03CB for inverse-image composition.
(blueprint: lem-sbc-abelian-raw-pullback-coherence-base).

Proof: For each transition and each cone leg, use the five factors in
abelianHigherDirectImageRawPullback. The middle factor is an additive derived
inverse-image functor, and composition with the other four fixed morphisms is additive.
Thus each component is a homomorphism. If r is a morphism of test objects, naturality
of upperStarComp and of mapDerivedCategoryPlusSingleFunctor moves its free-sheaf
restriction through the first two factors. Functor.map_comp moves it through the
pulled-back class. This is the naturality square, so the component homomorphisms
bundle as tau and beta. Their displayed component equations hold by construction.

For an identity transition, rewrite D.map_id and use hphiid. The unit laws for
upperStarComp cancel the source identity comparison against the coefficient identity.
The corresponding derived identity comparison is natural in the class and commutes
with its shift. Its comparison on single complexes is the underived identity
comparison, since both come from the same termwise map; hence the other single
comparisons cancel. The resulting component is the original class.

For two transitions, expand the two five-factor formulas and use map_comp.
Naturality of the single comparison moves it past the intermediate source map and
cancels the intermediate hom/inv pair. The derived composition comparison is natural
in the class and commutes with shift. Its comparison on single complexes is the
underived composition comparison (abelianPullbackSingleComposition, specialized to
these scheme maps). Apply upperStarComp associativity to the two source maps and
the structure map to combine the source factors, and apply hphicomp to combine the
coefficient factors. The remaining factors are those of the composite raw pullback.
Extensionality of homomorphisms and natural transformations proves both laws.
Neither construction uses hH, continuity, or any geometric hypothesis. In particular
empty index sets, empty test objects, zero coefficients, and p = 0 are allowed. -/
theorem abelianRawPullback_coherent_base {S : Scheme.{v}}
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
    [HasColimit H] (p : ℕ) :
    ∃ (τ : ∀ {i j : I} (_f : i ⟶ j),
        abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
          abelianHigherDirectImageRawPresheaf (D.obj (op j)).hom p (F j))
      (β : ∀ i : I, abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i) ⟶
        abelianHigherDirectImageRawPresheaf c.pt.hom p (colimit H)),
      (∀ {i j : I} (f : i ⟶ j) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (τ f).app (op V) t = abelianHigherDirectImageRawPullback (D.map f.op).left
          (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
          (F i) (F j) (φ f) V t) ∧
      (∀ (i : I) (V : S.Etale) (t :
          (abelianHigherDirectImageRawPresheaf (D.obj (op i)).hom p (F i)).obj (op V)),
        (β i).app (op V) t = abelianHigherDirectImageRawPullback (c.π.app (op i)).left
          (D.obj (op i)).hom c.pt.hom (Over.w (c.π.app (op i))) p
          (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i) V t) ∧
      (∀ i : I, τ (𝟙 i) = 𝟙 _) ∧
      (∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), τ (f ≫ g) = τ f ≫ τ g) := by
  have _ := @hH
  clear hH
  let τ := fun {i j : I} (f : i ⟶ j) ↦
    rawPullbackMap (D.map f.op).left (D.obj (op i)).hom (D.obj (op j)).hom
      (Over.w (D.map f.op)) p (F i) (F j) (φ f)
  let β := fun i : I ↦
    rawPullbackMap (c.π.app (op i)).left (D.obj (op i)).hom c.pt.hom
      (Over.w (c.π.app (op i))) p (F i) (colimit H) ((eH i).inv ≫ colimit.ι H i)
  refine ⟨τ, β, ?_, ?_, ?_, ?_⟩
  · intro i j f V t
    exact rawPullbackMap_app _ _ _ _ _ _ _ _ _ _
  · intro i V t
    exact rawPullbackMap_app _ _ _ _ _ _ _ _ _ _
  · intro i
    apply presheaf_map_ext
    rintro ⟨U⟩ t
    dsimp only [τ, NatTrans.id_app, AddCommGrpCat.id_apply]
    rw [rawPullbackMap_app]
    have ha : (D.map (𝟙 i).op).left = 𝟙 (D.obj (op i)).left := by
      exact congrArg (fun q ↦ q.left) (D.map_id (op i))
    exact abelianHigherDirectImageRawPullback_identity _ ha (D.obj (op i)).hom
      (Over.w (D.map (𝟙 i).op)) p (F i) (φ (𝟙 i)) (hφid i) U t
  · intro i j k f g
    apply presheaf_map_ext
    rintro ⟨U⟩ t
    simp only [τ, NatTrans.comp_app, AddCommGrpCat.comp_apply]
    rw [rawPullbackMap_app, rawPullbackMap_app, rawPullbackMap_app]
    have hd : (D.map (f ≫ g).op).left = (D.map g.op).left ≫ (D.map f.op).left := by
      exact congrArg (fun q ↦ q.left) (D.map_comp g.op f.op)
    exact abelianHigherDirectImageRawPullback_composition _ _ _ hd
      (D.obj (op i)).hom (D.obj (op j)).hom (D.obj (op k)).hom
      (Over.w (D.map f.op)) (Over.w (D.map g.op)) (Over.w (D.map (f ≫ g).op)) p
      (F i) (F j) (F k) (φ f) (φ g) (φ (f ≫ g)) (hφcomp f g) U t

end AlgebraicGeometry.Etale
