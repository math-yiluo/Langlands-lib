/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Composition and base change for sections with proper support

Source: Stacks Project, More on Étale Cohomology, Tags 0F4X, 0F4Y, 0F50, 0F51,
0F55 and 0F77 (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem support_cancel {Λ : Type (u + 1)} [CommRing Λ]
    {Y : Scheme.{u}}
    {F G H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (i : G ⟶ H) (hi : ∀ V : Y.Etale, Function.Injective (i.hom.app (op V)))
    {a b : F ⟶ G} (h : a ≫ i = b ≫ i) : a = b := by
  ext V s
  apply hi V.unop
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun k => k.hom) h) V) s

private theorem support_factor {Λ : Type (u + 1)} [CommRing Λ]
    {Y : Scheme.{u}}
    {F G H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (i : G ⟶ H) (hi : ∀ V : Y.Etale, Function.Injective (i.hom.app (op V)))
    (a : F ⟶ H)
    (hr : ∀ (V : Y.Etale) (s : F.obj.obj (op V)),
      ∃ t, i.hom.app (op V) t = a.hom.app (op V) s) :
    ∃ l : F ⟶ G, l ≫ i = a := by
  classical
  let l (V : Y.Etaleᵒᵖ) : F.obj.obj V ⟶ G.obj.obj V := ModuleCat.ofHom
    { toFun := fun s => Classical.choose (hr V.unop s)
      map_add' := by
        intro s t
        apply hi V.unop
        change i.hom.app V (Classical.choose (hr V.unop (s + t))) =
          i.hom.app V (Classical.choose (hr V.unop s) + Classical.choose (hr V.unop t))
        rw [Classical.choose_spec (hr V.unop (s + t))]
        rw [map_add, map_add, Classical.choose_spec (hr V.unop s),
          Classical.choose_spec (hr V.unop t)]
      map_smul' := by
        intro r s
        apply hi V.unop
        change i.hom.app V (Classical.choose (hr V.unop (r • s))) =
          i.hom.app V (r • Classical.choose (hr V.unop s))
        rw [Classical.choose_spec (hr V.unop (r • s))]
        rw [map_smul, map_smul, Classical.choose_spec (hr V.unop s)] }
  have hl (V : Y.Etaleᵒᵖ) (s : F.obj.obj V) :
      i.hom.app V (l V s) = a.hom.app V s := Classical.choose_spec (hr V.unop s)
  refine ⟨⟨{ app := l, naturality := ?_ }⟩, ?_⟩
  · intro V W h
    ext s
    apply hi W.unop
    symm
    change i.hom.app W (G.obj.map h (l V s)) = i.hom.app W (l W (F.obj.map h s))
    calc
      _ = H.obj.map h (i.hom.app V (l V s)) :=
        ConcreteCategory.congr_hom (i.hom.naturality h) (l V s)
      _ = H.obj.map h (a.hom.app V s) := by rw [hl]
      _ = a.hom.app W (F.obj.map h s) :=
        (ConcreteCategory.congr_hom (a.hom.naturality h) s).symm
      _ = _ := (hl W _).symm
  · ext V s
    exact hl V s

private theorem support_isoOfRange {Λ : Type (u + 1)} [CommRing Λ]
    {Y : Scheme.{u}}
    {F G H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : F ⟶ H) (b : G ⟶ H)
    (ha : ∀ V : Y.Etale, Function.Injective (a.hom.app (op V)))
    (hb : ∀ V : Y.Etale, Function.Injective (b.hom.app (op V)))
    (hr : ∀ (V : Y.Etale) (s : H.obj.obj (op V)),
      (∃ t, a.hom.app (op V) t = s) ↔ ∃ t, b.hom.app (op V) t = s) :
    ∃ o : F ≅ G, o.hom ≫ b = a := by
  obtain ⟨l, hl⟩ := support_factor b hb a (fun V s => (hr V _).1 ⟨s, rfl⟩)
  obtain ⟨m, hm⟩ := support_factor a ha b (fun V s => (hr V _).2 ⟨s, rfl⟩)
  refine ⟨⟨l, m, ?_, ?_⟩, hl⟩
  · apply support_cancel a ha
    simp only [Category.assoc, hm, hl, Category.id_comp]
  · apply support_cancel b hb
    simp only [Category.assoc, hl, hm, Category.id_comp]

private theorem support_functorIsoOfRange {Λ : Type (u + 1)} [CommRing Λ]
    {D : Type*} [Category* D] {Y : Scheme.{u}}
    {A B H : D ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : A ⟶ H) (b : B ⟶ H)
    (ha : ∀ (F : D) (V : Y.Etale), Function.Injective ((a.app F).hom.app (op V)))
    (hb : ∀ (F : D) (V : Y.Etale), Function.Injective ((b.app F).hom.app (op V)))
    (hr : ∀ (F : D) (V : Y.Etale) (s : (H.obj F).obj.obj (op V)),
      (∃ t, (a.app F).hom.app (op V) t = s) ↔
        ∃ t, (b.app F).hom.app (op V) t = s) :
    ∃ o : A ≅ B, o.hom ≫ b = a := by
  classical
  have hex F := support_isoOfRange (a.app F) (b.app F) (ha F) (hb F) (hr F)
  let o F := Classical.choose (hex F)
  have ho F : (o F).hom ≫ b.app F = a.app F := Classical.choose_spec (hex F)
  refine ⟨NatIso.ofComponents o (fun {F G} φ => ?_), ?_⟩
  · apply support_cancel (b.app G) (hb G)
    calc
      _ = A.map φ ≫ a.app G := by rw [Category.assoc, ho]
      _ = a.app F ≫ H.map φ := a.naturality φ
      _ = (o F).hom ≫ b.app F ≫ H.map φ := by rw [← Category.assoc, ho]
      _ = _ := by rw [← b.naturality φ, Category.assoc]
  · apply NatTrans.ext
    funext F
    exact ho F

private theorem support_upperStarComp_hom {Λ : Type (u + 1)} [CommRing Λ]
    {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : k = f ≫ g) :
    (upperStarComp (ModuleCat.{u + 1} Λ) f g k hk).hom =
      eqToHom (congrArg (upperStar (ModuleCat.{u + 1} Λ)) hk) ≫
        (upperStarComp (ModuleCat.{u + 1} Λ) f g).hom := by
  subst k
  simp

private theorem support_upperStarComp_inv {Λ : Type (u + 1)} [CommRing Λ]
    {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : k = f ≫ g) :
    (upperStarComp (ModuleCat.{u + 1} Λ) f g k hk).inv =
      (upperStarComp (ModuleCat.{u + 1} Λ) f g).inv ≫
        eqToHom (congrArg (upperStar (ModuleCat.{u + 1} Λ)) hk.symm) := by
  subst k
  simp

private theorem support_squareUpperStarIso {Λ : Type (u + 1)} [CommRing Λ]
    {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (a : X' ⟶ X) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
    (sq : CommSq a f' f b) :
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom =
      (upperStarComp (ModuleCat.{u + 1} Λ) f' b).inv ≫
        (upperStarComp (ModuleCat.{u + 1} Λ) a f (f' ≫ b) sq.w.symm).hom := by
  dsimp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom]
  rw [support_upperStarComp_inv f' b (a ≫ f) sq.w,
    support_upperStarComp_hom a f (f' ≫ b) sq.w.symm]
  simp only [Category.assoc]

set_option linter.unusedVariables false in
/-- The proper-support subsheaves form functors, with composition, proper and open
specializations, and base change compatible with composition.
Source: Stacks Project, Tags 0F4X, 0F4Y, 0F50, 0F51, 0F55, 0F77.
(auxiliary; not a blueprint node)

The functors and inclusions are specified together: objectwise their images are exactly
sections with the indicated closed geometric-germ support and proper reduced subscheme.
The composition isomorphism is specified by its composite into the ordinary direct image.
The base-change isomorphism is specified by the ordinary adjunction comparison.

Proof:
1. Use the literal submodule presheaf, sheaf and natural inclusion constructed in
lem-cbc-proper-support-section-calculus. Its sectionwise range theorem and the
separably-closed support criterion give exactly the first clause of the statement.
For proper maps every closed support is proper, so its inclusion is an isomorphism.
2. Two sectionwise injective maps of module sheaves with the same image have a unique
compatible isomorphism: factor each map through the other using unique preimages,
then cancel the injections to prove the inverse and naturality identities.
3. Apply this elementary construction to the composite support inclusion and the
inclusion for the composite map. Their images agree by
lem-cbc-proper-support-composite-range; the ordinary direct-image compositor and
subtype inclusions prove injectivity. This constructs c with its specified equation.
4. Apply the same construction to the open-immersion comparison, using
lem-cbc-open-extension-proper-support-range, to obtain its compatible isomorphism.
5. Apply it to the restricted ordinary base-change map, using
lem-cbc-proper-support-exchange-range, to construct e. Expanding squareUpperStarIso
and the ordinary mate gives exactly the unit/counit formula required here.
6. Postcompose both pasted support paths with the injective inclusion for the final
composite. Substitute the equations specifying c and e, use naturality, and apply
ordinary base-change mate pasting (lem-weil-pbc-mate-pasting). The two composites
agree, so injectivity cancels that inclusion and proves the final coherence. Every
factorization is linear and natural; uniqueness determines all chosen preimages. -/
theorem properSupportSheafComposition (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ (L : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f],
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (ι : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f],
        L f ⟶ lowerStar (ModuleCat.{u + 1} Λ) f),
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale),
        Function.Injective (((ι f).app F).hom.app (op V)) ∧
        ∀ s : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)),
          (∃ t, (((ι f).app F).hom.app (op V)) t = s) ↔
          ∃ T : TopologicalSpace.Closeds
              ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left,
            (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
              (v : Spec (.of Ω) ⟶
                ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left),
              v default ∈ T ↔
                (Scheme.pointSmallEtale
                  (v ≫ ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom)).toPresheafFiber
                    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
                    (Over.homMk v) F.obj s ≠ 0) ∧
            IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫
              pullback.fst V.hom f)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsProper f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso ((ι f).app F)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsOpenImmersion f],
        ∃ o : openImmersionLowerShriek (ModuleCat.{u + 1} Λ) f ≅ L f,
          o.hom ≫ ι f = openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) f) ∧
      ∃ (c : ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
          [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g],
          L f ⋙ L g ≅ L (f ≫ g))
        (e : ∀ (X Y X' Y' : Scheme.{u}) (f : X ⟶ Y) (a : X' ⟶ X)
          (b : Y' ⟶ Y) (f' : X' ⟶ Y') [IsSeparated f] [LocallyOfFiniteType f]
          [IsSeparated f'] [LocallyOfFiniteType f'] (sq : IsPullback a f' f b),
          L f ⋙ upperStar (ModuleCat.{u + 1} Λ) b ≅
            upperStar (ModuleCat.{u + 1} Λ) a ⋙ L f'),
        (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
          [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
          (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          (c X Y Z f g).hom.app F ≫ (ι (f ≫ g)).app F =
            (ι g).app ((L f).obj F) ≫
              (lowerStar (ModuleCat.{u + 1} Λ) g).map ((ι f).app F) ≫
              (lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app F) ∧
        (∀ (X Y X' Y' : Scheme.{u}) (f : X ⟶ Y) (a : X' ⟶ X)
          (b : Y' ⟶ Y) (f' : X' ⟶ Y') [IsSeparated f] [LocallyOfFiniteType f]
          [IsSeparated f'] [LocallyOfFiniteType f'] (sq : IsPullback a f' f b)
          (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          (e X Y X' Y' f a b f' sq).hom.app F ≫
              (ι f').app ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) =
            (upperStar (ModuleCat.{u + 1} Λ) b).map ((ι f).app F) ≫
              (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').unit.app
                ((upperStar (ModuleCat.{u + 1} Λ) b).obj
                  ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) ≫
              (lowerStar (ModuleCat.{u + 1} Λ) f').map
                ((upperStarComp (ModuleCat.{u + 1} Λ) f' b).inv.app
                  ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
                  (upperStarComp (ModuleCat.{u + 1} Λ) a f (f' ≫ b) sq.w.symm).hom.app
                    ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F)) ≫
              (lowerStar (ModuleCat.{u + 1} Λ) f').map
                ((upperStar (ModuleCat.{u + 1} Λ) a).map
                  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F))) ∧
        (∀ (X Y Z X' Y' Z' : Scheme.{u})
          (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
          (a : Z' ⟶ Z) (b : Y' ⟶ Y) (d : X' ⟶ X)
          [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
          [IsSeparated f'] [LocallyOfFiniteType f'] [IsSeparated g'] [LocallyOfFiniteType g']
          (sf : IsPullback d f' f b) (sg : IsPullback b g' g a)
          (sfg : IsPullback d (f' ≫ g') (f ≫ g) a)
          (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          (upperStar (ModuleCat.{u + 1} Λ) a).map ((c X Y Z f g).hom.app F) ≫
              (e X Z X' Z' (f ≫ g) d a (f' ≫ g') sfg).hom.app F =
            (e Y Z Y' Z' g b a g' sg).hom.app ((L f).obj F) ≫
              (L g').map ((e X Y X' Y' f d b f' sf).hom.app F) ≫
              (c X' Y' Z' f' g').hom.app
                ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) := by
  classical
  let L : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f],
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun f _ _ => properSupportLowerStar Λ f
  let ι : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f],
      L f ⟶ lowerStar (ModuleCat.{u + 1} Λ) f :=
    fun f _ _ => properSupportLowerStarInclusion Λ f
  have hi {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale) :
      Function.Injective (((ι f).app F).hom.app (op V)) :=
    (properSupportLowerStarInclusion_range Λ f F V).1
  have hcExists (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g] :
      ∃ c : L f ⋙ L g ≅ L (f ≫ g),
        c.hom ≫ ι (f ≫ g) =
          Functor.whiskerLeft (L f) (ι g) ≫
            Functor.whiskerRight (ι f) (lowerStar (ModuleCat.{u + 1} Λ) g) ≫
            (lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom := by
    apply support_functorIsoOfRange
    · intro F V
      have hcomp : Function.Injective
          (((lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app F).hom.app (op V)) :=
        (ConcreteCategory.isIso_iff_bijective _).1 (by infer_instance) |>.1
      exact hcomp.comp ((hi f F (g.Etale.obj V)).comp (hi g ((L f).obj F) V))
    · exact hi (f ≫ g)
    · intro F V s
      exact (properSupportComposite_range Λ f g F V s).trans
        ((properSupportLowerStarInclusion_range Λ (f ≫ g) F V).2 s).symm
  choose c hc using hcExists
  have heExists (X Y X' Y' : Scheme.{u}) (f : X ⟶ Y) (a : X' ⟶ X)
      (b : Y' ⟶ Y) (f' : X' ⟶ Y') [IsSeparated f] [LocallyOfFiniteType f]
      [IsSeparated f'] [LocallyOfFiniteType f'] (sq : IsPullback a f' f b) :
      ∃ e : L f ⋙ upperStar (ModuleCat.{u + 1} Λ) b ≅
          upperStar (ModuleCat.{u + 1} Λ) a ⋙ L f',
        e.hom ≫ Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) a) (ι f') =
          Functor.whiskerRight (ι f) (upperStar (ModuleCat.{u + 1} Λ) b) ≫
            baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq := by
    apply support_functorIsoOfRange
    · intro F V
      exact (properSupportExchange_range Λ f a b f' sq F V).1
    · intro F V
      exact hi f' ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) V
    · intro F V s
      exact ((properSupportExchange_range Λ f a b f' sq F V).2 s).trans
        ((properSupportLowerStarInclusion_range Λ f'
          ((upperStar (ModuleCat.{u + 1} Λ) a).obj F) V).2 s).symm
  choose e he using heExists
  refine ⟨L, ι, ?_, ?_, ?_, c, e, ?_, ?_, ?_⟩
  · intro X Y f _ _ F V
    refine ⟨hi f F V, fun s => ?_⟩
    exact ((properSupportLowerStarInclusion_range Λ f F V).2 s).trans
      ((properSupportSectionCalculus Λ f).2.2.2.2.1 F V s)
  · intro X Y f _ F
    exact properSupportLowerStarInclusion_isIso Λ f F
  · intro X Y f _
    apply support_functorIsoOfRange
    · intro F V
      exact (openExtensionProperSupport_range Λ f F V).1
    · exact hi f
    · intro F V s
      exact ((openExtensionProperSupport_range Λ f F V).2 s).trans
        ((properSupportLowerStarInclusion_range Λ f F V).2 s).symm
  · intro X Y Z f g _ _ _ _ F
    exact NatTrans.congr_app (hc X Y Z f g) F
  · intro X Y X' Y' f a b f' _ _ _ _ sq F
    have h := NatTrans.congr_app (he X Y X' Y' f a b f' sq) F
    rw [baseChangeMap, support_squareUpperStarIso] at h
    simpa [mateEquiv, Functor.map_comp, Category.assoc] using h
  · intro X Y Z X' Y' Z' f g f' g' a b d _ _ _ _ _ _ _ _ sf sg sfg F
    have hcf := NatTrans.congr_app (hc X Y Z f g) F
    have hcf' := NatTrans.congr_app (hc X' Y' Z' f' g')
      ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)
    have hef := NatTrans.congr_app (he X Y X' Y' f d b f' sf) F
    have heg := NatTrans.congr_app (he Y Z Y' Z' g b a g' sg) ((L f).obj F)
    have hefg := NatTrans.congr_app
      (he X Z X' Z' (f ≫ g) d a (f' ≫ g') sfg) F
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      at hcf hcf' hef heg hefg
    have hp :
        (upperStar (ModuleCat.{u + 1} Λ) a).map
            ((lowerStarComp (ModuleCat.{u + 1} Λ) f g).hom.app F) ≫
          (baseChangeMap (ModuleCat.{u + 1} Λ) sfg.toCommSq).app F =
        (baseChangeMap (ModuleCat.{u + 1} Λ) sg.toCommSq).app
            ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g').map
            ((baseChangeMap (ModuleCat.{u + 1} Λ) sf.toCommSq).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) f' g').hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) d).obj F) := by
      rw [baseChangeMap_paste_vert_app (ModuleCat.{u + 1} Λ)
        sf.toCommSq sg.toCommSq sfg.toCommSq F]
      simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
      dsimp only [Functor.comp_obj]
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    apply support_cancel ((ι (f' ≫ g')).app
      ((upperStar (ModuleCat.{u + 1} Λ) d).obj F))
      (hi (f' ≫ g') ((upperStar (ModuleCat.{u + 1} Λ) d).obj F))
    calc
      _ = (upperStar (ModuleCat.{u + 1} Λ) a).map
          ((c X Y Z f g).hom.app F ≫ (ι (f ≫ g)).app F) ≫
          (baseChangeMap (ModuleCat.{u + 1} Λ) sfg.toCommSq).app F := by
        rw [Category.assoc, hefg, ← Category.assoc, ← Functor.map_comp]
      _ = (upperStar (ModuleCat.{u + 1} Λ) a).map
          ((ι g).app ((L f).obj F)) ≫
          (upperStar (ModuleCat.{u + 1} Λ) a).map
            ((lowerStar (ModuleCat.{u + 1} Λ) g).map ((ι f).app F)) ≫
          (baseChangeMap (ModuleCat.{u + 1} Λ) sg.toCommSq).app
            ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g').map
            ((baseChangeMap (ModuleCat.{u + 1} Λ) sf.toCommSq).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) f' g').hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) d).obj F) := by
        rw [hcf]
        simp only [Functor.map_comp, Category.assoc]
        rw [hp]
      _ = (upperStar (ModuleCat.{u + 1} Λ) a).map
          ((ι g).app ((L f).obj F)) ≫
          (baseChangeMap (ModuleCat.{u + 1} Λ) sg.toCommSq).app ((L f).obj F) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g').map
            ((upperStar (ModuleCat.{u + 1} Λ) b).map ((ι f).app F)) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g').map
            ((baseChangeMap (ModuleCat.{u + 1} Λ) sf.toCommSq).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) f' g').hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) d).obj F) := by
        have hn := (baseChangeMap (ModuleCat.{u + 1} Λ) sg.toCommSq).naturality
          ((ι f).app F)
        simpa only [Functor.comp_map, Category.assoc] using
          congrArg (fun k => (upperStar (ModuleCat.{u + 1} Λ) a).map
            ((ι g).app ((L f).obj F)) ≫ k ≫
            (lowerStar (ModuleCat.{u + 1} Λ) g').map
              ((baseChangeMap (ModuleCat.{u + 1} Λ) sf.toCommSq).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} Λ) f' g').hom.app
              ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) hn
      _ = (e Y Z Y' Z' g b a g' sg).hom.app ((L f).obj F) ≫
          (ι g').app ((upperStar (ModuleCat.{u + 1} Λ) b).obj ((L f).obj F)) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g').map
            ((e X Y X' Y' f d b f' sf).hom.app F) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g').map
            ((ι f').app ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) f' g').hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) d).obj F) := by
        have h₁ := congrArg (fun k =>
          (upperStar (ModuleCat.{u + 1} Λ) a).map ((ι g).app ((L f).obj F)) ≫
            (baseChangeMap (ModuleCat.{u + 1} Λ) sg.toCommSq).app ((L f).obj F) ≫
            (lowerStar (ModuleCat.{u + 1} Λ) g').map k ≫
            (lowerStarComp (ModuleCat.{u + 1} Λ) f' g').hom.app
              ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) hef
        have h₂ := congrArg (fun k => k ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g').map
            ((e X Y X' Y' f d b f' sf).hom.app F) ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g').map
            ((ι f').app ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) f' g').hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) heg
        simp only [Functor.map_comp, Category.assoc] at h₁ h₂
        exact h₁.symm.trans h₂.symm
      _ = _ := by
        have hn := (ι g').naturality ((e X Y X' Y' f d b f' sf).hom.app F)
        have h := congrArg (fun k =>
          (e Y Z Y' Z' g b a g' sg).hom.app ((L f).obj F) ≫ k ≫
          (lowerStar (ModuleCat.{u + 1} Λ) g').map
            ((ι f').app ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) f' g').hom.app
            ((upperStar (ModuleCat.{u + 1} Λ) d).obj F)) hn
        dsimp only [Functor.comp_obj] at h
        simpa only [Category.assoc, hcf'] using h.symm

end AlgebraicGeometry.Etale
