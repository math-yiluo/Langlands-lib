/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.RingedHomRestrictionComparison

/-! # Composition of augmentation-normalized internal Hom comparisons

Source: Stacks Project, Tags 08J7, 0A95 and 08JB.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingedHomRestriction

open Opposite

private abbrev pair {A : Type*} [Category A] {L I L' I' : A}
    (x : L ≅ L') (y : I ≅ I') : (op L, I) ⟶ (op L', I') :=
  (x.inv.op, y.hom)

section Pasting
variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C]
  [Category A'] [Category B'] [Category C']
  (H : Aᵒᵖ × A ⥤ A) (J : Bᵒᵖ × B ⥤ B) (K : Cᵒᵖ × C ⥤ C)
  (H' : A'ᵒᵖ × A' ⥤ A') (J' : B'ᵒᵖ × B' ⥤ B') (K' : C'ᵒᵖ × C' ⥤ C')
  (Q : A ⥤ A') (T : B ⥤ B') (U : C ⥤ C')
  (α : H ⋙ Q ⟶ (Q.op.prod Q) ⋙ H')
  (β : J ⋙ T ⟶ (T.op.prod T) ⋙ J')
  (γ : K ⋙ U ⟶ (U.op.prod U) ⋙ K')
  (F : A ⥤ B) (G : B ⥤ C) (V : A ⥤ C)
  (f : A' ⥤ B') (g : B' ⥤ C') (v : A' ⥤ C')
  (c : F ⋙ G ≅ V) (d : f ⋙ g ≅ v)
  (t : Q ⋙ f ≅ F ⋙ T) (r : T ⋙ g ≅ G ⋙ U) (z : Q ⋙ v ≅ V ⋙ U)
  (a : H ⋙ F ≅ (F.op.prod F) ⋙ J)
  (b : J ⋙ G ≅ (G.op.prod G) ⋙ K)
  (e : H' ⋙ f ≅ (f.op.prod f) ⋙ J')
  (s : J' ⋙ g ≅ (g.op.prod g) ⋙ K')

private theorem paste_equation (L I : A)
    (he : f.map (α.app (op L, I)) ≫ e.hom.app (op (Q.obj L), Q.obj I) ≫
      J'.map (pair (t.app L) (t.app I)) =
      t.hom.app (H.obj (op L, I)) ≫ T.map (a.hom.app (op L, I)) ≫
        β.app (op (F.obj L), F.obj I))
    (hs : g.map (β.app (op (F.obj L), F.obj I)) ≫
      s.hom.app (op (T.obj (F.obj L)), T.obj (F.obj I)) ≫
      K'.map (pair (r.app (F.obj L)) (r.app (F.obj I))) =
      r.hom.app (J.obj (op (F.obj L), F.obj I)) ≫
        U.map (b.hom.app (op (F.obj L), F.obj I)) ≫
        γ.app (op (G.obj (F.obj L)), G.obj (F.obj I)))
    (hz : ∀ X : A, d.hom.app (Q.obj X) ≫ z.hom.app X =
      g.map (t.hom.app X) ≫ r.hom.app (F.obj X) ≫ U.map (c.hom.app X)) :
    v.map (α.app (op L, I)) ≫
      (composite d e s).hom.app (op (Q.obj L), Q.obj I) ≫
      K'.map (pair (z.app L) (z.app I)) =
    z.hom.app (H.obj (op L, I)) ≫
      U.map ((composite c a b).hom.app (op L, I)) ≫
      γ.app (op (V.obj L), V.obj I) := by
  have hz' (X : A) : d.app (Q.obj X) ≪≫ z.app X =
      g.mapIso (t.app X) ≪≫ r.app (F.obj X) ≪≫ U.mapIso (c.app X) := by
    apply Iso.ext
    exact hz X
  have hp : K'.map (pair (d.app (Q.obj L)) (d.app (Q.obj I))) ≫
      K'.map (pair (z.app L) (z.app I)) =
      K'.map (pair (g.mapIso (t.app L)) (g.mapIso (t.app I))) ≫
      K'.map (pair (r.app (F.obj L)) (r.app (F.obj I))) ≫
      K'.map (pair (U.mapIso (c.app L)) (U.mapIso (c.app I))) := by
    simp only [← K'.map_comp]
    congr 1
    have hL := congrArg Iso.inv (hz' L)
    have hI := congrArg Iso.hom (hz' I)
    apply Prod.ext
    · simpa only [pair, Iso.trans_inv, Functor.mapIso_inv, op_comp,
        prod_comp, Prod.mkHom, Category.assoc] using
        congrArg Quiver.Hom.op hL
    · exact hI
  have hpaste :
      g.map (f.map (α.app (op L, I))) ≫
        g.map (e.hom.app (op (Q.obj L), Q.obj I)) ≫
        s.hom.app (op (f.obj (Q.obj L)), f.obj (Q.obj I)) ≫
        K'.map (pair (g.mapIso (t.app L)) (g.mapIso (t.app I))) ≫
        K'.map (pair (r.app (F.obj L)) (r.app (F.obj I))) =
      g.map (t.hom.app (H.obj (op L, I))) ≫
        r.hom.app (F.obj (H.obj (op L, I))) ≫
        U.map (G.map (a.hom.app (op L, I))) ≫
        U.map (b.hom.app (op (F.obj L), F.obj I)) ≫
        γ.app (op (G.obj (F.obj L)), G.obj (F.obj I)) := by
    have hn := s.hom.naturality (pair (t.app L) (t.app I))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map,
      pair, Functor.mapIso_inv, Functor.mapIso_hom, unop_op] at hn ⊢
    have he' := congrArg g.map he
    simp only [g.map_comp] at he'
    erw [← reassoc_of% hn, reassoc_of% he', hs,
      ← r.hom.naturality_assoc (a.hom.app (op L, I))]
    rfl
  apply (cancel_epi (d.hom.app (Q.obj (H.obj (op L, I))))).1
  simp only [composite, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, pairIso, NatIso.ofComponents_hom_app,
    Iso.prod_hom, Iso.op_hom, Category.assoc]
  erw [← d.hom.naturality_assoc (α.app (op L, I))]
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.op_obj, unop_op]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]
  change g.map (f.map (α.app (op L, I))) ≫
    g.map (e.hom.app (op (Q.obj L), Q.obj I)) ≫
    s.hom.app (op (f.obj (Q.obj L)), f.obj (Q.obj I)) ≫
    K'.map (pair (d.app (Q.obj L)) (d.app (Q.obj I))) ≫
    K'.map (pair (z.app L) (z.app I)) = _
  rw [← Category.assoc, hp]
  simp only [Category.assoc]
  rw [reassoc_of% hpaste, reassoc_of% (hz (H.obj (op L, I)))]
  simp only [Functor.map_comp, Category.assoc]
  rw [← U.map_comp_assoc (c.hom.app (H.obj (op L, I)))
    (c.inv.app (H.obj (op L, I))), Iso.hom_inv_id_app, U.map_id, Category.id_comp]
  have hn := γ.naturality (pair (c.app L) (c.app I))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map,
    pair, Functor.mapIso_inv, Functor.mapIso_hom, unop_op] at hn ⊢
  erw [hn]
  rfl

end Pasting

/-- Composing normalized Hom comparisons preserves their representative equation.
This concerns specified ordinary and derived comparisons; it asserts neither their existence
nor compatibility of an independently specified direct comparison.

Source: Stacks Project, Tag 08JB, identity of successive restrictions, with the representative
calculation of Tags 08J7 and 0A95.
(auxiliary; not a blueprint node).

Proof: fix a complex L and a K-injective I. Normalize the first comparison on L,I and apply
G to its equation. The complex F(I) is K-injective, so normalize the second comparison on
F(L),F(I). Naturality of the second derived comparison moves the two F-localization
factorizations through it. The composite exact-functor factorization identifies the resulting
G(F(L)) and G(F(I)) terms with those for F composed with G. Finally use naturality of the
augmentation for the complex isomorphism induced by c. The factorization equations for
mapDerivedCategoryCompIso and mapDerivedCategoryNatIso identify precisely the composition
comparison used in the statement. Cancel the invertible intermediate factorizations. What
remains is the Normalized equation for the ordinary and derived composites. All equations
are natural; no boundedness or extra resolution choice is involved. -/
theorem composite_normalized
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {N : GrothendieckTopology E}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (Z : Sheaf N CommRingCat.{u})
    [HasDerivedCategory.{w} (Modules R)] [HasDerivedCategory.{w} (Modules S)]
    [HasDerivedCategory.{w} (Modules Z)]
    (F : Modules R ⥤ Modules S) (G : Modules S ⥤ Modules Z) (V : Modules R ⥤ Modules Z)
    [F.Additive] [G.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : F ⋙ G ≅ V)
    (hF : ∀ I : Complex R, I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (.up ℤ)).obj I))
    (a : ordinary R ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).op.prod
        (F.mapHomologicalComplex (.up ℤ))) ⋙ ordinary S)
    (b : ordinary S ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      ((G.mapHomologicalComplex (.up ℤ)).op.prod
        (G.mapHomologicalComplex (.up ℤ))) ⋙ ordinary Z)
    (e : derivedInternalHom.{u, w} J R ⋙ F.mapDerivedCategory ≅
      (F.mapDerivedCategory.op.prod F.mapDerivedCategory) ⋙ derivedInternalHom.{u, w} K S)
    (s : derivedInternalHom.{u, w} K S ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.op.prod G.mapDerivedCategory) ⋙ derivedInternalHom.{u, w} N Z)
    (he : Normalized R S F a e) (hs : Normalized S Z G b s) :
    Normalized R Z V (composite (Functor.mapHomologicalComplexCompIso c (.up ℤ)) a b)
      (composite (Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.mapDerivedCategoryNatIso c) e s) := by
  intro L I hI
  have : CochainComplex.IsKInjective
      ((F.mapHomologicalComplex (.up ℤ)).obj I) := hF I hI
  let d := Functor.mapDerivedCategoryCompIso F G ≪≫
    Functor.mapDerivedCategoryNatIso c
  have hz (X : Complex R) :
      d.hom.app (DerivedCategory.Q.obj X) ≫ V.mapDerivedCategoryFactors.hom.app X =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app X) := by
    have h := Functor.mapDerivedCategoryCompIso_fac F G X
    have hc : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (.up ℤ)).hom.app X = 𝟙 _ := rfl
    erw [hc, DerivedCategory.Q.map_id, Category.comp_id] at h
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
      (DerivedCategory.Q.obj X))).1
    dsimp only [d, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [Functor.mapDerivedCategoryNatIso_fac, ← h]
    simp only [Category.assoc]
    rfl
  exact paste_equation (ordinary R) (ordinary S) (ordinary Z)
    (derivedInternalHom.{u, w} J R) (derivedInternalHom.{u, w} K S)
    (derivedInternalHom.{u, w} N Z)
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (augmentation J R) (augmentation K S) (augmentation N Z)
    (F.mapHomologicalComplex (.up ℤ)) (G.mapHomologicalComplex (.up ℤ))
    (V.mapHomologicalComplex (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory V.mapDerivedCategory
    (Functor.mapHomologicalComplexCompIso c (.up ℤ)) d
    F.mapDerivedCategoryFactors G.mapDerivedCategoryFactors V.mapDerivedCategoryFactors
    a b e s L I (he L I) (hs _ _) hz

end CategoryTheory.RingedHomRestriction
