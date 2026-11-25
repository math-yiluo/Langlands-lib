/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.AlgebraicGeometry.EtaleGraphDiagonalNormalization
import WeilConjectures.AlgebraicGeometry.EtaleGraphFromOpenBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleGraphRefinementNormalization
import WeilConjectures.AlgebraicGeometry.EtalePairwiseProductGraphNormalization

/-! # Cocycle and base change for the specified proper/open/proper graph comparisons

Source: Stacks Project, Tags 0F7C--0F7F; the product-graph formula in
`LowerShriekComposition.lean`, lines 193--268, and the refinement formula in
`LowerShriekIndependenceUnbounded.lean`
(auxiliary; not a blueprint node).

All maps below are constructed from the recorded graph model and canonical exchanges.
The base-change clause is stated for arbitrary Cartesian representatives of the pulled-back
presentations, so it includes the chosen fibre product and every isomorphic representative.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryNatIso

private theorem inverse_exchange
    {C D : Type*} [Category* C] [Category* D]
    {F G : C} {F' G' : D} (P : C ⥤ D)
    (e : F ≅ G) (e' : F' ≅ G')
    (a : P.obj F ⟶ F') (b : P.obj G ⟶ G')
    (h : P.map e.hom ≫ b = a ≫ e'.hom) :
    P.map e.inv ≫ a = b ≫ e'.inv := by
  apply (cancel_mono e'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, ← P.map_comp, Iso.inv_hom_id, P.map_id, Category.id_comp]

private theorem quotient_exchange
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (P : C ⥤ D) (Q : E ⥤ D)
    {F S T : C} {F' S' T' : E}
    (es : F ≅ S) (et : F ≅ T) (es' : F' ≅ S') (et' : F' ≅ T')
    (a : P.obj F ⟶ Q.obj F') (b : P.obj S ⟶ Q.obj S')
    (c : P.obj T ⟶ Q.obj T')
    (hs : P.map es.hom ≫ b = a ≫ Q.map es'.hom)
    (ht : P.map et.hom ≫ c = a ≫ Q.map et'.hom) :
    P.map (es.symm ≪≫ et).hom ≫ c = b ≫ Q.map (es'.symm ≪≫ et').hom := by
  have hi := inverse_exchange P es (Q.mapIso es') a b hs
  simp only [Iso.trans_hom, Iso.symm_hom, P.map_comp, Q.map_comp]
  rw [Category.assoc, ht, ← Category.assoc, hi]
  exact Category.assoc _ _ _

private theorem exchange_pair
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (P : C ⥤ D) (Q : E ⥤ D)
    {S T : C} {S' T' : E} (e : S ≅ T) (e' : S' ≅ T')
    (a : P.obj S ⟶ Q.obj S') (b : P.obj T ⟶ Q.obj T')
    (h : P.map e.hom ≫ b = a ≫ Q.map e'.hom) :
    (P.map e.hom ≫ b = a ≫ Q.map e'.hom) ∧
      (P.map e.inv ≫ a = b ≫ Q.map e'.inv) := by
  exact ⟨h, inverse_exchange P e (Q.mapIso e') a b h⟩

private theorem whiskered_exchange_pair
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (P : D ⥤ D') (Q : C ⥤ C')
    {S T : C ⥤ D} {S' T' : C' ⥤ D'} (e : S ≅ T) (e' : S' ≅ T')
    (a : S ⋙ P ⟶ Q ⋙ S') (b : T ⋙ P ⟶ Q ⋙ T')
    (h : Functor.whiskerRight e.hom P ≫ b = a ≫ Functor.whiskerLeft Q e'.hom) :
    (Functor.whiskerRight e.hom P ≫ b = a ≫ Functor.whiskerLeft Q e'.hom) ∧
      (Functor.whiskerRight e.inv P ≫ a = b ≫ Functor.whiskerLeft Q e'.inv) := by
  exact exchange_pair ((Functor.whiskeringRight _ _ _).obj P)
    ((Functor.whiskeringLeft _ _ _).obj Q) e e' a b h

private theorem whiskered_quotient_exchange
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (P : D ⥤ D') (Q : C ⥤ C')
    {F S T : C ⥤ D} {F' S' T' : C' ⥤ D'}
    (es : F ≅ S) (et : F ≅ T) (es' : F' ≅ S') (et' : F' ≅ T')
    (a : F ⋙ P ⟶ Q ⋙ F') (b : S ⋙ P ⟶ Q ⋙ S') (c : T ⋙ P ⟶ Q ⋙ T')
    (hs : Functor.whiskerRight es.hom P ≫ b = a ≫ Functor.whiskerLeft Q es'.hom)
    (ht : Functor.whiskerRight et.hom P ≫ c = a ≫ Functor.whiskerLeft Q et'.hom) :
    Functor.whiskerRight (es.symm ≪≫ et).hom P ≫ c =
      b ≫ Functor.whiskerLeft Q (es'.symm ≪≫ et').hom := by
  exact quotient_exchange ((Functor.whiskeringRight _ _ _).obj P)
    ((Functor.whiskeringLeft _ _ _).obj Q) es et es' et' a b c hs ht

/-- Independence, open normalization, identity, cocycle, arbitrary base change (also for
inverses), and common-refinement normalization of the specified graph comparisons.

Source: Stacks Project, Tags 0F7C--0F7F; `LowerShriekComposition.lean`, lines 193--268;
`LowerShriekIndependenceUnbounded.lean`, refinement comparison and common-refinement iso
(auxiliary; not a blueprint node).

Proof:
1. Apply the pairwise-product graph normalization for c and d. Its right side does
   not mention either auxiliary compactification, giving independence.
2. Change the auxiliary compactification to d. The diagonal graph normalization
   identifies B(d,d) with the inverse open normalization. Substitution gives the
   open-normalization clause.
3. Identity and cocycle for a fixed c follow by cancelling adjacent inverse B maps.
4. Put E_t = openNormalization(c);B(c,t). The single-graph base-change theorem gives
   exchange compatibility for each E. Cancel the common open normalizations to write
   C(s,t) = E_s^{-1};E_t. Compatibility is preserved by composition and inverse of
   the E factors; only these isomorphisms are cancelled, never an exchange map.
5. Factor C(s,t) through C(s,r);C(t,r)^{-1}. Open normalization and the one-refinement
   normalization identify these factors with the two specified refinement maps.
6. Specialize to Compactification.inf s t and unfold the named common-refinement iso.
   QuasiCompact is used only for this last choice; all prior clauses retain the
   arbitrary-scheme and unbounded hypotheses. -/
theorem etaleGraphComparisonBaseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (∀ (d : Compactification f) (s t : EtaleGraphPresentation f),
      etaleGraphComparison A c s t = etaleGraphComparison A d s t) ∧
    (∀ (d : Compactification f) (t : EtaleGraphPresentation f),
      etaleGraphComparison A c (EtaleGraphPresentation.ofCompactification d) t =
        etaleGraphOpenNormalization A d ≪≫ etaleGraphComparisonFromOpen A d t) ∧
    (∀ (s : EtaleGraphPresentation f), etaleGraphComparison A c s s = Iso.refl _) ∧
    (∀ (s t r : EtaleGraphPresentation f),
      etaleGraphComparison A c s t ≪≫ etaleGraphComparison A c t r =
        etaleGraphComparison A c s r) ∧
    (∀ {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (v : X' ⟶ X) (b : Y' ⟶ Y)
      (sq : IsPullback v f' f b) (s t : EtaleGraphPresentation f)
      (s' t' : EtaleGraphPresentation f')
      (ds : s.BaseChange s' v b) (dt : t.BaseChange t' v b),
      Functor.whiskerRight (etaleGraphComparison A c s t).hom
          D((b)^*[ModuleCat.{u + 1} A]) ≫ etaleGraphPresentationExchange A dt =
        etaleGraphPresentationExchange A ds ≫
          Functor.whiskerLeft D((v)^*[ModuleCat.{u + 1} A])
            (etaleGraphComparison A (c.ofIsPullback sq) s' t').hom ∧
      Functor.whiskerRight (etaleGraphComparison A c s t).inv
          D((b)^*[ModuleCat.{u + 1} A]) ≫ etaleGraphPresentationExchange A ds =
        etaleGraphPresentationExchange A dt ≫
          Functor.whiskerLeft D((v)^*[ModuleCat.{u + 1} A])
            (etaleGraphComparison A (c.ofIsPullback sq) s' t').inv) ∧
    (∀ [QuasiCompact f] (s t r : Compactification f)
      (rs : r.Refinement s) (rt : r.Refinement t)
      (hs : IsPullback r.i (𝟙 X) rs.hom s.i)
      (ht : IsPullback r.i (𝟙 X) rt.hom t.i),
      etaleGraphComparison A c (EtaleGraphPresentation.ofCompactification s)
          (EtaleGraphPresentation.ofCompactification t) =
        etaleGraphOpenNormalization A s ≪≫
          asIso (rightDerivedLowerShriekOfCompactificationComparison
            (ModuleCat.{u + 1} A) rs hs) ≪≫
          (asIso (rightDerivedLowerShriekOfCompactificationComparison
            (ModuleCat.{u + 1} A) rt ht)).symm ≪≫
          (etaleGraphOpenNormalization A t).symm) ∧
    (∀ [QuasiCompact f] (s t : Compactification f),
      etaleGraphComparison A c (EtaleGraphPresentation.ofCompactification s)
          (EtaleGraphPresentation.ofCompactification t) =
        etaleGraphOpenNormalization A s ≪≫
          rightDerivedLowerShriekOfCompactificationIso A s t ≪≫
          (etaleGraphOpenNormalization A t).symm) := by
  have hind (d : Compactification f) (s t : EtaleGraphPresentation f) :
      etaleGraphComparison A c s t = etaleGraphComparison A d s t := by
    rw [etalePairwiseProductGraphNormalization A c s t,
      etalePairwiseProductGraphNormalization A d s t]
  have hopen (d : Compactification f) (t : EtaleGraphPresentation f) :
      etaleGraphComparison A c (EtaleGraphPresentation.ofCompactification d) t =
        etaleGraphOpenNormalization A d ≪≫ etaleGraphComparisonFromOpen A d t := by
    rw [hind d]
    dsimp only [etaleGraphComparison]
    rw [etaleGraphComparison_diagonal A d, Iso.symm_symm_eq]
  have href [QuasiCompact f] (s t r : Compactification f)
      (rs : r.Refinement s) (rt : r.Refinement t)
      (hs : IsPullback r.i (𝟙 X) rs.hom s.i)
      (ht : IsPullback r.i (𝟙 X) rt.hom t.i) :
      etaleGraphComparison A c (EtaleGraphPresentation.ofCompactification s)
          (EtaleGraphPresentation.ofCompactification t) =
        etaleGraphOpenNormalization A s ≪≫
          asIso (rightDerivedLowerShriekOfCompactificationComparison
            (ModuleCat.{u + 1} A) rs hs) ≪≫
          (asIso (rightDerivedLowerShriekOfCompactificationComparison
            (ModuleCat.{u + 1} A) rt ht)).symm ≪≫
          (etaleGraphOpenNormalization A t).symm := by
    have hfactor :
        etaleGraphComparison A c (EtaleGraphPresentation.ofCompactification s)
            (EtaleGraphPresentation.ofCompactification t) =
          etaleGraphComparison A c (EtaleGraphPresentation.ofCompactification s)
              (EtaleGraphPresentation.ofCompactification r) ≪≫
            (etaleGraphComparison A c (EtaleGraphPresentation.ofCompactification t)
              (EtaleGraphPresentation.ofCompactification r)).symm := by
      simp only [etaleGraphComparison, Iso.trans_symm, Iso.symm_symm_eq,
        Iso.trans_assoc, Iso.self_symm_id_assoc]
    rw [hfactor, hopen, hopen, etaleGraphFromOpen_refinement A s r rs hs,
      etaleGraphFromOpen_refinement A t r rt ht]
    simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]
  refine ⟨hind, hopen, ?_, ?_, ?_, href, ?_⟩
  · intro s
    simpa only [etaleGraphComparison] using
      Iso.symm_self_id (etaleGraphComparisonFromOpen A c s)
  · intro s t r
    simp only [etaleGraphComparison, Iso.trans_assoc, Iso.self_symm_id_assoc]
  · intro X' Y' f' v b sq s t s' t' ds dt
    let cb := c.ofIsPullback sq
    let es := etaleGraphOpenNormalization A c ≪≫ etaleGraphComparisonFromOpen A c s
    let et := etaleGraphOpenNormalization A c ≪≫ etaleGraphComparisonFromOpen A c t
    let es' := etaleGraphOpenNormalization A cb ≪≫ etaleGraphComparisonFromOpen A cb s'
    let et' := etaleGraphOpenNormalization A cb ≪≫ etaleGraphComparisonFromOpen A cb t'
    have hs := etaleGraphFromOpen_baseChange A c v b sq s s' ds
    have ht := etaleGraphFromOpen_baseChange A c v b sq t t' dt
    have he : etaleGraphComparison A c s t = es.symm ≪≫ et := by
      simp only [es, et, etaleGraphComparison, Iso.trans_symm, Iso.trans_assoc,
        Iso.symm_self_id_assoc]
    have he' : etaleGraphComparison A cb s' t' = es'.symm ≪≫ et' := by
      simp only [es', et', etaleGraphComparison, Iso.trans_symm, Iso.trans_assoc,
        Iso.symm_self_id_assoc]
    have hforward :
        Functor.whiskerRight (etaleGraphComparison A c s t).hom
            D((b)^*[ModuleCat.{u + 1} A]) ≫ etaleGraphPresentationExchange A dt =
          etaleGraphPresentationExchange A ds ≫
            Functor.whiskerLeft D((v)^*[ModuleCat.{u + 1} A])
              (etaleGraphComparison A cb s' t').hom := by
      rw [he, he']
      exact whiskered_quotient_exchange D((b)^*[ModuleCat.{u + 1} A])
        D((v)^*[ModuleCat.{u + 1} A]) es et es' et' _ _ _ hs ht
    exact whiskered_exchange_pair D((b)^*[ModuleCat.{u + 1} A])
      D((v)^*[ModuleCat.{u + 1} A]) (etaleGraphComparison A c s t)
      (etaleGraphComparison A cb s' t') (etaleGraphPresentationExchange A ds)
      (etaleGraphPresentationExchange A dt) hforward
  · intro hqc s t
    simpa only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_assoc] using
      href s t (Compactification.inf s t) (Compactification.infFst s t)
        (Compactification.infSnd s t) (Compactification.isPullback_infFst s t)
        (Compactification.isPullback_infSnd s t)

end AlgebraicGeometry.Etale
