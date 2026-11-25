/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomologyEvaluationRestrictionComparison
import WeilConjectures.Algebra.Homology.HomologyEvaluationRoofNaturality

/-! # Compatibility of homology evaluation with a quasi-isomorphism roof

Source: Stacks Project, Tags 0A8X, 0A95, and 08DL. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

private theorem homComplex_precomp_homology_isIso
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    {R : Sheaf S CommRingCat.{u}}
    {A B K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (t : A ⟶ B) [K.IsKInjective] [QuasiIso t] (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      (((homComplexFunctor (R := R)).map t.op).app K) n) := by
  have h := quasiIso_homComplex_map (𝟙 K) t
  simp only [Functor.map_id, Category.comp_id] at h
  let : QuasiIso (((homComplexFunctor (R := R)).map t.op).app K) := h
  infer_instance

private theorem homologyEvaluation_compose_roof_square
    {C : Type*} [Category C] {M₁ N₁ U₁ V₁ P₁ Q₁ Z₁ Y₁ : C}
    (e : M₁ ⟶ N₁) (g : U₁ ⟶ V₁) (f : P₁ ⟶ Q₁)
    (a₀ : M₁ ≅ U₁) (b₀ : N₁ ≅ V₁) (aq : U₁ ≅ Z₁) (ap : P₁ ≅ Z₁)
    (bq : V₁ ≅ Y₁) (bp : Q₁ ≅ Y₁)
    (h₀ : e ≫ b₀.hom = a₀.hom ≫ g)
    (hs : g ≫ bq.hom = aq.hom ≫ ap.inv ≫ f ≫ bp.hom) :
    e ≫ (b₀ ≪≫ bq ≪≫ bp.symm).hom =
      (a₀ ≪≫ aq ≪≫ ap.symm).hom ≫ f := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    _ = ((e ≫ b₀.hom) ≫ bq.hom) ≫ bp.inv := by simp only [Category.assoc]
    _ = a₀.hom ≫ (g ≫ bq.hom) ≫ bp.inv := by rw [h₀]; simp only [Category.assoc]
    _ = _ := by rw [hs]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Cycle-compatible evaluations on a small site are compatible with a quasi-isomorphism
roof when the target complex is K-injective. The roof argument is independent of restriction. -/
private theorem homologyEvaluation_roof_of_cycle_pairings
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    {R : Sheaf S CommRingCat.{u}}
    (A E L K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℤ) (q : L ⟶ A) (p : L ⟶ E)
    [K.IsKInjective] [QuasiIso q] [QuasiIso p]
    {M N : SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (e : M ⟶ N)
    (f : (homComplex (R := R) E K).homology n ⟶
      SheafOfModules.homObj (R := R) (E.homology (-n)) (K.homology 0))
    (c : (homComplex (R := R) E K).cycles n ⟶
      SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0))
    (hc : c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
      (homComplex (R := R) E K).iCycles n ≫
        (Classical.choose (homComplex_projections_exists (R := R))) E K n (-n) 0
          (by omega) ≫ SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _))
    (hc' : c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
      (homComplex (R := R) E K).homologyπ n ≫ f ≫
        SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _))
    (h : ∃ a₀ : M ≅ (homComplex (R := R) A K).homology n,
      ∃ b₀ : N ≅ SheafOfModules.homObj (R := R) (A.homology (-n)) (K.homology 0),
      ∃ g : (homComplex (R := R) A K).homology n ⟶
          SheafOfModules.homObj (R := R) (A.homology (-n)) (K.homology 0),
      ∃ d : (homComplex (R := R) A K).cycles n ⟶
          SheafOfModules.homObj (R := R) (A.cycles (-n)) (K.cycles 0),
        d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
          (homComplex (R := R) A K).iCycles n ≫
            (Classical.choose (homComplex_projections_exists (R := R))) A K n (-n) 0
              (by omega) ≫ SheafOfModules.homObjMap (R := R) (A.iCycles (-n)) (𝟙 _) ∧
        d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
          (homComplex (R := R) A K).homologyπ n ≫ g ≫
            SheafOfModules.homObjMap (R := R) (A.homologyπ (-n)) (𝟙 _) ∧
        e ≫ b₀.hom = a₀.hom ≫ g) :
    ∃ a : M ≅ (homComplex (R := R) E K).homology n,
      ∃ b : N ≅ SheafOfModules.homObj (R := R) (E.homology (-n)) (K.homology 0),
        e ≫ b.hom = a.hom ≫ f := by
  obtain ⟨a₀, b₀, g, d, hd, hd', h₀⟩ := h
  let Qmap : (homComplex (R := R) A K).homology n ⟶
      (homComplex (R := R) L K).homology n :=
    HomologicalComplex.homologyMap (((homComplexFunctor (R := R)).map q.op).app K) n
  let Pmap : (homComplex (R := R) E K).homology n ⟶
      (homComplex (R := R) L K).homology n :=
    HomologicalComplex.homologyMap (((homComplexFunctor (R := R)).map p.op).app K) n
  have : IsIso Qmap := homComplex_precomp_homology_isIso (R := R) (K := K) q n
  have : IsIso Pmap := homComplex_precomp_homology_isIso (R := R) (K := K) p n
  let bq : SheafOfModules.homObj (R := R) (A.homology (-n)) (K.homology 0) ≅
      SheafOfModules.homObj (R := R) (L.homology (-n)) (K.homology 0) :=
    (((SheafOfModules.homFunctor R).mapIso
      (asIso (HomologicalComplex.homologyMap q (-n))).op).app (K.homology 0))
  let bp : SheafOfModules.homObj (R := R) (E.homology (-n)) (K.homology 0) ≅
      SheafOfModules.homObj (R := R) (L.homology (-n)) (K.homology 0) :=
    (((SheafOfModules.homFunctor R).mapIso
      (asIso (HomologicalComplex.homologyMap p (-n))).op).app (K.homology 0))
  have hs : g ≫ bq.hom = Qmap ≫ inv Pmap ≫ f ≫ bp.hom := by
    exact homologyEvaluation_roof_naturality (R := R) A E L K
      (Classical.choose (homComplex_projections_exists (R := R)))
      (Classical.choose_spec (homComplex_projections_exists (R := R))).2.1
      (Classical.choose_spec (homComplex_projections_exists (R := R))).2.2
      n q p g d f c hd hd' hc hc'
  refine ⟨a₀ ≪≫ asIso Qmap ≪≫ (asIso Pmap).symm, b₀ ≪≫ bq ≪≫ bp.symm, ?_⟩
  exact homologyEvaluation_compose_roof_square e
    g f a₀ b₀ (asIso Qmap) (asIso Pmap) bq bp h₀ hs

/-- Restriction and a quasi-isomorphism roof identify cycle evaluations by a
commutative square. No finite-freeness, zero-differential, concentration, or
invertibility hypothesis on the model evaluation is used.

Source: Stacks Project, Tag 0A8X, Hom-complex projections; Tag 0A95,
quasi-isomorphism invariance into K-injectives; Tag 08DL, open restriction.
(blueprint: new-v4-homology-evaluation-roof-comparison).

Proof: Write F for the two restrictions and K = F(J). Exactness of restriction
identifies F(H^n(Hom(T,J))) with H^n(Hom(F(T),K)), and identifies restricted
homology and internal Hom with the corresponding objects on the over site.
Construct the comparison from the fixed projections: overHomObjIso and
internalHom_overEquiv supply natural isomorphisms on each internal-Hom factor.
Restriction preserves these products sectionwise; the open equivalence preserves
all limits. The product universal property gives degreewise isomorphisms with
the specified projection equations. Applying each target projection and the
Hom differential formula proves compatibility with the differentials. The factor
comparisons reindex the same local linear maps, so evaluation on local sections
is preserved. Thus this comparison carries he to evaluation on F(T); a bare
existential isomorphism of Hom complexes alone would not give that compatibility.
Apply Hom(-,K) to q and p. K-injectivity and quasi-isomorphism invariance give
isomorphisms on homology from Hom(F(T),K) and Hom(E,K) to Hom(L,K).
Their composite supplies a, oriented from the restricted source to the model
source. Homology(q) and Homology(p) are isomorphisms; applying the internal-Hom
bifunctor and the restriction comparison supplies b with the same orientation.
The product-projection naturality equation identifies evaluation after
precomposition with q or p on cycle representatives. The first identity for c
identifies the resulting K-cycle, and the second identifies its homology class
with f applied to the Hom class. Thus both routes in the asserted square agree
on Hom-cycles and on source cycles. All homology classes lift locally to cycles,
so separatedness of the target sheaf and of internal Hom gives equality of
morphisms. This proves the square without assuming that f is invertible.
No basis, support bound, concentration hypothesis, or nonzero open is used. -/
theorem homologyEvaluation_roof_comparison (X : Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e) (V : X.Opens) (W : V.toScheme.Opens)
    (hI : CochainComplex.IsKInjective ((moduleOpenOverComplexFunctor X V W).obj J))
    (E L : CochainComplex (SheafOfModules (V.toScheme.ringCatSheaf.over W)) ℤ)
    (q : L ⟶ (moduleOpenOverComplexFunctor X V W).obj T)
    (p : L ⟶ E) (hq : QuasiIso q) (hp : QuasiIso p) :
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    let P := homComplex (R := V.toScheme.sheaf.over W) E K
    let π := (Classical.choose
      (homComplex_projections_exists (R := V.toScheme.sheaf.over W)))
      E K n (-n) 0 (by omega)
    ∀ (f : P.homology n ⟶ SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
        (E.homology (-n)) (K.homology 0))
      (c : P.cycles n ⟶ SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
        (E.cycles (-n)) (K.cycles 0)),
      c ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (𝟙 _) (K.iCycles 0) =
        P.iCycles n ≫ π ≫
          SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (E.iCycles (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (𝟙 _) (K.homologyπ 0) =
        P.homologyπ n ≫ f ≫
          SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (E.homologyπ (-n)) (𝟙 _) →
      ∃ a : ((Scheme.Modules.restrictFunctor V.ι).obj
          ((homComplex (R := X.sheaf) T J).homology n)).over W ≅ P.homology n,
        ∃ b : ((Scheme.Modules.restrictFunctor V.ι).obj
          (SheafOfModules.homObj (R := X.sheaf)
            (T.homology (-n)) (J.homology 0))).over W ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (E.homology (-n)) (K.homology 0),
        (((Scheme.Modules.restrictFunctor V.ι).map e).over W) ≫ b.hom =
          a.hom ≫ f := by
  dsimp only
  intro f c hc hc'
  have := hI
  have := hq
  have := hp
  exact homologyEvaluation_roof_of_cycle_pairings (R := V.toScheme.sheaf.over W)
    _ E L _ n q p _ f c hc hc'
    (homologyEvaluation_restriction_comparison X T J n e he V W)

end CategoryTheory
