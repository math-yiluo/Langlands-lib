/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechPresentation
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonPresentationSheafification
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale

/-! # Finite affine Čech complexes for intrinsic comparison

Source: Stacks Project, Tag 099U, the two finite Čech limit reductions.
-/

@[expose] public section
end
noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace AlgebraicGeometry.ProEtale

section Scalars
variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type w) [CommRing A]

private theorem scalars_equivalence : (coefficientModelFixedScalars J A).IsEquivalence := by
  let α := SheafOfModules.constantCoefficientUnit J A
  let Q := SheafOfModules.forget (SheafOfModules.constantCoefficientRing J A) ⋙
    PresheafOfModules.restrictScalars α
  let lift {M N : SheafOfModules.{w} (SheafOfModules.constantCoefficientRing J A)}
      (f : (coefficientModelFixedScalars J A).obj M ⟶
        (coefficientModelFixedScalars J A).obj N) : Q.obj M ⟶ Q.obj N :=
    { app := f.hom.app
      naturality := fun {_ _} g ↦ by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  let ff : (coefficientModelFixedScalars J A).FullyFaithful :=
    { preimage := fun f ↦ Q.preimage (lift f)
      map_preimage := fun f ↦ by
        ext U x
        exact congrArg (fun k ↦ k.app U x) (Q.map_preimage (lift f))
      preimage_map := fun f ↦ by
        apply Q.map_injective
        exact (Q.map_preimage (lift ((coefficientModelFixedScalars J A).map f))) }
  have := ff.full
  have := ff.faithful
  have : (coefficientModelFixedScalars J A).EssSurj := by
    constructor
    intro F
    let P : PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) :=
      { obj := F.obj.obj
        map := fun f ↦ F.obj.map f
        map_id := fun U ↦ by ext x; exact ConcreteCategory.congr_hom (F.obj.map_id U) x
        map_comp := fun f g ↦ by
          ext x
          exact ConcreteCategory.congr_hom (F.obj.map_comp f g) x }
    let M := PresheafOfModules.sheafify α (M₀ := P)
      (A := (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).obj F) (𝟙 _)
    let t := PresheafOfModules.toSheafify α (M₀ := P)
      (A := (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).obj F) (𝟙 _)
    let e : F ≅ (coefficientModelFixedScalars J A).obj M :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦
        (LinearEquiv.ofBijective (t.app U).hom (Function.bijective_id)).toModuleIso)
        (by intro U V f; ext x; rfl))
    exact ⟨M, ⟨e.symm⟩⟩
  exact {}
end Scalars

private theorem comparison_unit_scalar (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (U : (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ) (a : A) :
    (constructibleComparisonRingMap X A).hom.app U
        ((SheafOfModules.constantCoefficientUnit
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).app U a) =
      (SheafOfModules.constantCoefficientUnit
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).app
          ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U) a := by
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  have h := ((sheafificationAdjunction J CommRingCat.{max v (u + 1)}).homEquiv
    ((Functor.const _).obj (CommRingCat.of A))
    ((F.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj
      (ConstantCompletion.constant K A))).apply_symm_apply
        (Functor.whiskerLeft F.op (toSheafify K
          ((Functor.const _).obj (CommRingCat.of A))))
  exact congrArg (fun k ↦ k.app U a) h

private def comparison_direct_scalars (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    SheafOfModules.pushforward (F := Scheme.smallModelComparisonInclusion.{u, v} X)
        (constructibleComparisonRingMap X A) ⋙
        coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ≅
      coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ⋙
        (Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
          (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun a ↦ by
      ext x
      exact congrArg (fun b ↦
        @SMul.smul _
          (M.val.obj ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U))
          (M.val.obj ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj U)).isModule.toSMul
          b x) (comparison_unit_scalar X A U a).symm))
      (by intro U V f; ext x; rfl))) (by intro M N f; ext U x; rfl)

private def comparison_scalars (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    constructibleComparisonPullback.{u, v} X A ⋙
        coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ≅
      coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ⋙
        Functor.sheafPullbackConstruction.sheafPullback
          (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) := by
  have := scalars_equivalence (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
  have := scalars_equivalence (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  let E := (coefficientModelFixedScalars
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).asEquivalence
  let P := (coefficientModelFixedScalars
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).asEquivalence
  let adjM := SheafOfModules.pullbackPushforwardAdjunction
    (F := Scheme.smallModelComparisonInclusion.{u, v} X) (constructibleComparisonRingMap X A)
  let adjF := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  let adj := E.symm.toAdjunction.comp (adjM.comp P.toAdjunction)
  let eR := Functor.isoWhiskerLeft P.inverse (comparison_direct_scalars X A) ≪≫
    Functor.isoWhiskerRight P.counitIso
      ((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
        (ModuleCat.{max v (u + 1)} A)
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
        (Scheme.coefficientProEtaleModelTopology.{u, v} X))
  let eL := (adj.ofNatIsoRight eR).leftAdjointUniq adjF
  exact Functor.isoWhiskerRight E.unitIso
      (constructibleComparisonPullback X A ⋙ P.functor) ≪≫
    Functor.isoWhiskerLeft E.functor eL

section FiniteColimits
variable {X : Scheme.{u}} {U : Scheme.coefficientProEtaleSiteModel.{u, v} X} {m : ℕ}
  {V : Fin m → Scheme.coefficientProEtaleSiteModel.{u, v} X} {f : ∀ a, V a ⟶ U}
  {S : SiteCechComplex V f} {J : Type (u + 1)} [SmallCategory J]
  (P : CoefficientAffineCechPresentation X S J)
  (G : (Scheme.smallModelComparisonEtaleSite.{u, v} X)ᵒᵖ ⥤
    AddCommGrpCat.{max v (u + 1)})
  (F : (Scheme.coefficientProEtaleSiteModel.{u, v} X)ᵒᵖ ⥤
    AddCommGrpCat.{max v (u + 1)})
  (η : G ⟶ (Scheme.smallModelComparisonInclusion.{u, v} X).op ⋙ F)

private def sections (p : ℕ) (t : Fin (p + 1) → Fin m) :
    Cocone ((CoefficientAffineCechPresentation.nerve (X := X) (S := S) (J := J) P p t).op ⋙ G) where
  pt := F.obj (op (S.W p t))
  ι.app i := η.app _ ≫ F.map (P.projection p t i.unop).op
  ι.naturality i j a := by
    change G.map _ ≫ η.app _ ≫ F.map _ = (η.app _ ≫ F.map _) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, η.naturality]
    change η.app _ ≫ F.map
      ((Scheme.smallModelComparisonInclusion.{u, v} X).map (P.trans a.unop p t)).op ≫
        F.map (P.projection p t j.unop).op = _
    rw [← F.map_comp, ← op_comp, P.projection_trans]
    rfl

private def restrictCochain {i j : J} (a : i ⟶ j) (p : ℕ) :
    (P.stage j).cochains G p →+ (P.stage i).cochains G p :=
  AddMonoidHom.pi fun t ↦
    (G.map (P.trans a p t).op).hom.comp (Pi.evalAddMonoidHom _ t)

private def compareCochain (i : J) (p : ℕ) :
    (P.stage i).cochains G p →+ S.cochains F p :=
  AddMonoidHom.pi fun t ↦
    ((F.map (P.projection p t i).op).hom.comp (η.app _).hom).comp
      (Pi.evalAddMonoidHom _ t)

private theorem restrict_d {i j : J} (a : i ⟶ j) (p : ℕ)
    (c : (P.stage j).cochains G p) :
    (P.stage i).differentialValue G p (restrictCochain P G a p c) =
      restrictCochain P G a (p + 1) ((P.stage j).differentialValue G p c) := by
  funext t
  change (∑ k : Fin (p + 2), (-1 : ℤ) ^ k.val •
      G.map ((P.stage i).indexMap t k.succAbove).op
        (G.map (P.trans a p (t ∘ k.succAbove)).op (c (t ∘ k.succAbove)))) =
    G.map (P.trans a (p + 1) t).op
      (∑ k : Fin (p + 2), (-1 : ℤ) ^ k.val •
        G.map ((P.stage j).indexMap t k.succAbove).op (c (t ∘ k.succAbove)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← G.map_comp, ← op_comp,
    ← ConcreteCategory.comp_apply, ← G.map_comp, ← op_comp, P.trans_index]

private theorem compare_d (i : J) (p : ℕ) (c : (P.stage i).cochains G p) :
    S.differentialValue F p (compareCochain P G F η i p c) =
      compareCochain P G F η i (p + 1) ((P.stage i).differentialValue G p c) := by
  funext t
  change (∑ k : Fin (p + 2), (-1 : ℤ) ^ k.val •
      F.map (S.indexMap t k.succAbove).op
        (F.map (P.projection p (t ∘ k.succAbove) i).op
          (η.app _ (c (t ∘ k.succAbove))))) =
    F.map (P.projection (p + 1) t i).op
      (η.app _ (∑ k : Fin (p + 2), (-1 : ℤ) ^ k.val •
        G.map ((P.stage i).indexMap t k.succAbove).op (c (t ∘ k.succAbove))))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul, map_zsmul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, P.projection_index,
    op_comp, F.map_comp]
  exact congrArg (fun z ↦ F.map (P.projection (p + 1) t i).op z)
    (ConcreteCategory.congr_hom
      (η.naturality ((P.stage i).indexMap t k.succAbove).op).symm
      (c (t ∘ k.succAbove)))

private theorem compare_restrict {i j : J} (a : i ⟶ j) (p : ℕ)
    (c : (P.stage j).cochains G p) :
    compareCochain P G F η i p (restrictCochain P G a p c) =
      compareCochain P G F η j p c := by
  funext t
  have hn := ConcreteCategory.congr_hom (η.naturality (P.trans a p t).op) (c t)
  change F.map (P.projection p t i).op (η.app _ (G.map (P.trans a p t).op (c t))) = _
  change η.app _ (G.map (P.trans a p t).op (c t)) =
    F.map ((Scheme.smallModelComparisonInclusion.{u, v} X).map (P.trans a p t)).op
      (η.app _ (c t)) at hn
  rw [hn, ← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, P.projection_trans]
  rfl

private theorem finiteLimitExact [IsCofiltered J]
    (hcol : ∀ p t, IsColimit (sections P G F η p t))
    (q : ℕ)
    (hstage : ∀ i (c : (P.stage i).cochains G (q + 1)),
      (P.stage i).differentialValue G (q + 1) c = 0 →
        ∃ b : (P.stage i).cochains G q, (P.stage i).differentialValue G q b = c) :
    (S.complex F).ExactAt (q + 1) := by
  classical
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget AddCommGrpCat.{max v (u + 1)}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max v (u + 1), max v (u + 1),
      u + 1, u + 1} _
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro c hc
  change (S.complex F).d (q + 1) ((q + 1) + 1) c = 0 at hc
  simp only [SiteCechComplex.complex, CochainComplex.of_d] at hc
  change S.differentialValue F (q + 1) c = 0 at hc
  have hrep (t : Fin (q + 2) → Fin m) :=
    Concrete.isColimit_exists_rep _ (hcol (q + 1) t) (c t)
  choose i x hx using hrep
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let a (t : Fin (q + 2) → Fin m) : i t ⟶ j := (hj (by simp)).some
  let z : (P.stage j.unop).cochains G (q + 1) :=
    fun t ↦ G.map (P.trans (a t).unop (q + 1) t).op (x t)
  have hz : compareCochain P G F η j.unop (q + 1) z = c := by
    funext t
    exact (ConcreteCategory.congr_hom ((sections P G F η (q + 1) t).w (a t))
      (x t)).trans (hx t)
  let dz := (P.stage j.unop).differentialValue G (q + 1) z
  have hdz : compareCochain P G F η j.unop (q + 2) dz = 0 := by
    rw [← compare_d, hz, hc]
  have heq (t : Fin (q + 3) → Fin m) :=
    Concrete.isColimit_exists_of_rep_eq _ (hcol (q + 2) t)
      (dz t) (0 : G.obj (op ((P.stage j.unop).W (q + 2) t)))
      (by
        have ht := congrFun hdz t
        change F.map (P.projection (q + 2) t j.unop).op (η.app _ (dz t)) = 0 at ht
        change F.map (P.projection (q + 2) t j.unop).op (η.app _ (dz t)) = _
        simpa only [map_zero] using ht)
  choose k a b hab using heq
  obtain ⟨l, g, h, hh⟩ := IsFiltered.wideSpan a
  let z' := restrictCochain P G g.unop (q + 1) z
  have hz' : (P.stage l.unop).differentialValue G (q + 1) z' = 0 := by
    rw [restrict_d]
    funext t
    change G.map (P.trans g.unop (q + 2) t).op (dz t) = 0
    rw [← hh t, unop_comp, P.trans_comp, op_comp, G.map_comp]
    have ht := congrArg (fun y ↦ G.map (P.trans (h t).unop (q + 2) t).op y) (hab t)
    change G.map (P.trans (h t).unop (q + 2) t).op
      (G.map (P.trans (a t).unop (q + 2) t).op (dz t)) = _ at ht
    simpa only [map_zero, ConcreteCategory.comp_apply] using ht
  obtain ⟨b, hb⟩ := hstage l.unop z' hz'
  refine ⟨compareCochain P G F η l.unop q b, ?_⟩
  change (S.complex F).d q (q + 1) _ = c
  simp only [SiteCechComplex.complex, CochainComplex.of_d]
  change S.differentialValue F q _ = c
  rw [compare_d, hb, compare_restrict, hz]
end FiniteColimits

private def fixedComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :=
  Functor.sheafPullbackConstruction.sheafPullback
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

private def fixedUnit (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (G : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) :
    G.obj ⟶ (Scheme.smallModelComparisonInclusion.{u, v} X).op ⋙
      ((fixedComparison X A).obj G).obj :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)).unit.app G).hom

private def nervePresentation {X : Scheme.{u}}
    {U : Scheme.coefficientProEtaleSiteModel.{u, v} X} {m : ℕ}
    {V : Fin m → Scheme.coefficientProEtaleSiteModel.{u, v} X} {f : ∀ a, V a ⟶ U}
    {S : SiteCechComplex V f} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (P : CoefficientAffineCechPresentation X S J)
    (hl : ∀ p t, Nonempty (IsLimit
      (((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt) ⋙
        Scheme.ProEt.forget X).mapCone (P.cone p t))))
    (p : ℕ) (t : Fin (p + 1) → Fin m) : AffinePresentation X J where
  diagram := (P.nerve p t ⋙ Scheme.smallModelComparisonInclusion.{u, v} X) ⋙ AsSmall.down
  affine j := P.affine_stage j p t
  etale j := inferInstanceAs (Etale (AsSmall.down.obj ((P.stage j).W p t)).hom)
  cone := AsSmall.down.mapCone (P.cone p t)
  affineVertex := P.affine_vertex p t
  isLimit := (hl p t).some

private def nerveSectionsColimit (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (G : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    {U : Scheme.coefficientProEtaleSiteModel.{u, v} X} {m : ℕ}
    {V : Fin m → Scheme.coefficientProEtaleSiteModel.{u, v} X} {f : ∀ a, V a ⟶ U}
    {S : SiteCechComplex V f} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (P : CoefficientAffineCechPresentation X S J)
    (hl : ∀ p t, Nonempty (IsLimit
      (((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt) ⋙
        Scheme.ProEt.forget X).mapCone (P.cone p t))))
    (p : ℕ) (t : Fin (p + 1) → Fin m) :
    IsColimit (sections P (G.obj ⋙ forget₂ (ModuleCat A) AddCommGrpCat)
      (((fixedComparison X A).obj G).obj ⋙ forget₂ (ModuleCat A) AddCommGrpCat)
      (Functor.whiskerRight (fixedUnit X A G) (forget₂ (ModuleCat A) AddCommGrpCat))
      p t) := by
  let B := Scheme.smallModelComparisonInclusion.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let M := ModuleCat.{max v (u + 1)} A
  let F := ((fixedComparison X A).obj G).obj
  let Q := nervePresentation P hl p t
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤
      X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤
      Scheme.coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).symm.isEquivalence_inverse
  have : B.op.Full := inferInstance
  have : B.op.Faithful := inferInstance
  have hunit (j : J) : IsIso ((fixedUnit X A G).app (op ((P.stage j).W p t))) := by
    have hu : fixedUnit X A G = B.op.lanUnit.app G.obj ≫
        Functor.whiskerLeft B.op (toSheafify K (B.op.lan.obj G.obj)) := by
      change (sheafToPresheaf _ M).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B M _ K).unit.app G) = _
      rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
        Adjunction.map_restrictFullyFaithful_unit_app]
      rfl
    have hη := (coefficientComparison_presentation_toSheafify_isIso X A G Q).2 j
    have : IsIso ((toSheafify K (B.op.lan.obj G.obj)).app
        (B.op.obj (op ((P.stage j).W p t)))) := hη
    have : B.op.HasPointwiseLeftKanExtension G.obj := inferInstance
    have : IsIso ((B.op.lanUnit.app G.obj).app (op ((P.stage j).W p t))) :=
      inferInstance
    rw [hu, NatTrans.comp_app]
    change IsIso ((B.op.lanUnit.app G.obj).app (op ((P.stage j).W p t)) ≫
      (toSheafify K (B.op.lan.obj G.obj)).app (B.op.obj (op ((P.stage j).W p t))))
    infer_instance
  let e : (P.nerve p t).op ⋙ G.obj ≅ (P.nerve p t ⋙ B).op ⋙ F :=
    NatIso.ofComponents (fun j ↦ asIso ((fixedUnit X A G).app
      (op ((P.stage j.unop).W p t))))
      (fun a ↦ (fixedUnit X A G).naturality (P.trans a.unop p t).op)
  have hF : IsColimit (F.mapCocone (P.cone p t).op) :=
    (coefficientFixedComparison_isColimit X A G Q).some
  have hG := (IsColimit.precomposeHomEquiv e (F.mapCocone (P.cone p t).op)).symm hF
  exact isColimitOfPreserves (forget₂ M AddCommGrpCat.{max v (u + 1)}) hG

private def reindexCech {C : Type w} [SmallCategory C] {T : Type*} {U : C}
    {V : T → C} {f : ∀ a, V a ⟶ U} (S : SiteCechComplex V f)
    {T' : Type*} (a : T' → T) : SiteCechComplex (V ∘ a) (fun t ↦ f (a t)) where
  W p t := S.W p (a ∘ t)
  pr p t k := S.pr p (a ∘ t) k
  comm p t k := S.comm p (a ∘ t) k
  universal p t Z b hb := S.universal p (a ∘ t) Z b hb
  W_zero t := S.W_zero (a ∘ t)
  pr_zero t := S.pr_zero (a ∘ t)
  indexMap t α := S.indexMap (a ∘ t) α
  indexMap_pr t α k := S.indexMap_pr (a ∘ t) α k

private theorem stagePrimitive {C : Type w} [SmallCategory C]
    {K : GrothendieckTopology C} (R : Sheaf K RingCat.{w})
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (I : SheafOfModules.{w} R) [Injective I]
    {m : ℕ} {U : C} {V : Fin m → C} {f : ∀ a, V a ⟶ U}
    (S : SiteCechComplex V f) (q : ℕ)
    (c : S.cochains I.val.presheaf (q + 1))
    (hc : S.differentialValue I.val.presheaf (q + 1) c = 0) :
    ∃ b : S.cochains I.val.presheaf q, S.differentialValue I.val.presheaf q b = c := by
  have : Injective I.val := injective_module_sheaf_injective_presheaf R I
  let S' := reindexCech S (ULift.down : ULift.{w} (Fin m) → Fin m)
  let c' : S'.cochains I.val.presheaf (q + 1) := fun t ↦ c (ULift.down ∘ t)
  have hc' : S'.differentialValue I.val.presheaf (q + 1) c' = 0 := by
    funext t
    exact congrFun hc (ULift.down ∘ t)
  obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift
    R.obj I.val _ _ S' q c' hc'
  refine ⟨fun t ↦ b (ULift.up ∘ t), ?_⟩
  funext t
  exact congrFun hb (ULift.up ∘ t)

end AlgebraicGeometry.ProEtale
end

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Finite coverings in the affine ind-etale basis have zero positive Čech cohomology
with coefficients in the intrinsic comparison pullback of an injective etale module.
Source: Stacks Project, Tag 099U, paragraphs beginning "To check condition (3)" and
"Let U be an etale covering"; module coefficients use the augmented free-module
Čech resolution (Cohomology on Sites, Tag 03FC).
(auxiliary; not a blueprint node).

Proof: transport the cover through AsSmall.down, retaining its covering sieve. Present its
affine ind-etale objects by small cofiltered diagrams of affine etale X-schemes. First
approximate the finitely many covering arrows by etale arrows over the covered object. Their
finite disjoint union is surjective at each approximating stage. Next approximate the covered
object by affine etale X-schemes. Finite presentation descends the finitely many covering
objects and arrows to a common stage. Form their iterated intersections there and use base
change to recover the original intersections; no infinite diagram is descended. Joint
surjectivity holds on a cofinal tail. Thus each stage is an etale covering of an etale object of
X. The augmented free-module Čech complex is exact. Applying Hom into the injective module I
makes its positive cohomology zero. Constant-scalar restriction retains the abelian sheaf. The
canonical constant-section ring map identifies intrinsic comparison pullback under scalar
restriction with the fixed-scalar comparison pullback. The affine comparison-section formula
expresses each nerve term as the filtered colimit of its etale stage sections. For each omitted-
factor projection d, naturality says that the stage restriction followed by the continuity map
equals the continuity map followed by restriction along the limit projection. Taking their
signed sums identifies the Čech differentials. Repeated indices use the diagonal cofinal
subsystem of their finitely many stage indices. Finite products commute with these exact
filtered colimits of modules, so the alternating Čech complex has zero positive cohomology. The
projection-characterized isomorphism between any two choices of iterated fibre products
transfers this conclusion to the specified S. Transport back through AsSmall.up changes no
section. The empty covering has zero terms in every positive degree, and the zero ring gives
only zero modules; both cases are included. No derived evaluation or acyclicity criterion is
used in this step. -/
theorem coefficientComparison_affineCech_vanishing (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    [HasSheafify (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)}]
    [HasSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)}]
    (I : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)) [Injective I]
    (U : Scheme.coefficientProEtaleSiteModel.{u, v} X)
    (m : ℕ) (V : Fin m → Scheme.coefficientProEtaleSiteModel.{u, v} X)
    (f : ∀ a, V a ⟶ U)
    (hU : proAffineEtale (AsSmall.down.obj U).hom)
    (hV : ∀ a, proAffineEtale (AsSmall.down.obj (V a)).hom)
    (hc : Presieve.ofArrows V f ∈
      (Scheme.coefficientProEtaleModelTopology.{u, v} X).toPrecoverage U)
    (S : SiteCechComplex V f) (q : ℕ) :
    IsZero ((S.cohomologyFunctor (q + 1)).obj
      ((constructibleComparisonPullback.{u, v} X A).obj I).val.presheaf)  := by
  classical
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let M := ModuleCat.{max v (u + 1)} A
  let G := (coefficientModelFixedScalars J A).obj I
  let F := ((fixedComparison X A).obj G).obj ⋙ forget₂ M AddCommGrpCat
  let η := Functor.whiskerRight (fixedUnit X A G) (forget₂ M AddCommGrpCat)
  obtain ⟨D, _, _, P, hl⟩ :=
    exists_coefficient_affine_cech_presentation X U m V f hU hV hc S
  have hF : (S.complex F).ExactAt (q + 1) :=
    finiteLimitExact P I.val.presheaf F η (nerveSectionsColimit X A G P hl) q
      (fun i c hc ↦ stagePrimitive _ I (P.stage i) q c hc)
  let e : ((constructibleComparisonPullback X A).obj I).val.presheaf ≅ F :=
    ((Functor.whiskeringRight _ _ _).obj (forget₂ M AddCommGrpCat)).mapIso
      ((sheafToPresheaf K M).mapIso ((comparison_scalars X A).app I))
  exact hF.isZero_homology.of_iso ((S.cohomologyFunctor (q + 1)).mapIso e)

end AlgebraicGeometry.ProEtale
